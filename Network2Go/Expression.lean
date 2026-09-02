module

public import Network2Go.Ord
public import Core.ComputablePlusCal.Syntax
public import Core.ComputableTLAPlus.Subst
public import Core.Go.Syntax
public import Common.Fresh

public section

/-!
  Compiling TLA⁺ expressions into Go expressions.

  The output is a single `Go.Expression`, never a statement prelude: everything that needs
  statements to express — the quantifiers' search loops, `IF`/`CASE`'s laziness, `EXCEPT`'s record
  update — is wrapped in an immediately-applied `Go.Expression.funcLit`. That keeps this function
  callable from any expression position (a branch's guard, an argument, another expression's
  sub-term) without every caller having to thread a list of statements to emit first. `funcLit`
  exists in `Core.Go.Syntax` precisely because these forms cannot be compiled without it.

  Recurring conventions, all forced by the runtime library's own types:

  - **Everything of TLA⁺ type `Bool` is `tlaplus.Bool`, not Go's `bool`.** `Bool` is a defined type
    over `bool`, so Go's own `&&`/`||`/`!` still apply to it directly and their results stay
    `tlaplus.Bool`; what does *not* apply is using one as an `if` condition or handing one to a
    runtime predicate, both of which want a real `bool`. Those sites convert with `bool(e)`, and
    anything producing a Go `bool` (`SetIn`, `Eq`, `SetEq`) converts back with `tlaplus.Bool(e)`.
  - **Literals go through the constructors, never composite literals.** `tlaplus.MkInt(1)` rather
    than `Int(1)` (the arbitrary-precision representation is a struct), `MkSet`/`MkSeq` rather than
    `Set[τ]{…}`/`Seq[τ]{…}` (a set literal may be unsorted or repeat an element; a sequence is
    1-indexed with slot 0 unused). The one exception is the *empty* literal, which has nothing to
    infer a type parameter from and so is written `tlaplus.Set[τ]{}` — trivially sorted,
    duplicate-free, and for `Seq` the nil slice is already the valid empty sequence.
  - **Types are read off the AST, never re-derived.** Go's `func` literals have mandatory
    signatures, so `{e : x ∈ S}`, `[x ∈ S ↦ e]`, `IF`/`CASE` and a record `EXCEPT` all have to write
    out a type TLA⁺ never spells. The checker records each of them
    (`Elaborator/Expressions.lean`); this pass only reads them off the node it is compiling.
    `f[e]`'s head type is recorded for a different reason — it is a three-way dispatch, between a
    function application, a sequence index and a tuple projection, not a type to emit.
  - **Operator applications dispatch on the head's `Origin`.** `\in`, `=` and friends are not Go
    functions with those names — `x \in S` reverses its arguments into `SetIn(o, S, x)` and `=`
    picks between the element dictionary's `Eq`, `SetEq` and `SeqEq` by operand type — so a builtin
    head is matched at the application site rather than compiled to a name and applied. A *bare*
    builtin reference (one passed around rather than applied) has no Go counterpart at all and is
    rejected.
  - **Every comparison is a dictionary call, and the dictionary comes from the type.** `Ord[T]` is
    a struct of two functions, not an interface, so nothing is a method on the value being
    compared: `x = y` at type `τ` is `⟦τ⟧ᴼʳᵈ.Eq(x, y)`, and every runtime operation that compares
    (`MkSet`, `SetIn`, `SetUnion`, `FnApply`, …) takes the dictionary as its first argument. Which
    dictionary a `Set` was built with is not recorded in the set, so every operation on it must be
    handed the same one — guaranteed here by deriving both from the same `Typ`, via `ordDict`. The
    operations that never compare (`SetFilter`, `Choose`, `Cardinality`, and all of `Sequences`
    except equality) take none.

  Deliberately not handled here, since they are not expression forms: operator and function
  *definitions* (including `MkRecFn` for recursive ones), which live in `Network2Go.Definition`,
  and the renaming of user-chosen names that collide after
  capitalization.
-/

namespace Network2Go

open ComputableTLAPlus (Typ)

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty N2GError m] [MonadFresh m]

/-- The standard modules `Driver/Builtins.lean` supplies. A `.var`'s `Origin` records the module it
resolved in, and every one of these is compiled to a runtime call rather than to a reference to a
generated definition. Matching on the module *name* is sound because `Driver/Modules.lean` refuses
to silently shadow a builtin with a user module of the same name (it reports the ambiguity), so a
name in this set never denotes user code. -/
private def builtinModuleNames : Std.HashSet String :=
  { "Naturals", "Integers", "Sequences", "FiniteSets", "Bags", "TLC", "Fugue" }

/-- `bool(e)` — Go's conversion out of the runtime's `Bool`, needed wherever a real `bool` is
required: an `if` condition, and every predicate the runtime library takes.

Cancels against `tlaBool` rather than nesting inside it. The two meet constantly — every runtime
predicate answers in Go's `bool`, gets wrapped so that the TLA⁺ expression has a TLA⁺ type, and is
then unwrapped again by whatever consumes it as a condition — and `bool(tlaplus.Bool(e))` is
merely `e`, so a compiled guard reads as one comparison instead of three nested calls. -/
def goBool : ComputableGo.Expression → ComputableGo.Expression
  | .call (.var f) [e] => if f == qualified tlaplusPkg "Bool" then e else .call (.var "bool") [.call (.var f) [e]]
  | e => .call (.var "bool") [e]

/-- `tlaplus.Bool(e)` — the conversion back, wrapping anything that produced a Go `bool`. -/
private def tlaBool (e : ComputableGo.Expression) : ComputableGo.Expression :=
  tlaplusCall "Bool" [e]

/-- An operator applied to the wrong number of arguments — impossible past type checking, which
checks every application's arity. -/
private def wrongArity (pos : SourceSpan) (name : String) (n : Nat) : m ComputableGo.Expression :=
  throw (.internalInvariantViolated pos
    s!"'{name}' applied to {n} arguments, which type checking should already have rejected")

/-- TLA⁺ `=` and `#`, dispatched on the operand type. Most types compare through their dictionary's
`Eq`, but `Set` and `Seq` are slice types: their equality needs the *element* dictionary and walks
the two slices, so the runtime gives it as a free function taking that dictionary.

Functions have no equality at all: comparing two lazy maps means comparing them on every point of
their domain, which the representation deliberately does not do. -/
private def compileEq (pos : SourceSpan) (τ : Typ) (x y : ComputableGo.Expression) :
    m ComputableGo.Expression :=
  match τ with
  | .set ρ => return tlaplusCall "SetEq" [← ordDict ρ, x, y]
  | .seq ρ => return tlaplusCall "SeqEq" [← ordDict ρ, x, y]
  | .function _ _ =>
    throw (.unsupported pos "="
      "two functions can only be compared by comparing them at every point of their domain, which \
       the lazy-map representation does not do")
  | .operator _ _ =>
    throw (.internalInvariantViolated pos
      "an operator reached '=', but operators are not values in TLA⁺")
  | _ => return .call (.field (← ordDict τ) "Eq") [x, y]

/-- The element dictionary of a set-typed operand — what every set-to-set runtime operation takes
as its first argument. `name` is the operator asking, for the diagnostic. -/
private def setElemDict (pos : SourceSpan) (name : String) : Typ → m ComputableGo.Expression
  | .set ρ => ordDict ρ
  | τ =>
    throw (.internalInvariantViolated pos
      s!"'{name}' was applied to {repr τ}, which type checking should already have rejected")

mutual

/--
  Compiles a checked TLA⁺ expression into the Go expression that computes it.
-/
partial def compileExpr (e : ComputablePlusCal.Expression) : m ComputableGo.Expression :=
  match_source e with
  | .nat n, _ =>
    -- Never `Int(n)`: under the default arbitrary-precision representation `Int` is a struct, and
    -- `MkInt` is what both representations agree on.
    return tlaplusCall "MkInt" [.nat n]
  | .str s, _ => return tlaplusCall "Str" [.str s]
  | .true, _ => return tlaBool .true
  | .false, _ => return tlaBool .false
  -- A memory-keyed name — a quantifier's, resolved to its hint by `openHints`; a process's; a
  -- branch's — keeps the name it had: capitalization applies to *definitions*, not variables.
  | .var _ (.free name), _ => return .var (binderName name)
  | .var τ (.module mod name), pos =>
    if builtinModuleNames.contains mod then compileBuiltinVar pos mod name τ
    -- A user definition. `LOCAL` ones keep their case, which this reference cannot see; the
    -- definition-compilation step owns that flag and has to agree with what is emitted here.
    else return .var (definitionName (isLocal := false) name)
  | .var _ (.intrinsic name), pos =>
    throw (.unsupported pos name
      "a builtin operator can only be applied, not passed around as a value — Go has no \
       counterpart to refer to")
  | .var _ (.bound _), pos =>
    throw (.internalInvariantViolated pos
      "a de Bruijn index reached code generation — every binder body is opened with its hint first")
  | .opCall f args, pos => do
    let args' ← args.mapM compileExpr
    match f with
    | .var τ (.intrinsic name) => compileIntrinsic pos name τ args'
    | .var τ (.module mod name) =>
      if builtinModuleNames.contains mod then compileBuiltinCall pos mod name τ args'
      else return .call (← compileExpr f) args'
    | _ => return .call (← compileExpr f) args'
  | .forall x τ dom body, _ => compileQuantifier (isForall := true) x τ dom body
  | .exists x τ dom body, _ => compileQuantifier (isForall := false) x τ dom body
  -- `CHOOSE` must be deterministic, which the runtime achieves by taking the smallest satisfying
  -- element of the sorted representation rather than picking at random.
  | .choose x τ dom body, _ =>
    return tlaplusCall "Choose" [← compileExpr dom, ← compilePredicate x τ body]
  | .set es τ, _ => do
    if es.isEmpty then return .sliceLit (tlaplusTyp "Set" [← compileTyp τ]) []
    else return tlaplusCall "MkSet" ((← ordDict τ) :: (← es.mapM compileExpr))
  | .seq es τ, _ => do
    if es.isEmpty then return .sliceLit (tlaplusTyp "Seq" [← compileTyp τ]) []
    else return tlaplusCall "MkSeq" (← es.mapM compileExpr)
  | .collect x τ dom body, _ =>
    return tlaplusCall "SetFilter" [← compileExpr dom, ← compilePredicate x τ body]
  | .map' body x τ cod dom, _ => do
    -- `SetMap` renormalizes its result: the mapping function is neither monotone nor injective in
    -- general, so neither the sortedness nor the duplicate-freedom invariant survives it. It is
    -- therefore the *result* dictionary it needs — nothing here compares an element of the source.
    return tlaplusCall "SetMap"
      [← ordDict cod, ← compileExpr dom,
        .funcLit [(binderName x, ← compileTyp τ)] [← compileTyp cod] [.return [← compileExpr body]]]
  | .fn x τ cod dom body, _ =>
    return tlaplusCall "FnConstructor"
      [← ordDict τ, ← compileExpr dom,
        .funcLit [(binderName x, ← compileTyp τ)] [← compileTyp cod] [.return [← compileExpr body]]]
  | .fnCall f fnTyp i, pos => do
    let f' ← compileExpr f
    match fnTyp with
    -- `FnApply` needs a dictionary despite the lazy map already holding a comparator: the domain
    -- check goes through `SetIn`, which needs one of its own.
    | .function dom _ => return tlaplusCall "FnApply" [← ordDict dom, f', ← compileExpr i]
    | .seq _ => return tlaplusCall "SeqIndex" [f', ← compileExpr i]
    -- A tuple is a struct, so its components are reachable only by name, and the name is fixed by
    -- the index — which therefore has to be a literal.
    | .tuple _ =>
      match i with
      | .nat n =>
        match n.toNat? with
        | some k => return .field f' (projName k)
        | none =>
          throw (.internalInvariantViolated pos s!"tuple index '{n}' is not a natural number")
      | _ =>
        throw (.unsupported pos "t[e]"
          "a tuple's components can have different types, so it compiles to a struct and can only \
           be indexed by a literal")
    | _ =>
      throw (.internalInvariantViolated pos
        "the head of a function application is neither a function, a sequence nor a tuple")
  | .recordAccess r x, _ => return .field (← compileExpr r) (fieldName x)
  -- Both literals build their own Go type from the annotations they already carry: a record node
  -- records a type per field, a tuple node one per component.
  | .record fs, _ => do
    let τ ← compileTyp (.record (fs.map λ (τᵢ, x, _) ↦ (x, τᵢ)))
    -- Field order in a keyed composite literal is free, but the fields are sorted anyway so that
    -- the same record written two ways compiles to identical output, as its *type* already does.
    let fields ← fs.mapM λ (_, x, e') ↦ return (fieldName x, ← compileExpr e')
    return .structLit τ (fields.mergeSort λ (x, _) (y, _) ↦ x ≤ y)
  | .tuple es, _ => do
    let τ ← compileTyp (.tuple (es.map Prod.fst))
    let fields ← es.zipIdx.mapM λ ((_, e'), i) ↦ return (projName (i + 1), ← compileExpr e')
    return .structLit τ fields
  | .except f τ upds, pos => do
    -- Each override applies to the result of the previous one, so `[f EXCEPT ![1] = a, ![2] = b]`
    -- is one function with both points changed rather than two independent overrides of `f`.
    upds.foldlM (init := ← compileExpr f) λ acc (path, rhs) ↦ compileExcept pos τ acc path rhs
  | .if c t f τ, _ => do
    let τ ← compileTyp τ
    -- An immediately-applied literal, not a helper taking both arms: Go evaluates arguments
    -- eagerly, and `IF x # 0 THEN 1 \div x ELSE 0` must not evaluate the arm it did not select.
    return .call (.funcLit [] [τ]
      [.if (goBool (← compileExpr c)) [.return [← compileExpr t]] [],
        .return [← compileExpr f]]) []
  | .case arms other τ, _ => do
    let τ ← compileTyp τ
    let guards ← arms.mapM λ (p, body) ↦
      return Go.Statement.if (goBool (← compileExpr p)) [.return [← compileExpr body]] []
    -- Without an `OTHER` arm a `CASE` matching nothing is undefined in TLA⁺, so the generated
    -- function panics. `panic` also terminates the block, which is what lets Go accept it as the
    -- final statement of a function that must return a value.
    let fallthrough ← match other with
      | some body => pure <| Go.Statement.return [← compileExpr body]
      | none => pure <| Go.Statement.panic (.str "CASE with no matching arm")
    return .call (.funcLit [] [τ] (guards ++ [fallthrough])) []

/-- `func(x τ) bool { return bool(P) }` — the callback shape every runtime set operation takes.
`SetFilter`/`Choose` are declared over a Go `bool` predicate rather than a `tlaplus.Bool` one, so
the body converts. -/
partial def compilePredicate (x : String) (τ : Typ) (body : ComputablePlusCal.Expression) :
    m ComputableGo.Expression :=
  return .funcLit [(binderName x, ← compileTyp τ)] [.bool] [.return [goBool (← compileExpr body)]]

/--
  `\A x \in S : P` and `\E x \in S : P`: a search of `S` for the first counterexample/witness, the
  two being De Morgan duals of one another.

  Written as a loop inside an immediately-applied literal rather than as
  `Cardinality(SetFilter(S, ¬P)) = 0`, because the filter would evaluate `P` at every element even
  after the answer is settled — visible whenever `P` is undefined somewhere in `S`. `S` becomes the
  literal's parameter so that it is evaluated exactly once.
-/
partial def compileQuantifier (isForall : Bool) (x : String) (τ : Typ)
    (dom body : ComputablePlusCal.Expression) : m ComputableGo.Expression := do
  let elemτ ← compileTyp τ
  let x := binderName x
  let s := goIdent (← freshName "set")
  let i := goIdent (← freshName "i")
  let body' ← compileExpr body
  -- `\A` stops at the first element failing `P`, `\E` at the first satisfying it; each then
  -- returns the opposite of whatever it would have returned had the loop run out.
  let stop := if isForall then Go.Expression.unary .not body' else body'
  let early := tlaBool (if isForall then .false else .true)
  let final := tlaBool (if isForall then .true else .false)
  return .call (.funcLit [(s, tlaplusTyp "Set" [elemτ])] [tlaplusTyp "Bool"]
    [ .var i .int,
      .for (.binary .lt (.var i) (.builtin .len [.var s]))
        [ .var x elemτ,
          .assign [.var x] [.index (.var s) (.var i)],
          .if (goBool stop) [.return [early]] [],
          .assign [.var i] [.binary .add (.var i) (.nat "1")] ],
      .return [final] ]) [← compileExpr dom]

/--
  One `![e] = v` / `!.x = v` override of an `EXCEPT`, following the path down and rebuilding on the
  way back up. `τ` is the type of what `base` computes.

  A function override is `FnOverload`, which keeps the fresh map header `Insert` returns so that the
  override stays scoped to the overloaded copy. Records and tuples have no such helper — Go has no
  functional update for a struct — so they go through a literal taking the struct *by value*: the
  parameter is already a copy, so assigning into it cannot reach the original.
-/
partial def compileExcept (pos : SourceSpan) (τ : Typ) (base : ComputableGo.Expression)
    (path : List (String ⊕ ComputablePlusCal.Expression)) (rhs : ComputablePlusCal.Expression) :
    m ComputableGo.Expression := do
  match path with
  | [] => compileExpr rhs
  | .inr i :: rest => do
    let i' ← compileExpr i
    match τ with
    | .function δ ρ => do
      let dict ← ordDict δ
      return tlaplusCall "FnOverload"
        [dict, base, i', ← compileExcept pos ρ (tlaplusCall "FnApply" [dict, base, i']) rest rhs]
    | .seq ρ =>
      return tlaplusCall "SeqUpdate"
        [base, i', ← compileExcept pos ρ (tlaplusCall "SeqIndex" [base, i']) rest rhs]
    | .tuple τs =>
      match i with
      | .nat n =>
        match n.toNat? with
        | some k =>
          match τs[k - 1]? with
          | some ρ => compileStructUpdate pos τ (projName k) ρ base rest rhs
          | none =>
            throw (.internalInvariantViolated pos
              s!"EXCEPT indexes a tuple at component {k}, which it does not have")
        | none =>
          throw (.internalInvariantViolated pos s!"tuple index '{n}' is not a natural number")
      | _ =>
        throw (.unsupported pos "EXCEPT"
          "a tuple compiles to a struct, so an EXCEPT on one can only be indexed by a literal")
    | _ =>
      throw (.internalInvariantViolated pos
        "EXCEPT indexes something that is neither a function, a sequence nor a tuple")
  | .inl x :: rest =>
    match τ with
    | .record fs =>
      match fs.lookup x with
      | some ρ => compileStructUpdate pos τ (fieldName x) ρ base rest rhs
      | none =>
        throw (.internalInvariantViolated pos s!"EXCEPT overrides field '{x}', which does not exist")
    | _ =>
      throw (.internalInvariantViolated pos "EXCEPT selects a field of something that is not a record")

/-- `func(r T) T { r.X = …; return r }(base)` — the struct update shared by record and tuple
overrides. Taking `r` by value is the whole trick: Go copies a struct argument, so the assignment
cannot be seen by whoever still holds `base`. -/
partial def compileStructUpdate (pos : SourceSpan) (τ : Typ) (field : String) (fieldτ : Typ)
    (base : ComputableGo.Expression) (rest : List (String ⊕ ComputablePlusCal.Expression))
    (rhs : ComputablePlusCal.Expression) : m ComputableGo.Expression := do
  let goτ ← compileTyp τ
  let r := goIdent (← freshName "rec")
  let inner ← compileExcept pos fieldτ (.field (.var r) field) rest rhs
  return .call (.funcLit [(r, goτ)] [goτ]
    [.assign [.field (.var r) field] [inner], .return [.var r]]) [base]

/--
  A builtin operator, applied. `τ` is the *operator's own* type, already specialized by
  the checker, which is where the operand type `=` dispatches on comes from.

  Every case producing a truth value converts back into `tlaplus.Bool`: the runtime's predicates
  answer in Go's `bool`, but a TLA⁺ expression of type `Bool` must be one of the newtypes, since
  everything in a specification has to satisfy `Eq`/`Ord`.
-/
partial def compileIntrinsic (pos : SourceSpan) (name : String) (τ : Typ)
    (args : List ComputableGo.Expression) : m ComputableGo.Expression := do
  -- The operand type of a binary intrinsic, for the ones that dispatch on it.
  let operandτ := match τ with
    | .operator (α :: _) _ => some α
    | _ => none
  match name, args with
  | "=", [x, y] | "/=", [x, y] => do
    let some α := operandτ
      | throw (.internalInvariantViolated pos s!"'{name}' has a non-operator type")
    let eq := tlaBool (← compileEq pos α x y)
    return if name == "=" then eq else .unary .not eq
  -- `Bool` is defined over `bool`, so Go's own connectives apply to it directly and stay in the
  -- newtype — no conversion in either direction.
  | "/\\", [x, y] => return .binary .and x y
  | "\\/", [x, y] => return .binary .or x y
  | "\\neg", [x] => return .unary .not x
  | "=>", [x, y] => return .binary .or (.unary .not x) y
  | "<=>", [x, y] => return tlaBool (.call (.field (tlaplusVar "BoolOrd") "Eq") [x, y])
  -- The runtime takes the dictionary first and the set before the element; TLA⁺ writes the element
  -- first. `\in`'s left operand type *is* the element type, so no destructuring is needed here.
  | "\\in", [x, s] => do
    let some α := operandτ
      | throw (.internalInvariantViolated pos s!"'{name}' has a non-operator type")
    return tlaBool (tlaplusCall "SetIn" [← ordDict α, s, x])
  | "\\notin", [x, s] => do
    let some α := operandτ
      | throw (.internalInvariantViolated pos s!"'{name}' has a non-operator type")
    return tlaBool (.unary .not (tlaplusCall "SetIn" [← ordDict α, s, x]))
  -- These four take two sets, so the dictionary they need is one level down from the operand type.
  | "\\subseteq", [s, t] => do
    let some α := operandτ
      | throw (.internalInvariantViolated pos s!"'{name}' has a non-operator type")
    return tlaBool (tlaplusCall "SetSubseteq" [← setElemDict pos name α, s, t])
  | "\\cup", [s, t] => do
    let some α := operandτ
      | throw (.internalInvariantViolated pos s!"'{name}' has a non-operator type")
    return tlaplusCall "SetUnion" [← setElemDict pos name α, s, t]
  | "\\cap", [s, t] => do
    let some α := operandτ
      | throw (.internalInvariantViolated pos s!"'{name}' has a non-operator type")
    return tlaplusCall "SetIntersect" [← setElemDict pos name α, s, t]
  | "\\", [s, t] => do
    let some α := operandτ
      | throw (.internalInvariantViolated pos s!"'{name}' has a non-operator type")
    return tlaplusCall "SetDifference" [← setElemDict pos name α, s, t]
  | "DOMAIN", [f] => return tlaplusCall "Domain" [f]
  -- The `Str <: Seq(Int)` coercion, and the only intrinsic here no source text can write: it
  -- reaches code generation solely because `Coercion.applyComputable` inserted it. The runtime
  -- fixes the semantics — the sequence of the string's Unicode code points.
  | "StrToSeq", [s] => return tlaplusCall "StrToSeq" [s]
  -- Typed (`builtinContext`) but not compiled. A product's elements are pairs, and a tuple
  -- compiles to an *anonymous* struct built at the site that needs it — so a runtime product
  -- cannot construct its own elements the way `SetUnion` can, and would have to take the pair
  -- constructor as a callback the way `SetMap` takes its function.
  | "\\X", _ =>
    throw (.unsupported pos name
      "a Cartesian product has no runtime representation: its elements are pairs, and a tuple \
       compiles to an anonymous struct that only the site building it can name")
  -- Banned from anything reachable from the algorithm by `WellFormedness/Restrictions.lean`'s
  -- check 3, so reaching code generation means that check did not run or did not hold.
  | "ENABLED", _ | "UNCHANGED", _ | "[]", _ | "<>", _ | "'", _ =>
    throw (.internalInvariantViolated pos
      s!"the temporal/action operator '{name}' reached code generation, but well-formedness \
         checking rejects those in anything the algorithm can reach")
  | _, _ => wrongArity pos name args.length

/-- A reference to a builtin operator that carries no arguments — a *value* exported by a standard
module, not something to apply. -/
partial def compileBuiltinVar (pos : SourceSpan) (mod name : String) (_τ : Typ) :
    m ComputableGo.Expression :=
  match mod, name with
  -- Both denote infinite sets, and the representation is a finite sorted slice. Nothing is
  -- lost by rejecting them: they are only useful as a quantifier's domain, which would not
  -- terminate either.
  | "Naturals", "Nat" | "Integers", "Int" =>
    throw (.unsupported pos name
      "it denotes an infinite set, and sets are represented by their elements")
  | "Bags", _ =>
    throw (.unsupported pos s!"Bags!{name}" "the Bags module has no runtime representation")
  | _, _ =>
    throw (.internalInvariantViolated pos
      s!"'{mod}!{name}' is not a value exported by a standard module")

/-- A builtin operator from a standard module, applied. `Naturals`'s comparisons all go through
`tlaplus.IntOrd` — `Lt` is one of the dictionary's two primitive fields, `Gt`/`Le`/`Ge` are methods
the runtime derives from it once. Arithmetic is not a comparison and takes no dictionary. -/
partial def compileBuiltinCall (pos : SourceSpan) (mod name : String) (τ : Typ)
    (args : List ComputableGo.Expression) : m ComputableGo.Expression :=
  match mod, name, args with
  | "Naturals", "+", [x, y] => return tlaplusCall "Add" [x, y]
  | "Naturals", "-", [x, y] => return tlaplusCall "Sub" [x, y]
  | "Naturals", "*", [x, y] => return tlaplusCall "Mul" [x, y]
  | "Naturals", "\\div", [x, y] => return tlaplusCall "Div" [x, y]
  | "Naturals", "%", [x, y] => return tlaplusCall "Mod" [x, y]
  | "Naturals", "^", [x, y] => return tlaplusCall "Pow" [x, y]
  -- Unary minus is `Integers`, not `Naturals` — `Naturals` has no negatives.
  | "Integers", "-.", [x] => return tlaplusCall "Neg" [x]
  | "Naturals", "<", [x, y] => return tlaBool (.call (.field (tlaplusVar "IntOrd") "Lt") [x, y])
  | "Naturals", ">", [x, y] => return tlaBool (.call (.field (tlaplusVar "IntOrd") "Gt") [x, y])
  | "Naturals", "=<", [x, y] => return tlaBool (.call (.field (tlaplusVar "IntOrd") "Le") [x, y])
  | "Naturals", ">=", [x, y] => return tlaBool (.call (.field (tlaplusVar "IntOrd") "Ge") [x, y])
  | "Naturals", "..", [x, y] => return tlaplusCall "IntRange" [x, y]
  | "Sequences", "Len", [s] => return tlaplusCall "Len" [s]
  | "Sequences", "Head", [s] => return tlaplusCall "Head" [s]
  | "Sequences", "Tail", [s] => return tlaplusCall "Tail" [s]
  | "Sequences", "Append", [s, e] => return tlaplusCall "Append" [s, e]
  -- Every `Set` is finite by construction — the representation is its elements — so the predicate
  -- is constantly true and the count is the element count.
  | "FiniteSets", "IsFiniteSet", [_] => return tlaBool .true
  | "FiniteSets", "Cardinality", [s] => return tlaplusCall "Cardinality" [s]
  | "Bags", _, _ =>
    throw (.unsupported pos s!"Bags!{name}" "the Bags module has no runtime representation")
  -- The whole point of `Fugue`'s `\prec` (`Driver/Builtins.lean`): the order on `Address` that the
  -- type checker does not have, taken from the same dictionary `Ord.lean` hands every other
  -- address-comparing operation.
  | "Fugue", "\\prec", [x, y] => return tlaBool (.call (.field (commVar "AddressOrd") "Lt") [x, y])
  | "Fugue", "\\preceq", [x, y] => return tlaBool (.call (.field (commVar "AddressOrd") "Le") [x, y])
  | "Fugue", "\\succ", [x, y] => return tlaBool (.call (.field (commVar "AddressOrd") "Gt") [x, y])
  | "Fugue", "\\succeq", [x, y] => return tlaBool (.call (.field (commVar "AddressOrd") "Ge") [x, y])
  -- The Apalache-style unsafe downcasts. `FunAsSeq` materializes the lazy function into a slice,
  -- panicking unless its domain is `1 .. n`; `SetAsFun` builds a lazy function from the pair set,
  -- panicking on a first component that repeats. Both raise `-Wunsafe` at type checking.
  | "Fugue", "FunAsSeq", [f] => return tlaplusCall "FunAsSeq" [f]
  | "Fugue", "SetAsFun", [s] => do
    -- The pair type `<<a, b>>` compiles to an anonymous struct only the building site can name, so
    -- the runtime cannot project a pair on its own — it is handed the two projections as callbacks,
    -- the way `SetMap` is handed its mapping function.
    let some (a, b) := (match τ with
      | .operator [.set (.tuple [a, b])] _ => some (a, b)
      | _ => none)
      | throw (.internalInvariantViolated pos "'SetAsFun' does not have its declared type")
    let pairτ ← compileTyp (.tuple [a, b])
    let aτ ← compileTyp a
    let bτ ← compileTyp b
    let p := goIdent (← freshName "p")
    let fst : ComputableGo.Expression :=
      .funcLit [(p, pairτ)] [aτ] [.return [.field (.var p) (projName 1)]]
    let snd : ComputableGo.Expression :=
      .funcLit [(p, pairτ)] [bτ] [.return [.field (.var p) (projName 2)]]
    return tlaplusCall "SetAsFun" [← ordDict a, s, fst, snd]
  | "Fugue", "MkSeq", _ =>
    throw (.unsupported pos "MkSeq"
      "its second argument is an operator, and passing an operator as an argument needs LAMBDA, \
       which this compiler does not have")
  | _, _, [] => compileBuiltinVar pos mod name τ
  | _, _, _ => wrongArity pos s!"{mod}!{name}" args.length

end

/-- `compileExpr` for a term straight from an earlier pass — its binders' bodies still carry de
Bruijn `.bound` indices. `outer` names any binders enclosing `e` that are not nodes within it: an
operator's or function's parameters, or a `multicast` filter's recipient, in source order. Every
caller outside this file goes through here so that `compileExpr` itself only ever meets `.free`
occurrences. -/
def compileExprTop (e : ComputablePlusCal.Expression) (outer : List String := []) :
    m ComputableGo.Expression :=
  compileExpr (e.openHints outer)

/-- `compileExcept` for a path and right-hand side straight from an earlier pass — opens every de
Bruijn index in the index expressions and the right-hand side against its binder hint first. -/
def compileExceptTop (pos : SourceSpan) (τ : Typ) (base : ComputableGo.Expression)
    (path : List (String ⊕ ComputablePlusCal.Expression)) (rhs : ComputablePlusCal.Expression) :
    m ComputableGo.Expression :=
  compileExcept pos τ base
    (path.map (Sum.map id (·.openHints))) (rhs.openHints)

end Network2Go

end
