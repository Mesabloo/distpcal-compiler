module

public import Network2Go.Typ
public import Core.ComputableTLAPlus.TypeOf
public import Core.ComputablePlusCal.Syntax
public import Core.Go.Syntax
public import Common.Fresh

public section

/-!
  Compiling TLA⁺ expressions into Go expressions (thesis §7.2.1.2).

  The output is a single `Go.Expression`, never a statement prelude: everything that needs
  statements to express — the quantifiers' search loops, `IF`/`CASE`'s laziness, `EXCEPT`'s record
  update — is wrapped in an immediately-applied `Go.Expression.funcLit`. That keeps this function
  callable from any expression position (a branch's guard, an argument, another expression's
  sub-term) without every caller having to thread a list of statements to emit first. `funcLit`
  exists in `Core/Go/Syntax.lean` precisely because §7.2.1.2 cannot be compiled without it.

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
  - **Operator applications dispatch on the head's `Origin`.** `\in`, `=` and friends are not Go
    functions with those names — `x \in S` reverses its arguments into `SetIn(S, x)` and `=` picks
    between `Eq`, `SetEq` and `SeqEq` by operand type — so a builtin head is matched at the
    application site rather than compiled to a name and applied. A *bare* builtin reference (one
    passed around rather than applied) has no Go counterpart at all and is rejected.

  Deliberately not handled here, since they are not expression forms: operator and function
  *definitions* (§7.2.2, including `MkRecFn` for recursive ones) and the renaming of user-chosen
  names that collide after capitalization. Both are the pass's own later steps.

  **Known limitation, needs the record-type work before it is real.** `compileTyp` gives records and
  tuples *anonymous* Go struct types, and Go cannot define methods on those, so a compiled record
  satisfies neither `Eq` nor `Ord`. Every use below that puts a record inside a set, a sequence or a
  function key therefore emits code that will not compile until record and tuple types are emitted
  as named declarations carrying generated `Eq`/`Ord` methods. That is the open half of
  `runtime/tlaplus/records.go`'s question, and it is a design step of its own.
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
  { "Naturals", "Integers", "Sequences", "FiniteSets", "Bags", "TLC" }

/-- `bool(e)` — Go's conversion out of the runtime's `Bool`, needed wherever a real `bool` is
required: an `if` condition, and every predicate the runtime library takes. -/
private def goBool (e : ComputableGo.Expression) : ComputableGo.Expression :=
  .call (.var "bool") [e]

/-- `tlaplus.Bool(e)` — the conversion back, wrapping anything that produced a Go `bool`. -/
private def tlaBool (e : ComputableGo.Expression) : ComputableGo.Expression :=
  tlaplusCall "Bool" [e]

/-- The type of a checked sub-expression, already compiled to Go. A `none` from `typeOf?` means the
checker's output was not well-typed in a way it should itself have rejected — see
`Core/ComputableTLAPlus/TypeOf.lean`. -/
private def compileTypeOf (pos : SourceSpan) (e : ComputablePlusCal.Expression) : m Go.Typ := do
  match e.typeOf? with
  | some τ => compileTyp τ
  | none =>
    throw (.internalInvariantViolated pos
      "the type of a checked expression could not be re-derived, so its Go type is unknown")

/-- An operator applied to the wrong number of arguments — impossible past type checking, which
checks every application's arity. -/
private def wrongArity (pos : SourceSpan) (name : String) (n : Nat) : m ComputableGo.Expression :=
  throw (.internalInvariantViolated pos
    s!"'{name}' applied to {n} arguments, which type checking should already have rejected")

/-- TLA⁺ `=` and `#`, dispatched on the operand type: the runtime gives `Eq` as a *method* on each
value type, but `Set` and `Seq` are slice types whose equality cannot be a method (it needs more of
the element type than the type declaration demands), so those are free functions instead.

Functions have no equality at all: comparing two lazy maps means comparing them on every point of
their domain, which the representation deliberately does not do (`§7.2.1.2`). -/
private def compileEq (pos : SourceSpan) (τ : Typ) (x y : ComputableGo.Expression) :
    m ComputableGo.Expression :=
  match τ with
  | .set _ => return tlaplusCall "SetEq" [x, y]
  | .seq _ => return tlaplusCall "SeqEq" [x, y]
  | .function _ _ =>
    throw (.unsupported pos "="
      "two functions can only be compared by comparing them at every point of their domain, which \
       the lazy-map representation does not do")
  | .operator _ _ =>
    throw (.internalInvariantViolated pos
      "an operator reached '=', but operators are not values in TLA⁺")
  | _ => return .call (.field x "Eq") [y]

mutual

/--
  Compiles a checked TLA⁺ expression into the Go expression that computes it (§7.2.1.2).
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
  -- A bound variable — a quantifier's, a process's, a branch's — keeps the name it had: §7.2.2
  -- capitalizes *definitions*, not variables.
  | .var name _ .binder, _ => return .var name
  | .var name τ (.module mod), pos =>
    if builtinModuleNames.contains mod then compileBuiltinVar pos mod name τ
    -- A user definition. `LOCAL` ones keep their case, which this reference cannot see; the
    -- definition-compilation step owns that flag and has to agree with what is emitted here.
    else return .var (definitionName (isLocal := false) name)
  | .var name _ .intrinsic, pos =>
    throw (.unsupported pos name
      "a builtin operator can only be applied, not passed around as a value — Go has no \
       counterpart to refer to")
  | .opCall f args, pos => do
    let args' ← args.mapM compileExpr
    match f with
    | .var name τ .intrinsic => compileIntrinsic pos name τ args'
    | .var name τ (.module mod) =>
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
    else return tlaplusCall "MkSet" (← es.mapM compileExpr)
  | .seq es τ, _ => do
    if es.isEmpty then return .sliceLit (tlaplusTyp "Seq" [← compileTyp τ]) []
    else return tlaplusCall "MkSeq" (← es.mapM compileExpr)
  | .collect x τ dom body, _ =>
    return tlaplusCall "SetFilter" [← compileExpr dom, ← compilePredicate x τ body]
  | .map' body x τ dom, pos => do
    -- `SetMap` renormalizes its result: the mapping function is neither monotone nor injective in
    -- general, so neither the sortedness nor the duplicate-freedom invariant survives it.
    let elemτ ← compileTyp τ
    let resultτ ← compileTypeOf pos body
    return tlaplusCall "SetMap"
      [← compileExpr dom, .funcLit [(x, elemτ)] [resultτ] [.return [← compileExpr body]]]
  | .fn x τ dom body, pos => do
    let elemτ ← compileTyp τ
    let resultτ ← compileTypeOf pos body
    return tlaplusCall "FnConstructor"
      [← compileExpr dom, .funcLit [(x, elemτ)] [resultτ] [.return [← compileExpr body]]]
  | .fnCall f i, pos => do
    let f' ← compileExpr f
    match f.typeOf? with
    | some (.function _ _) => return tlaplusCall "FnApply" [f', ← compileExpr i]
    | some (.seq _) => return tlaplusCall "SeqIndex" [f', ← compileExpr i]
    -- A tuple is a struct, so its components are reachable only by name, and the name is fixed by
    -- the index — which therefore has to be a literal.
    | some (.tuple _) =>
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
  | .record fs, pos => do
    let τ ← compileTypeOf pos e
    -- Field order in a keyed composite literal is free, but the fields are sorted anyway so that
    -- the same record written two ways compiles to identical output, as its *type* already does.
    let fields ← fs.mapM λ (_, x, e') ↦ return (fieldName x, ← compileExpr e')
    return .structLit τ (fields.mergeSort λ (x, _) (y, _) ↦ x ≤ y)
  | .tuple es, pos => do
    let τ ← compileTypeOf pos e
    let fields ← es.zipIdx.mapM λ ((_, e'), i) ↦ return (projName (i + 1), ← compileExpr e')
    return .structLit τ fields
  | .except f upds, pos => do
    let τ ← match f.typeOf? with
      | some τ => pure τ
      | none =>
        throw (.internalInvariantViolated pos
          "the type of an EXCEPT's target could not be re-derived")
    -- Each override applies to the result of the previous one, so `[f EXCEPT ![1] = a, ![2] = b]`
    -- is one function with both points changed rather than two independent overrides of `f`.
    upds.foldlM (init := ← compileExpr f) λ acc (path, rhs) ↦ compileExcept pos τ acc path rhs
  | .if c t f, pos => do
    let τ ← compileTypeOf pos t
    -- An immediately-applied literal, not a helper taking both arms: Go evaluates arguments
    -- eagerly, and `IF x # 0 THEN 1 \div x ELSE 0` must not evaluate the arm it did not select.
    return .call (.funcLit [] [τ]
      [.if (goBool (← compileExpr c)) [.return [← compileExpr t]] [],
        .return [← compileExpr f]]) []
  | .case arms other, pos => do
    let τ ← compileTypeOf pos e
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
  return .funcLit [(x, ← compileTyp τ)] [.bool] [.return [goBool (← compileExpr body)]]

/--
  `\A x \in S : P` and `\E x \in S : P`, per §7.2.1.2: a search of `S` for the first
  counterexample/witness, the two being De Morgan duals of one another.

  Written as a loop inside an immediately-applied literal rather than as
  `Cardinality(SetFilter(S, ¬P)) = 0`, because the filter would evaluate `P` at every element even
  after the answer is settled — visible whenever `P` is undefined somewhere in `S`. `S` becomes the
  literal's parameter so that it is evaluated exactly once.
-/
partial def compileQuantifier (isForall : Bool) (x : String) (τ : Typ)
    (dom body : ComputablePlusCal.Expression) : m ComputableGo.Expression := do
  let elemτ ← compileTyp τ
  let s ← freshName "set"
  let i ← freshName "i"
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
    | .function _ ρ =>
      return tlaplusCall "FnOverload"
        [base, i', ← compileExcept pos ρ (tlaplusCall "FnApply" [base, i']) rest rhs]
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
  let r ← freshName "rec"
  let inner ← compileExcept pos fieldτ (.field (.var r) field) rest rhs
  return .call (.funcLit [(r, goτ)] [goτ]
    [.assign [.field (.var r) field] [inner], .return [.var r]]) [base]

/--
  A builtin operator, applied (§7.2.1.2). `τ` is the *operator's own* type, already specialized by
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
  | "<=>", [x, y] => return tlaBool (.call (.field x "Eq") [y])
  -- The runtime takes the set first, TLA⁺ writes the element first.
  | "\\in", [x, s] => return tlaBool (tlaplusCall "SetIn" [s, x])
  | "\\notin", [x, s] => return tlaBool (.unary .not (tlaplusCall "SetIn" [s, x]))
  | "\\subseteq", [s, t] => return tlaBool (tlaplusCall "SetSubseteq" [s, t])
  | "\\cup", [s, t] => return tlaplusCall "SetUnion" [s, t]
  | "\\cap", [s, t] => return tlaplusCall "SetIntersect" [s, t]
  | "\\", [s, t] => return tlaplusCall "SetDifference" [s, t]
  | "DOMAIN", [f] => return tlaplusCall "Domain" [f]
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
  -- Both denote infinite sets, and the representation is a finite sorted slice (§9.15). Nothing is
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

/-- A builtin operator from a standard module, applied. `Naturals`'s comparisons are methods on
`Int`, except `=<`/`>=` which the runtime derives generically from `Lt`/`Eq`. -/
partial def compileBuiltinCall (pos : SourceSpan) (mod name : String) (τ : Typ)
    (args : List ComputableGo.Expression) : m ComputableGo.Expression :=
  match mod, name, args with
  | "Naturals", "+", [x, y] => return tlaplusCall "Add" [x, y]
  | "Naturals", "-", [x, y] => return tlaplusCall "Sub" [x, y]
  | "Naturals", "-.", [x] => return tlaplusCall "Neg" [x]
  | "Naturals", "*", [x, y] => return tlaplusCall "Mul" [x, y]
  | "Naturals", "<", [x, y] => return tlaBool (.call (.field x "Lt") [y])
  | "Naturals", ">", [x, y] => return tlaBool (.call (.field x "Gt") [y])
  | "Naturals", "=<", [x, y] => return tlaBool (tlaplusCall "Le" [x, y])
  | "Naturals", ">=", [x, y] => return tlaBool (tlaplusCall "Ge" [x, y])
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
  | _, _, [] => compileBuiltinVar pos mod name τ
  | _, _, _ => wrongArity pos s!"{mod}!{name}" args.length

end

end Network2Go

end
