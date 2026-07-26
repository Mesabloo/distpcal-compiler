module

public import Network2Go.Typ

public section

/-!
  Building the `Ord` dictionary a TLA⁺ type is ordered by.

  The runtime represents ordering as a *value* — `tlaplus.Ord[T]` is a struct of two functions,
  `Eq` and `Lt` — rather than as an interface a type implements. Go has no conditional method sets,
  so `Set[T]` could not declare a comparison that calls `T`'s; a dictionary sidesteps that, keeps
  every container `[T any]`, and makes nesting ordinary composition (`Set[Set[Int]]`'s dictionary is
  `SetOrd(SetOrd(IntOrd))`). Every runtime operation that compares takes one.

  So `ordDict` is a second fold over `Typ`, mirroring `compileTyp` constructor for constructor: one
  produces the type, the other the dictionary ordering it. The two must agree, since a `Set` does
  not record which dictionary built it and every operation on it has to be handed the same one —
  that they are derived from the same `Typ` is what guarantees it.

  Three kinds of answer:

  - **Closed expressions**, for everything built out of the runtime's own types: a package-level
    value (`tlaplus.IntOrd`) or a constructor applied to its components (`tlaplus.SetOrd(…)`).
  - **A literal**, for records and tuples. These compile to *anonymous* Go structs, which can carry
    no methods — but a dictionary needs none, so the comparison functions are written out inline at
    each use. This is what removed the need for generated named types and a mangling scheme; Go
    identifies anonymous struct types structurally, so two identically-shaped records are already
    the same type, and `compileTyp`'s field sorting is what makes the shapes coincide.
  - **A parameter**, for a rigid type variable, bound by the enclosing definition.

  Rejected wholesale: `.operator`. Operators compile to Go `func`s, which have no equality at all,
  and TLA⁺ operators are not values, so one can never appear inside a set, a sequence, a record or
  a function's domain.
-/

namespace Network2Go

open ComputableTLAPlus (Typ)

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty N2GError m]

/-- `x.f` and `y.f`, the pair of field accesses every component of a struct dictionary compares. -/
private def fieldPair (x y : String) (f : String) :
    ComputableGo.Expression × ComputableGo.Expression :=
  (.field (.var x) f, .field (.var y) f)

mutual

/--
  The dictionary ordering values of a TLA⁺ type (§7.2.1.2).

  Fails on exactly the types that have no ordering and cannot need one — see the module doc.
-/
partial def ordDict : Typ → m ComputableGo.Expression
  | .bool => return tlaplusVar "BoolOrd"
  | .int => return tlaplusVar "IntOrd"
  | .str => return tlaplusVar "StrOrd"
  | .set τ => return tlaplusCall "SetOrd" [← ordDict τ]
  | .seq τ => return tlaplusCall "SeqOrd" [← ordDict τ]
  -- A placeholder in the runtime: ordering two lazy maps means forcing both domains and comparing
  -- pointwise, which is well defined and which nothing exercises yet. Emitting the call is still
  -- right — the panic belongs at the point a specification actually orders two functions.
  | .function dom rng => return tlaplusCall "FnOrd" [← ordDict dom, ← ordDict rng]
  | .address => return commVar "AddressOrd"
  -- The user's own Go type carries `Eq`/`Lt` as methods, which is the natural idiom for a
  -- hand-written type; the bridge from methods to a dictionary is Go's method-expression syntax
  -- and is a closed expression, so nothing needs declaring for it.
  | .const c => do
    let c := definitionName (isLocal := false) c
    let methods := [("Eq", Go.Expression.field (.var c) "Eq"), ("Lt", .field (.var c) "Lt")]
    return .structLit (tlaplusTyp "Ord" [.named c []]) methods
  | .var a => return .var (ordParamName a)
  | .tuple τs => do
    structDict (← compileTyp (.tuple τs))
      (τs.zipIdx.map λ (τ, i) ↦ (projName (i + 1), τ))
  | .record fs => do
    -- Sorted by *Go* field name, matching `compileTyp`'s own sort: the struct's field order and
    -- the order this dictionary compares in are then the same, and both are independent of how the
    -- record was spelled in the source.
    let fields := (fs.map λ (x, τ) ↦ (fieldName x, τ)).mergeSort λ (x, _) (y, _) ↦ x ≤ y
    structDict (← compileTyp (.record fs)) fields
  | .operator τs τ =>
    throw (.internalInvariantViolated SourceSpan.placeholder
      s!"an ordering was asked for an operator type ({repr τs}) => {repr τ}, but operators are not \
         values in TLA⁺ and cannot occur inside one")
  | .channel τ =>
    throw (.internalInvariantViolated SourceSpan.placeholder
      s!"an ordering was asked for Channel({repr τ}), but channels are not first-class")
  | .mvar n =>
    throw (.internalInvariantViolated SourceSpan.placeholder
      s!"unresolved metavariable ?{n} survived type checking")

/--
  The dictionary for a record or a tuple, as a literal beside the anonymous struct type it orders.

  Equality is componentwise; the order is lexicographic in the struct's own field order. Both are
  written against `goτ`, which the caller has already computed, so that the type is spelled
  identically in the literal's type argument and in both function signatures — Go compares
  anonymous struct types structurally, and a mismatch would not be a type error, just a different
  type.
-/
partial def structDict (goτ : Go.Typ) (fields : List (String × Typ)) :
    m ComputableGo.Expression := do
  let dicts ← fields.mapM λ (f, τ) ↦ return (f, ← ordDict τ)
  return .structLit (tlaplusTyp "Ord" [goτ])
    [("Eq", .funcLit [("x", goτ), ("y", goτ)] [.bool] [.return [eqBody dicts]]),
      ("Lt", .funcLit [("x", goτ), ("y", goτ)] [.bool] (ltBody dicts))]
where
  /-- `d₁.Eq(x.F₁, y.F₁) && … && dₙ.Eq(x.Fₙ, y.Fₙ)`; an empty struct has one value, so `true`. -/
  eqBody (dicts : List (String × ComputableGo.Expression)) : ComputableGo.Expression :=
    match dicts.map (λ (f, d) ↦ let (xf, yf) := fieldPair "x" "y" f; .call (.field d "Eq") [xf, yf]) with
    | [] => .true
    | e :: es => es.foldl (.binary .and) e
  /--
    Lexicographic `<`: at each component, `true` if it is already smaller, `false` if it differs the
    other way, and on to the next when they agree. The last component answers on its own — there is
    nothing left to break a tie with — and an empty struct is never smaller than itself.
  -/
  ltBody : List (String × ComputableGo.Expression) → List ComputableGo.Statement
    | [] => [.return [.false]]
    | [(f, d)] => let (xf, yf) := fieldPair "x" "y" f; [.return [.call (.field d "Lt") [xf, yf]]]
    | (f, d) :: rest =>
      let (xf, yf) := fieldPair "x" "y" f
      .if (.call (.field d "Lt") [xf, yf]) [.return [.true]] []
        :: .if (.unary .not (.call (.field d "Eq") [xf, yf])) [.return [.false]] []
        :: ltBody rest

end

/-- The rigid type variables a type mentions, in first-occurrence order — the type parameters, and
hence the dictionary parameters, a definition of that type has to bind (§7.2.2: type variables are
propagated to the nearest enclosing function definition). -/
partial def Typ.typeVars : Typ → List String
  | .var a => [a]
  | .set τ | .seq τ | .channel τ => Typ.typeVars τ
  | .function τ₁ τ₂ => dedup (Typ.typeVars τ₁ ++ Typ.typeVars τ₂)
  | .tuple τs => dedup (τs.flatMap Typ.typeVars)
  | .record fs => dedup (fs.flatMap λ (_, τ) ↦ Typ.typeVars τ)
  | .operator τs τ => dedup (τs.flatMap Typ.typeVars ++ Typ.typeVars τ)
  | .bool | .int | .str | .address | .const _ | .mvar _ => []
where
  /-- First occurrence wins, so that a definition's type parameters come out in the order its own
  type reads. -/
  dedup (xs : List String) : List String :=
    xs.foldl (init := []) λ acc a ↦ if acc.contains a then acc else acc ++ [a]

end Network2Go

end
