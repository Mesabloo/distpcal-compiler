module

public import Core.ComputableTLAPlus.Syntax

public section

/-!
  Recovering the type of a checked expression.

  `Typed2Computable`'s output is annotated, not *fully* annotated: the checker records a type at
  each site where re-deriving one would need `Γ` (`var`, the empty-literal cases, each binder's
  bound variable, each record field), and leaves the rest implied. `Network2Go` needs the implied
  ones back, because Go is explicitly typed exactly where TLA⁺ is not — a `func` literal must
  declare its return type, so compiling `{e : x ∈ S}`, `[x ∈ S ↦ e]`, `IF`/`CASE` all require the
  type of a sub-expression that carries no annotation of its own.

  This is a re-derivation, not a re-check: every case reads a type off an annotation or projects
  one out of a sub-expression's type, and nothing is unified or verified. It is therefore only
  correct on the checker's own output — which is the only thing that ever reaches it.

  `Option` rather than a diagnostic monad, keeping `Core/` free of any pass's error type. A `none`
  means the input was not well-typed in a way the checker should already have rejected
  (`DOMAIN`-less `.recordAccess` on a non-record, an operator-typed head that isn't an operator),
  so callers report it as an internal-invariant violation rather than a user error.
-/

namespace ComputableTLAPlus

/-- The type of a checked expression — see the module doc for what `none` means. -/
partial def Expression.typeOf? : Expression Typ → Option Typ
  | .var _ τ _ => some τ
  -- An application's type is its head's result type. The head is an *operator*, not a function:
  -- `f[e]` is `.fnCall`, below.
  | .opCall f _ => do
    match ← Expression.typeOf? f with
    | .operator _ ρ => some ρ
    | _ => none
  | .forall .. | .exists .. => some .bool
  -- `CHOOSE x \in S : P` picks an element of `S`, so its type is the bound variable's.
  | .choose _ τ _ _ => some τ
  | .set _ τ => some (.set τ)
  -- Filtering keeps the element type; the image of a map takes the body's.
  | .collect _ τ _ _ => some (.set τ)
  | .map' e _ _ _ => (.set ·) <$> Expression.typeOf? e
  | .fnCall f _ => do
    match ← Expression.typeOf? f with
    | .function _ ρ => some ρ
    -- `s[i]` on a sequence, and on a tuple whose components all agree; a tuple whose components
    -- differ has no single result type, so the caller must read the index literal instead.
    | .seq τ => some τ
    | .tuple (τ :: τs) => if τs.all (· == τ) then some τ else none
    | _ => none
  | .fn _ τ _ e => (.function τ ·) <$> Expression.typeOf? e
  | .record fs => some (.record (fs.map λ (τ, x, _) ↦ (x, τ)))
  -- `[f EXCEPT ...]` has the same type as `f`: an override changes values, never the shape.
  | .except e _ => Expression.typeOf? e
  | .recordAccess e x => do
    match ← Expression.typeOf? e with
    | .record fs => fs.lookup x
    | _ => none
  | .tuple es => some (.tuple (es.map Prod.fst))
  | .seq _ τ => some (.seq τ)
  -- Both arms of an `IF` and every arm of a `CASE` were checked against one type, so any arm
  -- answers for all of them.
  | .if _ e₂ _ => Expression.typeOf? e₂
  | .case ((_, e) :: _) _ => Expression.typeOf? e
  | .case [] (some e) => Expression.typeOf? e
  | .case [] none => none
  | .nat _ => some .int
  | .str _ => some .str
  | .true | .false => some .bool

end ComputableTLAPlus

end
