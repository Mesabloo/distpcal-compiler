module

public import Core.TypedTLAPlus.Coercion
public import Core.ComputableTLAPlus.Syntax

public section


/-!
  `Coercion.applyComputable` is the second of `Core/TypedTLAPlus/Coercion.lean`'s two structural
  recursions over `TypedTLAPlus.Coercion`, discharging against `ComputableTLAPlus.Expression`
  instead of `TypedTLAPlus.Expression`. Needed because a `receive`'s channel/reference coercion is
  stored unapplied and survives past `Typed2Computable`'s type change: `Guarded2Network` is the
  first pass with a concrete `ComputableTLAPlus.Expression` (the built `Head(inbox)`/`Tail(inbox)`
  expression) to discharge it against, so it can't reuse `Coercion.apply` (fixed at
  `TypedTLAPlus.Expr`).

  Mirrors `Coercion.apply` case-for-case, except `choose`'s domain here is a required `Expression
  α` rather than `Option (Expression α)` — see `Core/ComputableTLAPlus/Syntax.lean`'s module doc.
-/

namespace TypedTLAPlus

/-- Checked TLA⁺ expressions at `ComputableTLAPlus`'s output type — what `Coercion.applyComputable`
transforms. -/
abbrev CExpr := ComputableTLAPlus.Expression ComputableTLAPlus.Typ

-- Structural recursion isn't visibly decreasing to Lean here, same as `Coercion.apply` — `partial`
-- until revisited.
/-- Applies a coercion to an already-built `ComputableTLAPlus.Expression` — see the module doc
above for why this can't reuse `Coercion.apply`. Registers every synthesized node at the coerced
expression's own span, for the reason spelled out on `Coercion.apply`. -/
partial def Coercion.applyComputable (c : Coercion) (e : CExpr) : CExpr :=
  let pos := posOf e
  match c with
  | .id => e
  | .strToSeq =>
    .opCall (.var "Str2Seq" (.operator [.str] (.seq .int)) (.module "Sequences") @@ pos) [e] @@ pos
  | .seqToFun τ₀ i =>
    let range : CExpr :=
      .opCall (.var ".." (.operator [.int, .int] (.set .int)) (.module "Naturals") @@ pos)
        [.nat "1" @@ pos,
         .opCall (.var "Len" (.operator [.seq τ₀] .int) (.module "Sequences") @@ pos) [e] @@ pos] @@ pos
    .fn i .int τ₀ range (.fnCall e (.seq τ₀) (.var i .int .binder @@ pos) @@ pos) @@ pos
  | .tupleToSeq n τ =>
    .seq ((List.range n).map λ i ↦
      .fnCall e (.tuple (List.replicate n τ)) (.nat (toString (i + 1)) @@ pos) @@ pos) τ @@ pos
  | .set x τ τ' c =>
    .map' (c.applyComputable (.var x τ .binder @@ pos)) x τ τ' e @@ pos
  | .tuple coes τs τs' =>
    (.tuple <| ((List.range coes.length).zip coes).zip τs' |>.map λ ((i, c), τ'ᵢ) ↦
      (τ'ᵢ, c.applyComputable (.fnCall e (.tuple τs) (.nat (toString (i + 1)) @@ pos) @@ pos))) @@ pos
  | .record fields =>
    (.record <| fields.map λ (name, c, τ'ᵢ) ↦
      (τ'ᵢ, name, c.applyComputable (.recordAccess e name @@ pos))) @@ pos
  | .function x y dom rng dom' rng' cDom cRng =>
    let domainExpr : CExpr :=
      .opCall (.var "DOMAIN" (.operator [.function dom rng] (.set dom)) .intrinsic @@ pos) [e] @@ pos
    let newDomain : CExpr :=
      .map' (cDom.applyComputable (.var x dom .binder @@ pos)) x dom dom' domainExpr @@ pos
    let eqTy : Typ := .operator [dom', dom'] .bool
    let recoveredArg : CExpr :=
      .choose x dom domainExpr
        (.opCall (.var "=" eqTy .intrinsic @@ pos)
          [cDom.applyComputable (.var x dom .binder @@ pos), .var y dom' .binder @@ pos] @@ pos) @@ pos
    .fn y dom' rng' newDomain (cRng.applyComputable (.fnCall e (.function dom rng) recoveredArg @@ pos)) @@ pos
  | .comp c₁ c₂ => c₂.applyComputable (c₁.applyComputable e)

end TypedTLAPlus

end
