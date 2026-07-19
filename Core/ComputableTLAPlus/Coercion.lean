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
above for why this can't reuse `Coercion.apply`. -/
partial def Coercion.applyComputable : Coercion → CExpr → CExpr
  | .id, e => e
  | .strToSeq, e =>
    .opCall (.var "Str2Seq" (.operator [.str] (.seq .int)) (.module "Sequences")) [e]
  | .seqToFun τ₀ i, e =>
    let range : CExpr := .opCall (.var ".." (.operator [.int, .int] (.set .int)) (.module "Naturals"))
      [.nat "1", .opCall (.var "Len" (.operator [.seq τ₀] .int) (.module "Sequences")) [e]]
    .fn i .int τ₀ range (.fnCall e (.seq τ₀) (.var i .int .binder))
  | .tupleToSeq n τ, e =>
    .seq ((List.range n).map λ i ↦
      .fnCall e (.tuple (List.replicate n τ)) (.nat (toString (i + 1)))) τ
  | .set x τ τ' c, e =>
    .map' (c.applyComputable (.var x τ .binder)) x τ τ' e
  | .tuple coes τs τs', e =>
    .tuple <| ((List.range coes.length).zip coes).zip τs' |>.map λ ((i, c), τ'ᵢ) ↦
      (τ'ᵢ, c.applyComputable (.fnCall e (.tuple τs) (.nat (toString (i + 1)))))
  | .record fields, e =>
    .record <| fields.map λ (name, c, τ'ᵢ) ↦ (τ'ᵢ, name, c.applyComputable (.recordAccess e name))
  | .function x y dom rng dom' rng' cDom cRng, e =>
    let domainExpr : CExpr := .opCall (.var "DOMAIN" (.operator [.function dom rng] (.set dom)) .intrinsic) [e]
    let newDomain : CExpr := .map' (cDom.applyComputable (.var x dom .binder)) x dom dom' domainExpr
    let eqTy : Typ := .operator [dom', dom'] .bool
    let recoveredArg : CExpr :=
      .choose x dom domainExpr
        (.opCall (.var "=" eqTy .intrinsic) [cDom.applyComputable (.var x dom .binder), .var y dom' .binder])
    .fn y dom' rng' newDomain (cRng.applyComputable (.fnCall e (.function dom rng) recoveredArg))
  | .comp c₁ c₂, e => c₂.applyComputable (c₁.applyComputable e)

end TypedTLAPlus

end
