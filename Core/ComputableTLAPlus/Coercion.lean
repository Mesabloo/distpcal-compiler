module

public import Core.TypedTLAPlus.Coercion
public import Core.ComputableTLAPlus.Syntax

public section


/-!
  `Coercion.applyComputable` — the second of `Core/TypedTLAPlus/Coercion.lean`'s two structural
  recursions consuming `TypedTLAPlus.Coercion` data, this one discharging against
  `ComputableTLAPlus.Expression` instead of `TypedTLAPlus.Expression`. Needed because a `receive`
  statement's channel/reference coercion is stored unapplied on the `receive` node and survives
  past `Typed2Computable`'s type change — `Guarded2Network` is the first pass with a concrete
  `ComputableTLAPlus.Expression` to discharge it against (the freshly-built `Head(inbox)`/
  `Tail(inbox)` expression), so this can't reuse `Coercion.apply` (fixed at `TypedTLAPlus.Expr`).

  Same case-for-case structure as `Coercion.apply` — every constructor `Coercion.apply` handles
  has a like-shaped `ComputableTLAPlus.Expression` counterpart, except `choose`'s domain is a
  required `Expression α`, not `Option (Expression α)` (`Core/ComputableTLAPlus/Syntax.lean`'s
  own module doc explains why).
-/

namespace TypedTLAPlus

/-- Checked TLA⁺ expressions at `ComputableTLAPlus`'s own output type — what `Coercion.
applyComputable` transforms. -/
abbrev CExpr := ComputableTLAPlus.Expression ComputableTLAPlus.Typ

-- Structural recursion isn't visibly decreasing to Lean here, same as `Coercion.apply` — see its
-- own note in `Core/TypedTLAPlus/Coercion.lean` — `partial` until revisited.
/-- Apply a coercion to an already-built `ComputableTLAPlus.Expression` — see the module doc
above for why this can't just reuse `Coercion.apply`. -/
partial def Coercion.applyComputable : Coercion → CExpr → CExpr
  | .id, e => e
  | .strToSeq, e =>
    .opCall (.var "Str2Seq" (.operator [.str] (.seq .int)) .intrinsic) [e]
  | .seqToFun τ₀ i, e =>
    let range : CExpr := .opCall (.var ".." (.operator [.int, .int] (.set .int)) (.module "Naturals"))
      [.nat "1", .opCall (.var "Len" (.operator [.seq τ₀] .int) (.module "Sequences")) [e]]
    .fn i .int range (.fnCall e (.var i .int .binder))
  | .tupleToSeq n τ, e =>
    .seq ((List.range n).map λ i ↦ .fnCall e (.nat (toString (i + 1)))) τ
  | .set x τ c, e =>
    .map' (c.applyComputable (.var x τ .binder)) x τ e
  | .tuple coes τs', e =>
    .tuple <| ((List.range coes.length).zip coes).zip τs' |>.map λ ((i, c), τ'ᵢ) ↦
      (τ'ᵢ, c.applyComputable (.fnCall e (.nat (toString (i + 1)))))
  | .record fields, e =>
    .record <| fields.map λ (name, c, τ'ᵢ) ↦ (τ'ᵢ, name, c.applyComputable (.recordAccess e name))
  | .function x y dom rng dom' cDom cRng, e =>
    let domainExpr : CExpr := .opCall (.var "DOMAIN" (.operator [.function dom rng] (.set dom)) .intrinsic) [e]
    let newDomain : CExpr := .map' (cDom.applyComputable (.var x dom .binder)) x dom domainExpr
    let eqTy : Typ := .operator [dom', dom'] .bool
    let recoveredArg : CExpr :=
      .choose x dom domainExpr
        (.opCall (.var "=" eqTy .intrinsic) [cDom.applyComputable (.var x dom .binder), .var y dom' .binder])
    .fn y dom' newDomain (cRng.applyComputable (.fnCall e recoveredArg))
  | .comp c₁ c₂, e => c₂.applyComputable (c₁.applyComputable e)

end TypedTLAPlus

end
