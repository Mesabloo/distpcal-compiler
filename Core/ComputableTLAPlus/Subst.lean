module

public import Core.ComputableTLAPlus.Syntax
public import Core.TypedPlusCal.Syntax

@[expose] public section


/-!
  Substitution for `ComputableTLAPlus.Expression`, mirroring `CoreTLAPlus.Expression.subst`
  (`Desugarer/TLAPlus.lean:73`) against this type's smaller constructor set: no temporal binders
  (`fforall`/`eexists`), no `fnSet`/`recordSet`/`stutter`, but an extra `seq` (checking-mode
  literal sequences, distinct from synthesis-mode `tuple`) with no `CoreTLAPlus` equivalent.

  First consumer: `Computable2Guarded/FlatReord.lean`'s `𝒞_reord` case, substituting a preceding
  action's effect into a guard expression floated past it.
-/

namespace ComputableTLAPlus

/-- Substitute every free occurrence of `Expression.var x` with `e`, stopping at any binder that
rebinds `x` (a binder's domain expression is not under its own scope, so it's substituted into
regardless). -/
partial def Expression.subst {α} (x : String) (e : Expression α) : Expression α → Expression α
  | .var y τ o => if y == x then e else .var y τ o
  | .opCall f es => .opCall (subst x e f) (subst x e <$> es)
  | .forall y ann dom body => .forall y ann (subst x e dom) (if y == x then body else subst x e body)
  | .exists y ann dom body => .exists y ann (subst x e dom) (if y == x then body else subst x e body)
  | .choose y ann dom body => .choose y ann (subst x e dom) (if y == x then body else subst x e body)
  | .set es τ => .set (subst x e <$> es) τ
  | .collect y ann dom pred => .collect y ann (subst x e dom) (if y == x then pred else subst x e pred)
  | .map' body y ann dom => .map' (if y == x then body else subst x e body) y ann (subst x e dom)
  | .fnCall f e' => .fnCall (subst x e f) (subst x e e')
  | .fn y ann dom body => .fn y ann (subst x e dom) (if y == x then body else subst x e body)
  | .record fs => .record (fs.map λ (ann, name, v) ↦ (ann, name, subst x e v))
  | .except f upds => .except (subst x e f) (upds.map λ (path, v) ↦ (path.map (Sum.map id (subst x e)), subst x e v))
  | .recordAccess f name => .recordAccess (subst x e f) name
  | .tuple es => .tuple (es.map λ (τ, e') ↦ (τ, subst x e e'))
  | .seq es τ => .seq (subst x e <$> es) τ
  | .if e₁ e₂ e₃ => .if (subst x e e₁) (subst x e e₂) (subst x e e₃)
  | .case bs other => .case (bs.map (Bifunctor.bimap (subst x e) (subst x e))) (subst x e <$> other)
  | .nat n => .nat n
  | .str s => .str s
  | .true => .true
  | .false => .false

/-- `e'[e\r]`: substitutes a preceding `r≔e` assignment's effect into a later expression `e'`. A
bare-variable `r` (no `.args`) substitutes directly; a compound `r` (with field/index segments)
instead substitutes the whole variable with `[var(r) EXCEPT !path = e]`. `r.args` is already the
`List (String ⊕ Expression α)` shape `Expression.except` takes, so it's just a one-entry `except`
list, no reshaping needed. -/
def Expression.substRef {α} (r : ElaboratedPlusCal.Ref α (Expression α)) (rhs e' : Expression α) :
    Expression α :=
  if r.args.isEmpty then
    Expression.subst r.name rhs e'
  else
    Expression.subst r.name (.except (.var r.name r.baseType .binder) [(r.args, rhs)]) e'

end ComputableTLAPlus

end
