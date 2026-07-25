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
regardless).

Every rebuilt node is re-registered at the span the original carried, for the same reason
`CoreTLAPlus.Expression.subst` does it: substitution rebuilds a whole path through the
expression, and an unregistered node is one `posOf` answers for with an unrelated node's span
(`Common/Position.lean`). -/
partial def Expression.subst {α} (x : String) (e : Expression α) (target : Expression α) :
    Expression α := match_source target with
  | .var y τ o, pos => if y == x then e else .var y τ o @@ pos
  | .opCall f es, pos => .opCall (subst x e f) (subst x e <$> es) @@ pos
  | .forall y ann dom body, pos => .forall y ann (subst x e dom) (if y == x then body else subst x e body) @@ pos
  | .exists y ann dom body, pos => .exists y ann (subst x e dom) (if y == x then body else subst x e body) @@ pos
  | .choose y ann dom body, pos => .choose y ann (subst x e dom) (if y == x then body else subst x e body) @@ pos
  | .set es τ, pos => .set (subst x e <$> es) τ @@ pos
  | .collect y ann dom pred, pos => .collect y ann (subst x e dom) (if y == x then pred else subst x e pred) @@ pos
  | .map' body y ann cod dom, pos =>
    .map' (if y == x then body else subst x e body) y ann cod (subst x e dom) @@ pos
  | .fnCall f fnTyp e', pos => .fnCall (subst x e f) fnTyp (subst x e e') @@ pos
  | .fn y ann cod dom body, pos =>
    .fn y ann cod (subst x e dom) (if y == x then body else subst x e body) @@ pos
  | .record fs, pos => .record (fs.map λ (ann, name, v) ↦ (ann, name, subst x e v)) @@ pos
  | .except f τ upds, pos =>
    .except (subst x e f) τ (upds.map λ (path, v) ↦ (path.map (Sum.map id (subst x e)), subst x e v)) @@ pos
  | .recordAccess f name, pos => .recordAccess (subst x e f) name @@ pos
  | .tuple es, pos => .tuple (es.map λ (τ, e') ↦ (τ, subst x e e')) @@ pos
  | .seq es τ, pos => .seq (subst x e <$> es) τ @@ pos
  | .if e₁ e₂ e₃ τ, pos => .if (subst x e e₁) (subst x e e₂) (subst x e e₃) τ @@ pos
  | .case bs other τ, pos =>
    .case (bs.map (Bifunctor.bimap (subst x e) (subst x e))) (subst x e <$> other) τ @@ pos
  | .nat n, pos => .nat n @@ pos
  | .str s, pos => .str s @@ pos
  | .true, pos => .true @@ pos
  | .false, pos => .false @@ pos

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
    -- The synthesized `EXCEPT` stands for the assignment whose right-hand side `rhs` is, so it
    -- takes that expression's span.
    let pos := posOf rhs
    Expression.subst r.name
      (.except (.var r.name r.baseType .binder @@ pos) r.baseType [(r.args, rhs)] @@ pos) e'

end ComputableTLAPlus

end
