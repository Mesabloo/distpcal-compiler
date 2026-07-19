module

public import Typed2Computable.Errors
public import Core.TypedTLAPlus.Syntax
public import Core.ComputableTLAPlus.Syntax

public section

/-!
  `TypedTLAPlus.Expression.toComputable` — translates a checked TLA⁺ expression into its
  computable fragment (`Core/ComputableTLAPlus/Syntax.lean`'s module doc has the full
  per-constructor rationale). Structurally mirrors `TypedTLAPlus.Expression.traverse`'s own
  recursion (`Core/TypedTLAPlus/Syntax.lean:162-197`), reattaching source positions the same way
  (`@@ pos`) — total on every constructor `ComputableTLAPlus.Expression` keeps, throwing
  `ComputableError.notComputable` on `fnSet`/`recordSet`, and `.internalInvariantViolated` on
  whatever else shouldn't be reachable here at all (an unbounded quantifier domain, a bare
  temporal/action construct, a pending `mvar` coercion) — see `Typed2Computable/Errors.lean`'s
  own doc for why these stay one defense-in-depth case rather than a dedicated error each.

  `τ`/`Origin` fields pass through unchanged: `ComputableTLAPlus.Typ`/`.Origin` are literal
  reuses of `TypedTLAPlus.Typ`/`.Origin` (`Core/ComputableTLAPlus/Syntax.lean`), not a second
  copy, so there's nothing to convert.
-/

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty ComputableError m]

/-- See the module doc above. `partial`: structural recursion isn't visibly decreasing to Lean
here, same reason `Expression.map`/`.traverse` are `partial` (nested `List`/`Option` occurrences
of `Expression`). -/
partial def TypedTLAPlus.Expression.toComputable :
    TypedTLAPlus.Expression TypedTLAPlus.Typ → m (ComputableTLAPlus.Expression ComputableTLAPlus.Typ) :=
  λ e ↦ match_source e with
  | .var v τ o, pos => pure (.var v τ o @@ pos)
  | .nat n, pos => pure (.nat n @@ pos)
  | .str s, pos => pure (.str s @@ pos)
  | .true, pos => pure (.true @@ pos)
  | .false, pos => pure (.false @@ pos)
  | .opCall f es, pos => (.opCall · · @@ pos) <$> f.toComputable <*> es.mapM Expression.toComputable
  | .forall x ann dom body, pos => match dom with
    | none => throw (.internalInvariantViolated pos
        "an unbounded ∀ domain — WellFormedness/Restrictions.lean's check 3 already bans this transitively-reachable-from-the-algorithm")
    | some d => (.forall x ann · · @@ pos) <$> d.toComputable <*> body.toComputable
  | .exists x ann dom body, pos => match dom with
    | none => throw (.internalInvariantViolated pos
        "an unbounded ∃ domain — WellFormedness/Restrictions.lean's check 3 already bans this transitively-reachable-from-the-algorithm")
    | some d => (.exists x ann · · @@ pos) <$> d.toComputable <*> body.toComputable
  | .fforall .., pos => throw (.internalInvariantViolated pos
      "a bare \\AA (temporal universal quantification) — already banned transitively-reachable-from-the-algorithm by WellFormedness/Restrictions.lean's check 3")
  | .eexists .., pos => throw (.internalInvariantViolated pos
      "a bare \\EE (temporal existential quantification) — already banned transitively-reachable-from-the-algorithm by WellFormedness/Restrictions.lean's check 3")
  | .choose x ann dom body, pos => match dom with
    | none => throw (.internalInvariantViolated pos
        "an unbounded CHOOSE domain — WellFormedness/Restrictions.lean's check 3 already bans this transitively-reachable-from-the-algorithm")
    | some d => (.choose x ann · · @@ pos) <$> d.toComputable <*> body.toComputable
  | .set es τ, pos => (.set · τ @@ pos) <$> es.mapM Expression.toComputable
  | .collect x ann dom body, pos => (.collect x ann · · @@ pos) <$> dom.toComputable <*> body.toComputable
  | .map' body x ann cod dom, pos =>
    (.map' · x ann cod · @@ pos) <$> body.toComputable <*> dom.toComputable
  | .fnCall f fnTyp idx, pos =>
    (.fnCall · fnTyp · @@ pos) <$> f.toComputable <*> idx.toComputable
  | .fn x ann cod dom body, pos =>
    (.fn x ann cod · · @@ pos) <$> dom.toComputable <*> body.toComputable
  | .fnSet .., pos => throw (.notComputable pos .fnSet)
  | .record fs, pos => (.record · @@ pos) <$> fs.mapM λ (τ, name, e) ↦ (τ, name, ·) <$> e.toComputable
  | .recordSet .., pos => throw (.notComputable pos .recordSet)
  | .except e τ upds, pos =>
    (.except · τ · @@ pos) <$> e.toComputable <*> upds.mapM λ (path, newVal) ↦ do
      let path' ← path.mapM λ
        | .inl s => pure (Sum.inl s)
        | .inr idx => Sum.inr <$> idx.toComputable
      let newVal' ← newVal.toComputable
      pure (path', newVal')
  | .recordAccess e v, pos => (.recordAccess · v @@ pos) <$> e.toComputable
  | .tuple es, pos => (.tuple · @@ pos) <$> es.mapM λ (τ, e) ↦ (τ, ·) <$> e.toComputable
  | .seq es τ, pos => (.seq · τ @@ pos) <$> es.mapM Expression.toComputable
  | .if e₁ e₂ e₃ τ, pos =>
    (.if · · · τ @@ pos) <$> e₁.toComputable <*> e₂.toComputable <*> e₃.toComputable
  | .case branches other τ, pos =>
    (.case · · τ @@ pos) <$> branches.mapM (λ (p, e) ↦ Prod.mk <$> p.toComputable <*> e.toComputable)
      <*> other.mapM Expression.toComputable
  | .stutter .., pos => throw (.internalInvariantViolated pos
      "a bare [A]_e (stuttering-allowed action) — already banned transitively-reachable-from-the-algorithm by WellFormedness/Restrictions.lean's check 3")
  | .mvar _ _, pos => throw (.internalInvariantViolated pos
      "a pending coercion placeholder (mvar) — every mvar node is substituted away before the type checker's own output is ever handed to a caller (Core/TypedTLAPlus/Syntax.lean's own guarantee)")

end
