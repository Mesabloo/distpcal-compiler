module

public import Guarded2Network.PlusCal
public import Guarded2Network.Lemmas.Monad
public import Guarded2Network.Lemmas.Seq
public import Guarded2Network.Lemmas.Trace
public import Guarded2Network.Lemmas.Relation
public import Guarded2Network.Lemmas.Statement
public import Guarded2Network.Lemmas.Reorder
public import Guarded2Network.Lemmas.Precondition
public import Guarded2Network.Lemmas.AtomicBranch
public import Core.NetworkPlusCal.Semantics.Lemmas
public import VerifiedCompiler
public import Std.Do.WP

@[expose] public section

/-!
  Proof support for `Guarded2Network`'s refinement proof (item 7, `.claude/plans/
  item7-refinement-proof.md`). Everything about the pass itself — the AST transformation, its own
  denotational semantics, the correctness statement — lives elsewhere; this file is where the
  reasoning-specific machinery accumulates.

  `Guarded2Network.PlusCal`'s pass runs monad-polymorphically, and a proof pins it to `G2NM`
  (`Guarded2Network/Lemmas/Monad.lean`, where the reasoning behind the choice is written down).
-/

/-- T6: registers `sem_side` (T1) as `mvcgen`'s automatic VC-discharge hook, so the cheap side
conditions `sem_red`-adjacent reasoning produces never surface as named verification conditions at
all — the one setting where a search tactic is *supposed* to run non-terminally, since `mvcgen`
only keeps what it closes. -/
macro_rules | `(tactic| mvcgen_trivial_extensible) => `(tactic| sem_side)

open Std.Do in
/-- Smoke test (plan §1 P4): `mvcgen` actually discharges a goal against `G2NM`, before anything
real is built on top of it. -/
example : ⦃⌜True⌝⦄ (do let _ ← MonadFresh.fresh; pure () : G2NM Unit) ⦃⇓_ => ⌜True⌝⦄ := by
  mvcgen

/-! # T1/T3 validation (plan §3)

  Two item-6 facts, re-proved with `sem_red`/`sem_side`/`gcongr` instead of the manual
  `rintro`/`exact` style item 6 used throughout `Semantics/Lemmas.lean` — the same content, in one
  line of tactic each rather than the several-line `⟨_, _, ..., rfl⟩` term or the `rw [Set.…]`
  chain the old style needs.
-/

open ComputableTLAPlus (ExprSemantics)

/-- Old style: `exact ⟨M, F, v, p, rfl, rfl, hv, hp, rfl⟩` — every field of `Statement.print`'s
`reducing` case named by hand. New style: `sem_red` picks the one matching intro lemma (`.print`)
off the goal's head constructor and leaves the existential body; `sem_side` supplies the witnesses
from `hv`/`hp` already in context via the `sem` rule set. -/
example {V} [ExprSemantics V] {M : ComputableTLAPlus.Memory V} {F v p} {e}
    (hv : M ⊢ e ⇒ v) (hp : M.lookup GuardedPlusCal.selfName = some p) :
    ⟨GuardedPlusCal.LocalState.running M F, Stream'.Seq.cons (.print p v) 1,
      GuardedPlusCal.LocalState.running M F⟩ ∈
      GuardedPlusCal.Statement.reducing (GuardedPlusCal.Statement.print e) := by
  sem_red
  sem_side

/-- Old style: `Relation.lcomp₁.mono h₁ h₂` invoked explicitly, or a `rw` chain through
`Relation.lcomp₁.right_union_eq_union`/`left_lcomp₂_eq`/etc. to massage both sides into a shape
`⊆` applies to directly. New style: `gcongr` finds the tagged `Relation.lcomp₁.mono`/`.lcomp₂.mono`
congruence lemma and reduces the goal to its two component inequalities on its own. -/
example {α β γ : Type} [Monoid β] {R R' : Set (α × β × γ)} {W W' : Set (γ × β)}
    (hR : R ≤ R') (hW : W ≤ W') : R ∘ᵣ₁ W ≤ R' ∘ᵣ₁ W' := by
  gcongr

end
