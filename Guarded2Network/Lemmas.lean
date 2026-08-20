module

public import Guarded2Network.PlusCal
public import Guarded2Network.Lemmas.Monad
public import Guarded2Network.Lemmas.Seq
public import Guarded2Network.Lemmas.Trace
public import Guarded2Network.Lemmas.Relation
public import Guarded2Network.Lemmas.Rx
public import Guarded2Network.Lemmas.Statement
public import Guarded2Network.Lemmas.Locality
public import Guarded2Network.Lemmas.Reorder
public import Guarded2Network.Lemmas.Precondition
public import Guarded2Network.Lemmas.AtomicBranch
public import Guarded2Network.Lemmas.AtomicBlock
public import Guarded2Network.Lemmas.Thread
public import Guarded2Network.Lemmas.Process
public import Guarded2Network.Lemmas.Algorithm
public import Guarded2Network.Lemmas.Correctness
public import Core.NetworkPlusCal.Semantics.Lemmas
public import VerifiedCompiler
public import Std.Do.WP

@[expose] public section

/-!
  Proof support for `Guarded2Network`'s refinement proof. Everything about the pass itself — the
  AST transformation, its own denotational semantics, the correctness statement — lives elsewhere;
  this file is where the reasoning-specific machinery accumulates.

  `Guarded2Network.PlusCal`'s pass runs monad-polymorphically, and a proof pins it to `G2NM`
  (`Guarded2Network.Lemmas.Monad`, where the reasoning behind the choice is written down).
-/

/-- Registers `sem_side` as `mvcgen`'s automatic VC-discharge hook, so the cheap side
conditions `sem_red`-adjacent reasoning produces never surface as named verification conditions at
all — the one setting where a search tactic is *supposed* to run non-terminally, since `mvcgen`
only keeps what it closes. -/
macro_rules | `(tactic| mvcgen_trivial_extensible) => `(tactic| sem_side)

open Std.Do in
/-- Smoke test: `mvcgen` discharges a goal stated against `G2NM`. -/
example : ⦃⌜True⌝⦄ (do let _ ← MonadFresh.fresh; pure () : G2NM Unit) ⦃⇓_ => ⌜True⌝⦄ := by
  mvcgen

/-! # Tactic validation

  Two facts about the semantics, each proved in one line of tactic: a check that `sem_red`,
  `sem_side` and `gcongr` fire on the goal shapes they exist for.
-/

open ComputableTLAPlus (ExprSemantics)

/-- `sem_red` picks the one matching intro lemma (`.print`) off the goal's head constructor and
leaves the existential body; `sem_side` supplies the witnesses from `hv`/`hp` already in context,
via the `sem` rule set. -/
example {V} [ExprSemantics V] {M : ComputableTLAPlus.Memory V} {F v p} {e}
    (hv : M ⊢ e ⇒ v) (hp : M.lookup GuardedPlusCal.selfName = some p) :
    ⟨(M, F, .none), Stream'.Seq.cons (.print p v) 1, (M, F, .none)⟩ ∈
      GuardedPlusCal.Statement.reducing (GuardedPlusCal.Statement.print e) := by
  sem_red
  sem_side

/-- `gcongr` finds the tagged `Relation.lcomp₁.mono`/`.lcomp₂.mono` congruence lemma and reduces
the goal to its two component inequalities on its own. -/
example {α β γ : Type} [Monoid β] {R R' : Set (α × β × γ)} {W W' : Set (γ × β)}
    (hR : R ≤ R') (hW : W ≤ W') : R ∘ᵣ₁ W ≤ R' ∘ᵣ₁ W' := by
  gcongr

end
