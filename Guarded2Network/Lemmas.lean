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
public import Guarded2Network.Lemmas.Blocking
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

open Std.Do in
/-- Smoke test: `mvcgen` discharges a goal stated against `G2NM`. -/
example : ⦃⌜True⌝⦄ (do let _ ← MonadFresh.fresh; pure () : G2NM Unit) ⦃⇓_ => ⌜True⌝⦄ := by
  mvcgen

/-! # Tactic validation

  A check that `gcongr` fires on the goal shape it exists for.
-/

/-- `gcongr` finds the tagged `Relation.lcomp₁.mono`/`.lcomp₂.mono` congruence lemma and reduces
the goal to its two component inequalities on its own. -/
example {α β γ : Type} [Monoid β] {R R' : Set (α × β × γ)} {W W' : Set (γ × β)}
    (hR : R ≤ R') (hW : W ≤ W') : R ∘ᵣ₁ W ≤ R' ∘ᵣ₁ W' := by
  gcongr

end
