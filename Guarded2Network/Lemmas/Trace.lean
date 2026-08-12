module

public import VerifiedCompiler.Denotational.Tactics
public import Core.NetworkPlusCal.Semantics.Lemmas

@[expose] public section

/-!
  This pass's trace relation: **equality**.

  `VerifiedCompiler/Trace.lean` keeps `Rτ` a parameter because a pass may relate source and target
  traces up to something weaker. `Guarded2Network` does not need that: reception is not an
  observable event (`Behavior` is `print | send`), the `.rx` thread is silent, and every `print`/
  `send` the source performs the target performs in the same place. So the two traces are equal,
  and `Rτ := Eq` — `Trace.instSeq`, at the `Stream'.Seq` alphabet the PlusCal semantics use.

  Registered `scoped` rather than as a global instance or a file-local `attribute`. A global
  instance would compete with whatever `Rτ` a *different* pass registers for the same trace type,
  which is why `Trace.instSeq` is a `def` in the first place; a `local instance` would have to be
  repeated in every proof file, since `attribute [local instance]` does not cross module
  boundaries. `scoped` gives exactly the wanted scope: any file working inside (or opening)
  `Guarded2Network` gets this pass's choice, and nothing else does.
-/

namespace Guarded2Network

/-- Traces are preserved exactly by this pass, so its trace relation is equality. -/
@[reducible] scoped instance instTrace {V : Type} :
    _root_.Trace (GuardedPlusCal.Trace V) (GuardedPlusCal.Trace V) := Trace.instSeq

/-- `Rτ` unfolded, for rewriting a framework-level obligation into the equation it actually is. -/
@[simp] theorem instTrace_Rτ {V : Type} :
    (instTrace (V := V)).Rτ = Eq := rfl

/-- The sequentially consistent prefix order at this pass's `Rτ`, in the form leaf goals meet it:
the source emitted `ε'`, and the target's `ε` extends it. -/
theorem scPrefix_iff {V : Type} {ε' ε : GuardedPlusCal.Trace V} :
    ε' ≼[(instTrace (V := V)).Rτ] ε ↔ ∃ δ, ε' * δ = ε := Iff.rfl

/-- The empty trace is a prefix of anything, which is what an abort *before* the target's first
observable event needs. -/
theorem one_scPrefix {V : Type} (ε : GuardedPlusCal.Trace V) :
    (1 : GuardedPlusCal.Trace V) ≼[(instTrace (V := V)).Rτ] ε :=
  ⟨ε, one_mul ε⟩

/-! ## The two ω-product obligations the divergence laws take as parameters

  `OmegaProd` fixes no laws, so the framework's divergence lemmas take what they need about infinite
  products as hypotheses. Both are trivial at this pass's choice and are discharged once here rather
  than at each call site.
-/

/-- `Rτ_omega`: two sequences related pointwise by *equality* are the same sequence, so their
products agree. -/
theorem rτ_omega {V : Type} (e' e : ℕ → GuardedPlusCal.Trace V)
    (h : ∀ i, (instTrace (V := V)).Rτ (e' i) (e i)) :
    (instTrace (V := V)).Rτ (OmegaProd.ωProd e') (OmegaProd.ωProd e) :=
  congrArg OmegaProd.ωProd (funext h)

/-- Deleting factors that are `1`, at this pass's trace type — `Stream'.Seq.ωProduct_comp_of_ones`,
which is where the work is. What a stuttering divergence refinement needs, since the source's run is
indexed by the target indices at which it actually moved. -/
theorem ωProd_comp {V : Type} (e : ℕ → GuardedPlusCal.Trace V) (n : ℕ → ℕ) (hmono : StrictMono n)
    (hone : ∀ i, (∀ j, n j ≠ i) → e i = 1) :
    OmegaProd.ωProd e = OmegaProd.ωProd (e ∘ n) :=
  Stream'.Seq.ωProduct_comp_of_ones hmono hone

end Guarded2Network

end
