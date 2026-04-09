import Extra.Topology.IMetricSpace
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

open scoped Uniformity Filter UniformConvergence

universe u v

private lemma uniformFun_edist_le_one {α : Type u} {β : Type v} [PseudoIMetricSpace β]
    (f g : α →ᵤ β) : edist f g ≤ 1 := by
  rw [UniformFun.edist_def]
  apply iSup_le λ x ↦ ?_
  rw [edist_dist]
  exact ENNReal.ofReal_le_one.mpr unitInterval.le_one'

private lemma uniformFun_edist_ne_top {α : Type u} {β : Type v} [PseudoIMetricSpace β]
    (f g : α →ᵤ β) : edist f g ≠ ⊤ :=
  ne_of_lt ((uniformFun_edist_le_one f g).trans_lt ENNReal.one_lt_top)

noncomputable instance {α : Type u} {β : Type v} [PseudoIMetricSpace β] : PseudoIMetricSpace (α →ᵤ β) :=
  .of_emetric_space_of_dist_le_one uniformFun_edist_le_one

noncomputable instance {α : Type u} {β : Type v} [IMetricSpace β] : IMetricSpace (α →ᵤ β) :=
  .of_emetric_space_of_dist_le_one uniformFun_edist_le_one

noncomputable instance {α : Type u} {β : Type v} [PseudoIMetricSpace β] [CompleteSpace β] :
    CompleteSpace (α →ᵤ β) :=
  UniformFun.instCompleteSpace

theorem UniformFun.idist_eq {α : Type u} {β : Type v} [PseudoIMetricSpace β] {f g : α →ᵤ β} :
    idist f g = (edist f g).toReal :=
  rfl

lemma idist_bddAbove_real {α : Type u} {β : Type v} [PseudoIMetricSpace β] {f g : α →ᵤ β} :
    BddAbove (Set.range (λ x ↦ (idist (f x) (g x) : ℝ))) :=
  ⟨1, λ _ ⟨x, hx⟩ ↦ hx ▸ (idist (f x) (g x)).2.2⟩

lemma idist_cast_eq_iSup_real {α : Type u} {β : Type v} [PseudoIMetricSpace β] {f g : α →ᵤ β} :
    (idist f g : ℝ) = ⨆ x, (idist (f x) (g x) : ℝ) := by
  rw [UniformFun.idist_eq, UniformFun.edist_def, ENNReal.toReal_iSup]
  · rfl
  · intros x
    rw [edist_dist]
    exact ENNReal.ofReal_ne_top

theorem UniformFun.idist_eq_iSup {α : Type u} {β : Type v} [PseudoIMetricSpace β] {f g : α →ᵤ β} :
    idist f g = ⨆ x, idist (f x) (g x) := by
  apply le_antisymm
  · rw [le_iSup_iff]
    intro b hb
    rw [← Subtype.coe_le_coe, idist_cast_eq_iSup_real]
    by_cases hne : Nonempty α
    · exact ciSup_le λ x ↦ Subtype.coe_le_coe.mpr (hb x)
    · haveI : IsEmpty α := not_nonempty_iff.mp hne
      simp [Real.iSup_of_isEmpty, b.2.1]
  · apply iSup_le
    intro x
    rw [← Subtype.coe_le_coe, idist_cast_eq_iSup_real]
    exact le_ciSup idist_bddAbove_real x

attribute [-instance] UniformFun.instPseudoEMetricSpace UniformFun.instEMetricSpace
