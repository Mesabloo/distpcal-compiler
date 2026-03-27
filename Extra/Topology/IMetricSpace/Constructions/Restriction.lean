import Extra.Topology.IMetricSpace
import CustomPrelude
import Extra.Topology.ClosedEmbedding

@[reducible]
def Restriction (α : Type _) (ε : unitInterval) (_ : ε > 0 := by bound) := α

noncomputable instance (priority := low) {α ε h} [inst : IMetricSpace α] : IMetricSpace (Restriction α ε h) where
  idist x y := ε * idist (x : α) (y : α)
  idist_self x := by
    rw [idist_self, MonoidWithZero.mul_zero]
  idist_comm x y := by
    rw [idist_comm]
  idist_triangle x y z := by
    repeat rw [Set.Icc.coe_mul]
    rw [← left_distrib]
    apply mul_le_mul (by rfl) (idist_triangle x y z)
    · grind only [= Set.mem_Icc]
    · grind only [= Set.mem_Icc]
  eq_of_idist_eq_zero x y h := by
    apply eq_of_idist_eq_zero
    rw [mul_eq_zero] at h
    obtain h|h := h
    · grind only
    · assumption
  toUniformSpace := inst.toUniformSpace
  uniformity_idist := by
    rw [inst.uniformity_idist, le_antisymm_iff, le_iInf_iff, le_iInf_iff]
    constructor
    · intros ε'
      rw [le_iInf_iff, Filter.le_principal_iff]
      intros ε'_pos
      refine Filter.mem_iInf_of_mem (ε' / ε) (Filter.mem_iInf_of_mem (div_pos ε'_pos h) ?_)
      rw [Filter.mem_principal, Set.setOf_subset_setOf]
      intros x h'
      rwa [lt_div_iff₀' h, ← Set.Icc.coe_mul] at h'
    · intros ε'
      rw [le_iInf_iff, Filter.le_principal_iff]
      intros ε'_pos
      refine Filter.mem_iInf_of_mem (ε' * ε) (Filter.mem_iInf_of_mem (mul_pos ε'_pos h) ?_)
      rw [Filter.mem_principal, Set.setOf_subset_setOf]
      intros x h'
      rwa [Set.Icc.coe_mul, mul_comm, mul_lt_mul_iff_left₀ ?_] at h'
      · rwa [gt_iff_lt, ← unitInterval.coe_pos] at h

instance {α ε h} [UniformSpace α] [CompleteSpace α] : CompleteSpace (Restriction α ε h) :=
  inferInstanceAs (CompleteSpace α)

abbrev Restriction.map {α β ε h} (f : α → β) : Restriction α ε h → Restriction β ε h := f

theorem Restriction.map_injective {α β ε h} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
  (hf : Function.Injective f) :
    Function.Injective (Restriction.map (ε := ε) (h := h) f) :=
  hf

theorem Restriction.map.isClosedEmbedding {α β ε h} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
  (hf : Topology.IsClosedEmbedding f) :
    Topology.IsClosedEmbedding (Restriction.map (ε := ε) (h := h) f) :=
  hf

macro_rules
| `(tactic| is_closed_embedding_step) =>
  `(tactic| guard_target =ₛ Topology.IsClosedEmbedding (Restriction.map ?_);
            apply Restriction.map.isClosedEmbedding)

theorem Restriction.map_isometry' {α β ε h} [IMetricSpace α] [IMetricSpace β] {f : α → β}
  (hf : ∀ x y, idist (f x) (f y) = idist x y) :
    ∀ x y, idist (@Restriction.map _ _ ε h f x) (Restriction.map f y) = idist x y :=
  hf

theorem Restriction.map_isometry {α β ε h} [IMetricSpace α] [IMetricSpace β] {f : α → β}
  (hf : Isometry f) :
    Isometry (@Restriction.map _ _ ε h f) :=
  hf

theorem Restriction.uniformContinuous_map {α β ε h} [IMetricSpace α] [IMetricSpace β] {f : α → β}
  (hf : UniformContinuous f) :
    UniformContinuous (@Restriction.map _ _ ε h f) :=
  hf
