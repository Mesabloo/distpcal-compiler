import Extra.Topology.IMetricSpace
import CustomPrelude
import Extra.Topology.ClosedEmbedding

@[unbox]
structure Restriction (α : Type _) (ε : unitInterval) (h : ε > 0 := by bound) where
  val : α

instance {α ε h} : Coe α (Restriction α ε h) where
  coe x := { val := x }

@[ext]
theorem Restriction.ext_iff {α ε h} {x y : Restriction α ε h} (h : x.val = y.val) : x = y := by
  let ⟨_⟩ := x
  let ⟨_⟩ := y
  solve_by_elim

instance {α ε h} [Inhabited α] : Inhabited (Restriction α ε h) where
  default := { val := default }

instance {α ε h} [inst : Nonempty α] : Nonempty (Restriction α ε h) :=
  .intro { val := inst.some }

instance {α ε h} [inst : TopologicalSpace α] : TopologicalSpace (Restriction α ε h) :=
  inst.induced Restriction.val

instance Restriction.instUniformSpace {α ε h} [inst : UniformSpace α] : UniformSpace (Restriction α ε h) :=
  inst.comap Restriction.val

noncomputable instance {α ε h} [inst : IMetricSpace α] : IMetricSpace (Restriction α ε h) where
  idist x y := ε * idist x.val y.val
  idist_self x := by
    rw [idist_self, MonoidWithZero.mul_zero]
  idist_comm x y := by
    rw [idist_comm]
  idist_triangle x y z := by
    repeat rw [Set.Icc.coe_mul]
    rw [← left_distrib]
    apply mul_le_mul (by rfl) (idist_triangle x.val y.val z.val)
    · grind only [= Set.mem_Icc]
    · grind only [= Set.mem_Icc]
  eq_of_idist_eq_zero x y h := by
    ext : 1
    apply eq_of_idist_eq_zero
    rw [mul_eq_zero] at h
    obtain h|h := h
    · let ⟨_⟩ := x
      grind only
    · assumption
  toUniformSpace := Restriction.instUniformSpace
  uniformity_idist := by
    conv_lhs =>
      apply (IMetric.uniformity_basis_idist.comap (Prod.map Restriction.val Restriction.val)).eq_biInf
    rw [le_antisymm_iff, le_iInf_iff, le_iInf_iff]
    constructor
    · intros ε'
      rw [le_iInf_iff, Filter.le_principal_iff]
      intros ε'_pos
      refine Filter.mem_iInf_of_mem (ε' / ε) (Filter.mem_iInf_of_mem (div_pos ε'_pos h) ?_)
      rw [Filter.mem_principal, Set.preimage_setOf_eq, Set.setOf_subset_setOf]
      intros x h'
      rwa [lt_div_iff₀' h, ← Set.Icc.coe_mul] at h'
    · intros ε'
      rw [le_iInf_iff, Filter.le_principal_iff]
      intros ε'_pos
      refine Filter.mem_iInf_of_mem (ε' * ε) (Filter.mem_iInf_of_mem (mul_pos ε'_pos h) ?_)
      rw [Filter.mem_principal, Set.preimage_setOf_eq, Set.setOf_subset_setOf]
      intros x h'
      rwa [Set.Icc.coe_mul, mul_comm, mul_lt_mul_iff_left₀ ?_] at h'
      · rwa [gt_iff_lt, ← unitInterval.coe_pos] at h

instance {α ε h} [UniformSpace α] [CompleteSpace α] : CompleteSpace (Restriction α ε h) := by
  apply IsUniformInducing.completeSpace (f := Restriction.val)
  · solve_by_elim
  · grind only [isComplete_iff_clusterPt, isComplete_iff_ultrafilter, isComplete_iff_ultrafilter',
      cauchy_iff_exists_le_nhds, = Set.mem_range]

abbrev Restriction.map {α β ε h} (f : α → β) (x : Restriction α ε h) : Restriction β ε h where
  val := f x.val

theorem Restriction.map_id {α ε h} {x : Restriction α ε h} : Restriction.map id x = x :=
  rfl

theorem Restriction.map_map {α β γ ε h} {x : Restriction α ε h} {f : α → β} {g : β → γ} :
    Restriction.map g (Restriction.map f x) = Restriction.map (g ∘ f) x := by
  rfl

theorem Restriction.mk_comp_val_eq_id {α ε h} : @Restriction.mk α ε h ∘ Restriction.val = id := by
  rfl

theorem Restriction.val_uniformContinuous {α ε h} [UniformSpace α] : UniformContinuous (@Restriction.val α ε h) := by
  grind only [uniformContinuous_comap]

theorem Restriction.mk_uniformContinuous {α ε h} [UniformSpace α] : UniformContinuous (@Restriction.mk α ε h) := by
  exact uniformContinuous_comap' λ ⦃_⦄ h ↦ h

theorem Restriction.map_injective {α β ε h} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
  (hf : Function.Injective f) :
    Function.Injective (Restriction.map (ε := ε) (h := h) f) := by
  rintro ⟨x⟩ ⟨y⟩ h
  injection h with h
  ext : 1
  exact hf h

theorem Restriction.map.isClosedEmbedding {α β ε h} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
  (hf : Topology.IsClosedEmbedding f) :
    Topology.IsClosedEmbedding (Restriction.map (ε := ε) (h := h) f) := by
  -- FIXME: This is true but painful to prove
  admit

macro_rules
| `(tactic| is_closed_embedding_step) =>
  `(tactic| apply Restriction.map.isClosedEmbedding)

theorem Restriction.map_isometry' {α β ε h} [IMetricSpace α] [IMetricSpace β] {f : α → β}
  (hf : ∀ x y, idist (f x) (f y) = idist x y) :
    ∀ x y, idist (@Restriction.map _ _ ε h f x) (Restriction.map f y) = idist x y := by
  change ∀ (x y : Restriction α ε h), ε * idist (f x.val) (f y.val) = ε * idist x.val y.val
  simp [hf]

theorem Restriction.map_isometry {α β ε h} [IMetricSpace α] [IMetricSpace β] {f : α → β}
  (hf : Isometry f) :
    Isometry (@Restriction.map _ _ ε h f) := by
  apply Isometry.of_idist_eq
  apply Restriction.map_isometry'
  apply Isometry.to_idist_eq
  exact hf

theorem Restriction.uniformContinuous_map {α β ε h} [IMetricSpace α] [IMetricSpace β] {f : α → β}
  (hf : UniformContinuous f) :
    UniformContinuous (@Restriction.map _ _ ε h f) := by
  -- FIXME: This is true but painful to prove
  admit
