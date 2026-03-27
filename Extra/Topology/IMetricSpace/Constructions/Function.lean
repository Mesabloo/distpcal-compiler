import Extra.Topology.IMetricSpace
import Extra.Topology.ClosedEmbedding

universe u v

noncomputable instance {α : Type u} {β : α → Type v} [Nonempty α] [∀ i, PseudoIMetricSpace (β i)] : PseudoIMetricSpace ((x : α) → β x) where
  idist f g := ⨆ x : α, idist (f x) (g x) -- uniform distance
  idist_self f := by
    conv_lhs => enter [1, x]; rw [idist_self]
    rw [iSup_const]
  idist_comm f g := by
    conv_lhs => enter [1, x]; rw [idist_comm]
  idist_triangle f g h := by
    admit
  toUniformSpace := Pi.uniformSpace β
  uniformity_idist := by
    admit

noncomputable instance {α : Type u} {β : α → Type v} [Nonempty α] [∀ i, IMetricSpace (β i)] : IMetricSpace ((x : α) → β x) where
  eq_of_idist_eq_zero {f g} h := by
    erw [iSup_eq_bot] at h
    replace h : ∀ (i : α), f i = g i := λ i ↦ eq_of_idist_eq_zero _ _ (h i)
    exact funext h

noncomputable instance {α : Type u} {β : Type v} [Nonempty α] [IMetricSpace β] : IMetricSpace (α → β) :=
  inferInstanceAs (IMetricSpace ((x : α) → β))

-- instance {α : Type u} {β : Type v} [UniformSpace β] : UniformSpace (α → β) :=
--   Pi.uniformSpace (λ _ ↦ β)

instance {α : Type u} {β : Type v} [UniformSpace β] [CompleteSpace β] : CompleteSpace (α → β) :=
  Pi.complete (λ _ ↦ β)

noncomputable instance {α β} [Nonempty α] [TopologicalSpace α] [IMetricSpace β] : IMetricSpace (α ↪c β) :=
  .induced ClosedEmbedding.toFun ClosedEmbedding.injective_toFun inferInstance
