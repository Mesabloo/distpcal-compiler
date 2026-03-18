import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Basic
import Extra.Topology.ClosedEmbedding

lemma Set.range_const' {α β} [Nonempty α] {v : β} : Set.range (Function.const α v) = {v} := by
  unfold Set.range
  grind only [usr mem_setOf_eq, = mem_singleton_iff]

theorem Topology.IsClosedEmbedding.const {α β} [Nonempty α] [TopologicalSpace α] [TopologicalSpace β] [Subsingleton α] [T1Space β] {v : β} :
    IsClosedEmbedding (Function.const α v) where
  eq_induced := of_decide_eq_true rfl
  injective := Function.injective_of_subsingleton _
  isClosed_range := by grind only [Set.range_const', isClosed_singleton]

theorem Topology.IsClosedEmbedding.const' {α β} [Nonempty α] [TopologicalSpace α] [TopologicalSpace β] [Subsingleton α] [T1Space β] {v : β} :
    IsClosedEmbedding (λ _ : α ↦ v) :=
  Topology.IsClosedEmbedding.const

macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| apply Topology.IsClosedEmbedding.const)
macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| apply Topology.IsClosedEmbedding.const')
