import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Basic
import Extra.Topology.ClosedEmbedding
import Extra.Topology.IMetricSpace
import Extra.Topology.IMetricSpace.Constructions.Function
import Mathlib.Topology.UniformSpace.Pi

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

protected theorem Isometry.piMap''.{u, v} {ι : Type u} {α β : ι → Type v} [Nonempty ι]
  [∀ i, PseudoIMetricSpace (α i)]
  [∀ i, PseudoIMetricSpace (β i)] (f : ∀ i, α i → β i)
  (hf : ∀ i x y, idist (f i x) (f i y) = idist x y) :
    ∀ x y, idist (Pi.map f x) (Pi.map f y) = idist x y := by
  intros g g'
  change ⨆ x, idist (Pi.map f g x) (Pi.map f g' x) = ⨆ x, idist (g x) (g' x)
  simp [Pi.map_apply]
  congr 1 with x
  specialize hf x (g x) (g' x)
  solve_by_elim

protected theorem Isometry.piMap'.{u, v} {ι : Type u} {α β : ι → Type v} [Nonempty ι]
  [∀ i, PseudoIMetricSpace (α i)]
  [∀ i, PseudoIMetricSpace (β i)] (f : ∀ i, α i → β i) (hf : ∀ i, Isometry (f i)) :
    Isometry (Pi.map f) := by
  apply Isometry.of_idist_eq
  apply Isometry.piMap'' _ λ i x y ↦ to_idist_eq (hf i) x y

theorem Pi.uniformContinuous_map_const {ι α β} {f : α → β} [UniformSpace α] [UniformSpace β]
  (hf : UniformContinuous f) :
    UniformContinuous (Pi.map λ _ : ι ↦ f) := by
  rw [uniformContinuous_pi]
  intro _
  apply UniformContinuous.comp
  · exact hf
  · apply uniformContinuous_proj
