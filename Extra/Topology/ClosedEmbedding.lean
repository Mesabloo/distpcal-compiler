import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic
import Extra.Topology.ClosedEmbedding.Tactic

structure ClosedEmbedding (α β) [TopologicalSpace α] [TopologicalSpace β] where
  toFun : α → β
  isClosedEmbedding : Topology.IsClosedEmbedding toFun := by first | sorry_if_sorry | is_closed_embedding; done
infixr:25 " ↪c " => ClosedEmbedding

macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| exact ClosedEmbedding.isClosedEmbedding _)

instance {α β} [TopologicalSpace α] [TopologicalSpace β] : Coe (ClosedEmbedding α β) (α → β) :=
  ⟨ClosedEmbedding.toFun⟩

theorem ClosedEmbedding.injective_toFun {α β} [TopologicalSpace α] [TopologicalSpace β] :
    Function.Injective (ClosedEmbedding.toFun (α := α) (β := β)) := by
  rintro ⟨⟩ ⟨⟩ rfl
  rfl
