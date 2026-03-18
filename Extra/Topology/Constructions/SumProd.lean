import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Constructions
import Extra.Topology.ClosedEmbedding.Tactic

namespace Topology
  variable {W X Y Z} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

  theorem IsClosedEmbedding.prodMap {f : W → X} {g : Y → Z} (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
      IsClosedEmbedding (Prod.map f g) where
    eq_induced := (hf.toIsEmbedding.prodMap hg.toIsEmbedding).eq_induced
    injective := by
      apply Function.Injective.prodMap
      · exact hf.injective
      · exact hg.injective
    isClosed_range := by
      rw [Set.range_prodMap]
      exact hf.isClosed_range.prod hg.isClosed_range

  theorem IsClosedEmbedding.sumMap {f : W → X} {g : Y → Z} (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
      IsClosedEmbedding (Sum.map f g) := by
    apply IsClosedEmbedding.sumElim
    · apply Topology.IsClosedEmbedding.comp
      · exact Topology.IsClosedEmbedding.inl
      · assumption
    · apply Topology.IsClosedEmbedding.comp
      · exact Topology.IsClosedEmbedding.inr
      · assumption
    · apply Function.Injective.sumElim
      · apply Function.Injective.comp
        · exact Sum.inl_injective
        · exact hf.injective
      · apply Function.Injective.comp
        · exact Sum.inr_injective
        · exact hg.injective
      · rintro w y (_|_)

  macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| exact IsClosedEmbedding.id)
  macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| refine IsClosedEmbedding.piMap λ _ ↦ ?_)
  macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| apply IsClosedEmbedding.prodMap)
  macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| apply IsClosedEmbedding.sumElim)
  macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| apply IsClosedEmbedding.sumMap)
