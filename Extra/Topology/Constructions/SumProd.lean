import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Constructions
import Extra.Topology.ClosedEmbedding
import Extra.Topology.UniformContinuousMap
import Extra.Topology.IMetricSpace.Constructions.Sum

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
end Topology

namespace Topology
  variable {W X Y Z} [UniformSpace W] [UniformSpace X] [UniformSpace Y] [UniformSpace Z]

theorem uniformContinuous_sum_dom {f : X ⊕ Y → Z} :
    UniformContinuous f ↔ UniformContinuous (f ∘ Sum.inl) ∧ UniformContinuous (f ∘ Sum.inr) := by
  iff_rintro hf ⟨hf_inl, hf_inr⟩
  · constructor
    · apply UniformContinuous.comp
      · exact hf
      · exact uniformContinuous_inl
    · apply UniformContinuous.comp
      · exact hf
      · exact uniformContinuous_inr
  · tauto

  theorem UniformContinuous.sumElim {f : W → X} {g : Y → X}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
      UniformContinuous (Sum.elim f g) := by
    rw [uniformContinuous_sum_dom]
    constructor
    · exact hf
    · exact hg

  theorem UniformContinuous.sumMap {f : W → X} {g : Y → Z}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
      UniformContinuous (Sum.map f g) := by
    apply UniformContinuous.sumElim
    · apply UniformContinuous.comp
      · exact uniformContinuous_inl
      · exact hf
    · apply UniformContinuous.comp
      · exact uniformContinuous_inr
      · exact hg
end Topology
