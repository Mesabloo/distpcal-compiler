import Extra.Topology.IMetricSpace
import Extra.Topology.IMetricSpace.Constructions.Function
import Mathlib.Topology.EMetricSpace.Lipschitz

open scoped UniformConvergence

structure LipschitzMap (α β : Type _) [PseudoIMetricSpace α] [PseudoIMetricSpace β] (K : NNReal) where
  toFun : α →ᵤ β
  lipschitz : LipschitzWith K toFun

theorem LipschitzMap.toFun_injective {α β K} [PseudoIMetricSpace α] [PseudoIMetricSpace β] :
    Function.Injective (LipschitzMap.toFun (α := α) (β := β) (K := K)) := by
  rintro ⟨f, _⟩ ⟨g, _⟩ (_|_)
  rfl

notation:25 α:25 " →ₗ[" K:0 "] " β:26 => LipschitzMap α β K

instance {α β K} [PseudoIMetricSpace α] [PseudoIMetricSpace β] : CoeHead (α →ₗ[K] β) (α →ᵤ β) where
  coe := LipschitzMap.toFun

instance {α β K} [PseudoIMetricSpace α] [PseudoIMetricSpace β] : FunLike (α →ₗ[K] β) α β where
  coe := LipschitzMap.toFun
  coe_injective' := LipschitzMap.toFun_injective

noncomputable instance {α β K} [PseudoIMetricSpace α] [PseudoIMetricSpace β] : PseudoIMetricSpace (α →ₗ[K] β) :=
  .induced LipschitzMap.toFun inferInstance

noncomputable instance {α β K} [PseudoIMetricSpace α] [IMetricSpace β] : IMetricSpace (α →ₗ[K] β) :=
  .induced LipschitzMap.toFun LipschitzMap.toFun_injective inferInstance

instance {α β K} [PseudoIMetricSpace α] [IMetricSpace β] [CompleteSpace β] : CompleteSpace (α →ₗ[K] β) := by
  apply IsUniformInducing.completeSpace (f := LipschitzMap.toFun)
  · exact ⟨rfl⟩
  · have : Set.range (LipschitzMap.toFun (α := α) (β := β) (K := K)) = {f | LipschitzWith K f} := by
      ext f
      constructor
      · rintro ⟨⟨g, hg⟩, rfl⟩; exact hg
      · intro hf; exact ⟨⟨f, hf⟩, rfl⟩
    rw [this]
    exact (UniformFun.isClosed_setOf_lipschitzWith K).isComplete
