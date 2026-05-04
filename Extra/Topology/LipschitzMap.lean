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

notation:25 α:26 " →ₗ[" K:0 "] " β:25 => LipschitzMap α β K

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

def LipschitzMap.comp {α β γ} [PseudoIMetricSpace α] [PseudoIMetricSpace β] [PseudoIMetricSpace γ] {K₁ K₂}
  (f : β →ₗ[K₂] γ) (g : α →ₗ[K₁] β) :
    α →ₗ[K₂ * K₁] γ where
  toFun := f ∘ g
  lipschitz := LipschitzWith.comp f.lipschitz g.lipschitz

theorem LipschitzMap.lipschitz_comp_right {α β γ} [PseudoIMetricSpace α] [PseudoIMetricSpace β] [PseudoIMetricSpace γ] {K₁ K₂} {f : γ →ₗ[K₂] β} :
    LipschitzWith K₂ (λ g : α →ₗ[K₁] γ ↦ f.comp g) := by
  apply LipschitzWith.of_idist_le λ g g' ↦ ?_
  erw [UniformFun.idist_eq_iSup, UniformFun.idist_eq_iSup]
  unfold LipschitzMap.comp
  dsimp

  apply unitInterval.coe_iSup_le
  · apply mul_nonneg
    · exact NNReal.zero_le_coe
    · apply unitInterval.nonneg
  · intros x
    trans
    · exact LipschitzWith.to_idist_le f.lipschitz (g x) (g' x)
    · apply mul_le_mul_of_nonneg
      · apply le_refl
      · rw [Subtype.coe_le_coe]
        apply le_iSup (f := λ x ↦ idist (g x) (g' x))
      · exact NNReal.zero_le_coe
      · apply unitInterval.nonneg

theorem LipschitzMap.lipschitz_comp_left {α β γ} [PseudoIMetricSpace α] [PseudoIMetricSpace β] [PseudoIMetricSpace γ] {K₁ K₂} :
    LipschitzWith 1 λ f : γ →ₗ[K₂] β ↦ {toFun := LipschitzMap.comp (α := α) (K₁ := K₁) f, lipschitz := LipschitzMap.lipschitz_comp_right : LipschitzMap _ _ _} := by
  apply LipschitzWith.of_idist_le λ f f' ↦ ?_
  erw [UniformFun.idist_eq_iSup, UniformFun.idist_eq_iSup]
  dsimp
  apply unitInterval.coe_iSup_le
  · apply mul_nonneg
    · apply zero_le_one
    · apply unitInterval.nonneg
  · intro g
    erw [UniformFun.idist_eq_iSup]
    apply unitInterval.coe_iSup_le
    · apply mul_nonneg
      · apply zero_le_one
      · apply unitInterval.nonneg
    · intro x
      dsimp [LipschitzMap.comp]

      trans (⨆ x, idist (f x) (f' x)).val
      · rw [Subtype.coe_le_coe]
        apply le_iSup (f := λ x ↦ idist (f x) (f' x))
      · erw [one_mul]
        rfl

theorem LipschitzMap.lipschitz_comp_left' {α β γ} [PseudoIMetricSpace α] [PseudoIMetricSpace β] [PseudoIMetricSpace γ] {K₁ K₂} {g : α →ₗ[K₁] γ} :
    LipschitzWith 1 λ f : γ →ₗ[K₂] β ↦ f.comp g := by
  apply LipschitzWith.of_idist_le λ f f' ↦ ?_
  erw [UniformFun.idist_eq_iSup, UniformFun.idist_eq_iSup]

  trans (⨆ x, idist (f x) (f' x)).val
  · rw [Subtype.coe_le_coe]
    apply iSup_le λ x ↦ ?_
    apply le_iSup (f := λ x ↦ idist (f x) (f' x))
  · erw [one_mul]
    rfl

theorem LipschitzMap.lipschitz_apply {β γ δ} [IMetricSpace β] [IMetricSpace γ] [IMetricSpace δ] {K₁ K₂} {f : β →ᵤ γ} (hf : LipschitzWith K₁ f) :
    LipschitzWith 1 λ g : (β →ₗ[K₁] γ) →ₗ[K₂] δ ↦ g { toFun := f, lipschitz := hf } := by
  apply LipschitzWith.of_idist_le λ g g' ↦ ?_
  erw [one_mul, Subtype.coe_le_coe, UniformFun.idist_eq_iSup]
  apply le_iSup (f := λ x ↦ idist (g x) (g' x))
