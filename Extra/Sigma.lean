import Mathlib.Data.Sigma.Basic
import CustomPrelude

theorem Sigma.map_id_id {α} {β : α → Type _} : Sigma.map (α₁ := α) (β₁ := β) id (λ _ ↦ id) = id := by
  rfl

theorem Sigma.map_map {α₁ α₂ α₃} {β₁ β₂ β₃ : _ → Type _} {f₁ : α₁ → α₂} {f₂ : α₂ → α₃}
  {g₁ : (i : α₁) → β₁ i → β₂ (f₁ i)} {g₂ : (i : α₂) → β₂ i → β₃ (f₂ i)} {x : Σ x : α₁, β₁ x} :
    Sigma.map f₂ g₂ (Sigma.map f₁ g₁ x) = Sigma.map (f₂ ∘ f₁) (λ i ↦ g₂ (f₁ i) ∘ g₁ i) x := by
  rfl
