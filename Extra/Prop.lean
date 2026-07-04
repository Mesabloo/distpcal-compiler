theorem And.equiv {a b : Prop} : a ∧ b ↔ a ∧ (a → b) where
  mp := λ ⟨a, b⟩ => ⟨a, λ _ => b⟩
  mpr := λ ⟨a, f⟩ => ⟨a, f a⟩
