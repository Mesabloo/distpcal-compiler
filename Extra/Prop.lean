theorem And.equiv {a b : Prop} : a ∧ b ↔ a ∧ (a → b) where
  mp := λ ⟨a, b⟩ => ⟨a, λ _ => b⟩
  mpr := λ ⟨a, f⟩ => ⟨a, f a⟩

@[simp]
theorem exists_exists_and_eq_and' {α β} {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∃ b, (∃ a, p a ∧ b = f a) ∧ q b) ↔ ∃ a, p a ∧ q (f a) :=
  ⟨fun ⟨_, ⟨a, ha, hab⟩, hb⟩ ↦ ⟨a, ha, hab.symm ▸ hb⟩, fun ⟨a, hp, hq⟩ ↦ ⟨f a, ⟨a, hp, rfl⟩, hq⟩⟩
