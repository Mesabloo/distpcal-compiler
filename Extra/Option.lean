import CustomPrelude

namespace Option
  theorem isSome_iff_exists_some {α} {x : Option α} : x.isSome = true ↔ ∃ y, x = some y := by
    cases x <;> constructor
    · intros; contradiction
    · rintro ⟨_, _⟩; contradiction
    · exact isSome_iff_exists.mp
    · rintro ⟨_, _⟩
      rfl

  theorem seq_eq_some {α β} {x : β} {f : Option (α → β)} {g : Option α} : f <*> g = Option.some x ↔ ∃ h, f = .some h ∧ ∃ y, g = .some y ∧ h y = x := by
    change (do let f ← f; f <$> g) = Option.some x ↔ _
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_map, Option.map_eq_some_iff]
end Option
