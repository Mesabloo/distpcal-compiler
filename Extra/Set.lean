import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image

namespace Set
  theorem mem_pair {α} {a b : α} {x : α} : x ∈ ({a, b} : Set α) ↔ x = a ∨ x = b := by
    constructor <;> exact id

  theorem mem_image_fst_of_mem {α β} {x : α} (y : β) {S : Set (α × β)} (h : (x, y) ∈ S) :
      x ∈ Prod.fst '' S := by
    grind

  theorem mem_image_snd_of_mem {α β} {x : α} (y : β) {S : Set (α × β)} (h : (x, y) ∈ S) :
      y ∈ Prod.snd '' S := by
    grind

  theorem exists_mem_of_mem_image_fst {α β} {x : α} {S : Set (α × β)} (h : x ∈ Prod.fst '' S) :
      ∃ y, (x, y) ∈ S := by
    grind only [= mem_image, cases eager Prod]

  theorem exists_mem_of_mem_image_snd {α β} {y : β} {S : Set (α × β)} (h : y ∈ Prod.snd '' S) :
      ∃ x, (x, y) ∈ S := by
    grind only [= mem_image, cases eager Prod]

  @[push_cast]
  theorem singleton_cast {α} {f : α → Sort _} {x y : α} (h : x = y) {a : f x} :
      h ▸ ({a} : Set _) = {h ▸ a} := by
    cases h
    rfl
end Set
