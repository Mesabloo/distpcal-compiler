module

import CustomPrelude

/-! Tests for `linter.fugue.simpIntro`. -/

/--
warning: `intro …` then a closing `simp` → `simp_intro …`

Note: This linter can be disabled with `set_option linter.fugue.simpIntro false`
-/
#guard_msgs in
example : ∀ n : Nat, n + 0 = n := by
  intro n
  simp

-- `simp_intro` is fine.
#guard_msgs in
example : ∀ n : Nat, n + 0 = n := by
  simp_intro n [Nat.add_zero]

-- `intro` before a non-`simp` closer is fine.
#guard_msgs in
example : ∀ n : Nat, n = n := by
  intro n
  rfl
