module

import CustomPrelude

/-! Tests for `linter.fugue.exactBy`. -/

/--
warning: `exact by …` — drop the `exact by` and run the tactics directly

Note: This linter can be disabled with `set_option linter.fugue.exactBy false`
-/
#guard_msgs in
example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  rw [Nat.add_zero]
  exact by simp [h]

-- Running the tactic directly is fine.
#guard_msgs in
example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  rw [Nat.add_zero]
  omega
