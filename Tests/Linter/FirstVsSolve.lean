module

import CustomPrelude

/-! Tests for `linter.fugue.firstVsSolve`. -/

/--
warning: terminal `first | …` closes the goal → `solve | …`

Note: This linter can be disabled with `set_option linter.fugue.firstVsSolve false`
-/
#guard_msgs in
example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  simp only [Nat.add_zero]
  first
  | rfl
  | exact h

-- `solve` is fine.
#guard_msgs in
example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  simp only [Nat.add_zero]
  solve
  | rfl
  | exact h
