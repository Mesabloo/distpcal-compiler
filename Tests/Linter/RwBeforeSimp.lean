module

import CustomPrelude

/-! Tests for `linter.fugue.rwBeforeSimp`. -/

/--
warning: merge this `rw` into the following `simp`, or use `rewrite`

Note: This linter can be disabled with `set_option linter.fugue.rwBeforeSimp false`
-/
#guard_msgs in
example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  rw [Nat.add_zero]
  simp [h]

-- `rw` not before a `simp`/`grind` is fine.
#guard_msgs in
example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  rw [Nat.add_zero, h]
