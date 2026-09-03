module

import CustomPrelude

/-! Tests for `linter.fugue.simpaUsing`. -/

/--
warning: `have h := e; simp … at h; exact h` → `simpa … using e`

Note: This linter can be disabled with `set_option linter.fugue.simpaUsing false`
-/
#guard_msgs in
example (a b : Nat) (hab : a + 0 = b) : a = b := by
  have h := hab
  simp only [Nat.add_zero] at h
  exact h

-- `simpa … using` is fine.
#guard_msgs in
example (a b : Nat) (hab : a + 0 = b) : a = b := by
  simpa only [Nat.add_zero] using hab
