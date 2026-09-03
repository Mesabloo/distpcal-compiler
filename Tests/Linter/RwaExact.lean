module

import CustomPrelude

/-! Tests for `linter.fugue.rwaExact`. -/

/--
warning: `rw … at k` then `exact k` → `rwa … at k`

Note: This linter can be disabled with `set_option linter.fugue.rwaExact false`
-/
#guard_msgs in
example (a b : Nat) (h : a = b) (k : a = 0) : b = 0 := by
  rw [h] at k
  exact k

-- `rwa` is fine.
#guard_msgs in
example (a b : Nat) (h : a = b) (k : a = 0) : b = 0 := by
  rwa [h] at k
