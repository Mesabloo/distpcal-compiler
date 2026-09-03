module

import CustomPrelude

/-! Tests for `linter.fugue.obtainRfl`. -/

/--
warning: `have hh : a = b := p` + `rw [hh]` → `obtain rfl : a = b := p`

Note: This linter can be disabled with `set_option linter.fugue.obtainRfl false`
-/
#guard_msgs in
example (a b : Nat) (h : a = b) : a + 0 = b := by
  have hh : a = b := id h
  rw [hh]
  omega

-- `obtain rfl` is fine.
#guard_msgs in
example (a b : Nat) (h : a = b) : a = b := by
  obtain rfl : a = b := h
  rfl
