module

import CustomPrelude

/-! Tests for `linter.fugue.rwShow`. -/

/--
warning: no `rw [show … by …]` — state it as a `have` and rewrite with that

Note: This linter can be disabled with `set_option linter.fugue.rwShow false`
-/
#guard_msgs in
example (a b : Nat) (h : a = b) : a = b := by
  rw [show a = b by exact h]

-- A plain rewrite list is fine.
#guard_msgs in
example (a b : Nat) (h : a = b) : b + 0 = a := by
  rw [Nat.add_zero, h]
