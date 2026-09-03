module

import CustomPrelude

/-! Tests for `linter.fugue.setNotLet`. -/

/--
warning: `set x := …` leaves the goal unchanged — use `let`

Note: This linter can be disabled with `set_option linter.fugue.setNotLet false`
-/
#guard_msgs in
example : Nat := by
  set x := (2 : Nat) + 3
  exact x

-- `set` that abstracts an occurrence in the goal is fine.
#guard_msgs in
example : (2 : Nat) + 3 = 5 := by
  set x := (2 : Nat) + 3
  guard_target = x = 5
  rfl

-- `let` for a fresh definition is fine.
#guard_msgs in
example : Nat := by
  let x := (2 : Nat) + 3
  exact x
