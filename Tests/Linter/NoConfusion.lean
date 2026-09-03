module

import CustomPrelude

/-! Tests for `linter.fugue.noConfusion`. -/

/--
warning: use `contradiction`, not `noConfusion` — `noConfusion` needs its implicits to line up

Note: This linter can be disabled with `set_option linter.fugue.noConfusion false`
-/
#guard_msgs in
example (h : (0 : Nat) = 1) : False := Nat.noConfusion h

-- `contradiction` is fine.
#guard_msgs in
example (h : (0 : Nat) = 1) : False := by contradiction
