module

import CustomPrelude

/-! Tests for `linter.fugue.byClassical`. -/

/--
warning: put `by classical` on one line

Note: This linter can be disabled with `set_option linter.fugue.byClassical false`
-/
#guard_msgs in
example : True := by
  classical
  trivial

-- One line is fine.
#guard_msgs in
example : True := by classical
                     trivial
