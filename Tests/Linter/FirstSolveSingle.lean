module

import CustomPrelude

/-! Tests for `linter.fugue.firstSolveSingle`. -/

/--
warning: `first | t` is just `t`

Note: This linter can be disabled with `set_option linter.fugue.firstSolveSingle false`
-/
#guard_msgs in
example : True := by first | trivial

/--
warning: `solve | t` is just `t`

Note: This linter can be disabled with `set_option linter.fugue.firstSolveSingle false`
-/
#guard_msgs in
example : True := by solve | trivial

-- Two or more alternatives is fine.
#guard_msgs in
example : True := by first | done | trivial
