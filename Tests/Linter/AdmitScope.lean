module

import CustomPrelude

/-! Tests for `linter.fugue.admitScope`. -/

/--
warning: declaration uses `sorry`
---
warning: tactic-position `sorry` → `admit`

Note: This linter can be disabled with `set_option linter.fugue.admitScope false`
-/
#guard_msgs in
example : True := by sorry

-- Term-position `sorry` stays `sorry`.
/--
warning: declaration uses `sorry`
-/
#guard_msgs in
example : True := sorry
