module

import CustomPrelude

/-! Tests for `linter.fugue.haveBareName`. -/

/--
warning: `have x : Y := <bare name>` — `change Y at z` for a hypothesis, or inline a global at its use

Note: This linter can be disabled with `set_option linter.fugue.haveBareName false`
-/
#guard_msgs in
example (q : True) : True := by
  have h : True := q
  exact h

-- `have` without a type ascription is fine.
#guard_msgs in
example (q : True) : True := by
  have h := q
  exact h
