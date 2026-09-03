module

import CustomPrelude

/-! Tests for `linter.fugue.selectorOneGoal`. -/

/--
warning: `all:` over a single goal — use a `·` bullet

Note: This linter can be disabled with `set_option linter.fugue.selectorOneGoal false`
-/
#guard_msgs in
example : True := by
  all: trivial

/--
warning: `all_goals` over a single goal — use a `·` bullet

Note: This linter can be disabled with `set_option linter.fugue.selectorOneGoal false`
-/
#guard_msgs in
set_option linter.fugue.goalSelector false in
example : True := by
  all_goals trivial

-- `all:` genuinely over several goals is fine.
#guard_msgs in
example : True ∧ True := by
  constructor
  all: trivial
