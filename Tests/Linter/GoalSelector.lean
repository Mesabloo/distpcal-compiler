module

import CustomPrelude

/-! Tests for `linter.fugue.goalSelector`. -/

/--
warning: `all_goals tac` → `all: tac`

Note: This linter can be disabled with `set_option linter.fugue.goalSelector false`
-/
#guard_msgs in
set_option linter.fugue.selectorOneGoal false in
example (p q : Prop) (h : p) : p ∨ q := by
  refine Or.inl ?_
  all_goals exact h

/--
warning: `on_goal n => tac` → `n: tac`

Note: This linter can be disabled with `set_option linter.fugue.goalSelector false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  on_goal 1 => exact h

/--
warning: `any_goals` is useless — drop it, or `all: tac` if a selector is meant

Note: This linter can be disabled with `set_option linter.fugue.goalSelector false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  any_goals exact h

-- `all:` is fine.
#guard_msgs in
set_option linter.fugue.selectorOneGoal false in
example (p q : Prop) (h : p) : p ∨ q := by
  refine Or.inl ?_
  all: exact h
