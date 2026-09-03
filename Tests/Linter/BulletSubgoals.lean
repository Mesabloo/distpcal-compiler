module

import CustomPrelude

/-! Tests for `linter.fugue.bulletSubgoals`. -/

/--
warning: 2 goals open here, 1 left untouched — bullet each branch with `·`

Note: This linter can be disabled with `set_option linter.fugue.bulletSubgoals false`
-/
#guard_msgs in
example : True ∧ True := by
  refine ⟨?_, ?_⟩
  trivial
  trivial

-- Bulleted branches are fine.
#guard_msgs in
example : True ∧ True := by
  refine ⟨?_, ?_⟩
  · trivial
  · trivial

-- A combinator that is explicit about every goal is fine.
#guard_msgs in
example : True ∧ True := by
  constructor <;> trivial

-- The project's `all:` selector is deliberately over many goals.
#guard_msgs in
example : True ∧ True := by
  constructor
  all: trivial
