module

import CustomPrelude

/-! Tests for `linter.fugue.selectorParens`. -/

/--
warning: a selector already groups its block — drop the `( … )`

Note: This linter can be disabled with `set_option linter.fugue.selectorParens false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p ∧ p := by
  refine ⟨?_, ?_⟩
  all: (exact h)

-- The unparenthesised block is fine.
#guard_msgs in
example (p : Prop) (h : p) : p ∧ p := by
  refine ⟨?_, ?_⟩
  all: exact h
