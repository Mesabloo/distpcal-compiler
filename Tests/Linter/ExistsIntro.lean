module

import CustomPrelude

/-! Tests for `linter.fugue.existsIntro`. -/

/--
warning: existential goal — `exists` (or `use`) the witnesses, not `refine ⟨…, ?_⟩`

Note: This linter can be disabled with `set_option linter.fugue.existsIntro false`
-/
#guard_msgs in
example : ∃ n : Nat, n = 0 := by
  refine ⟨0, ?_⟩
  rfl

-- Leading hole: no witness for `exists` to supply.
#guard_msgs in
example : ∃ n : Nat, n = 0 := by
  refine ⟨?_, ?_⟩
  · exact 0
  · rfl

-- Hole nested under `Or.inr` has no `exists` spelling.
#guard_msgs in
example : ∃ n : Nat, n = 0 ∨ n = 1 := by
  refine ⟨1, Or.inr ?_⟩
  rfl

-- Not an existential goal.
#guard_msgs in
example : True ∧ True := by
  refine ⟨trivial, ?_⟩
  trivial
