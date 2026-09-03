module

import CustomPrelude

/-! Tests for `linter.fugue.seqSolveBracket`. -/

/--
warning: `t <;> solve | s₁ | … | sₙ` with distinct scripts → `t <;> [s₁ | … | sₙ]`

Note: This linter can be disabled with `set_option linter.fugue.seqSolveBracket false`
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩ <;> solve | exact hp | exact hq

-- The pipe form is fine.
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩ <;> [exact hp | exact hq]
