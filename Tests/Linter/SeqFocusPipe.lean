module

import CustomPrelude

/-! Tests for `linter.fugue.seqFocusPipe`. -/

/--
warning: `t <;> [a; b]` → `t <;> [a | b]` (the project's spelling)

Note: This linter can be disabled with `set_option linter.fugue.seqFocusPipe false`
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩ <;> [exact hp; exact hq]

-- The `|`-separated form is fine.
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩ <;> [exact hp | exact hq]
