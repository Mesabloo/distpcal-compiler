module

import CustomPrelude

/-! Tests for `linter.fugue.rflHaveSimp`. -/

/--
warning: `have e : _ := rfl` then `simp only [e, …]` → `change`

Note: This linter can be disabled with `set_option linter.fugue.rflHaveSimp false`
-/
#guard_msgs in
example (n : Nat) : n + 0 = n := by
  have e : n + 0 = n := rfl
  simp only [e]

-- `change` is fine.
#guard_msgs in
example (n : Nat) : n + 0 = n := by
  change n = n
  rfl
