module

import CustomPrelude

/-! Tests for `linter.fugue.blockLayout`. -/

-- Correct: opening `(` ends its line, first tactic on the next, `)` alone and dedented.
#guard_msgs in
example (a : Nat) : a = a ∧ a = a := by
  (
    constructor
    · rfl
    · rfl
  )

/--
warning: first tactic shares the opening `(` line — put it on the next line

Note: This linter can be disabled with `set_option linter.fugue.blockLayout false`
-/
#guard_msgs in
example (a : Nat) : a = a ∧ a = a := by
  (constructor
   · rfl
   · rfl
  )

/--
warning: closing `)` is not alone on its line, dedented to column 2

Note: This linter can be disabled with `set_option linter.fugue.blockLayout false`
-/
#guard_msgs in
example (a : Nat) : a = a ∧ a = a := by
  (
    constructor
    · rfl
    · rfl)

-- A `(a; b)` one-liner is left alone even when the argument list makes it wrap.
#guard_msgs in
example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  (rw [Nat.add_zero]; omega)
