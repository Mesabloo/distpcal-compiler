module

import CustomPrelude

/-! Tests for `linter.fugue.lambda`. -/

/--
warning: write `λ x ↦ y`, not `fun x => y`

Note: This linter can be disabled with `set_option linter.fugue.lambda false`
-/
#guard_msgs in
example : Nat → Nat := fun x => x

-- `λ` is fine.
#guard_msgs in
example : Nat → Nat := λ x ↦ x

-- Quotation interiors are exempt.
#guard_msgs in
open Lean in
run_cmd do
  let _ ← `(term| fun x => x)
  pure ()
