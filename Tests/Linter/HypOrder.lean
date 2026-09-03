module

import CustomPrelude

/-! Tests for `linter.fugue.hypOrder`. -/

/--
warning: introduced names are out of signature order — the binders run `a b c`

Note: This linter can be disabled with `set_option linter.fugue.hypOrder false`
-/
#guard_msgs in
example : ∀ (a b c : Nat), a + b + c = c + b + a := by
  intro a c b
  omega

-- Names in signature order are fine.
#guard_msgs in
example : ∀ (a b c : Nat), a + b + c = c + b + a := by
  intro a b c
  omega

-- Fresh names that do not match the binders are a free rename, not a reorder.
#guard_msgs in
example : ∀ (a b c : Nat), a + b + c = c + b + a := by
  intro x y z
  omega

-- `rintro` with the same reordering.
/--
warning: introduced names are out of signature order — the binders run `first second`

Note: This linter can be disabled with `set_option linter.fugue.hypOrder false`
-/
#guard_msgs in
example : ∀ (first second : Nat), first ≤ second ∨ second ≤ first := by
  rintro second first
  omega
