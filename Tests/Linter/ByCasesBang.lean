module

import CustomPrelude

/-! Tests for `linter.fugue.byCasesBang`. -/

-- `push_neg` itself is deprecated upstream; `substring` keeps this test to the linter's own line.
/--
warning: `by_cases hp` then `push_neg at hp` — use `by_cases! hp`
-/
#guard_msgs (substring := true) in
example (n : Nat) : True := by
  by_cases hp : ∀ m, m = n
  · trivial
  · push_neg at hp
    trivial

-- The `!` form is fine.
#guard_msgs in
example (n : Nat) : True := by
  by_cases! hp : ∀ m, m = n
  · trivial
  · trivial
