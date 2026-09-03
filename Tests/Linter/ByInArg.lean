module

import CustomPrelude

/-! Tests for `linter.fugue.byInArg` (off by default — flip on for the test). -/

/--
warning: `(by …)` in argument position — a term if one exists, else `refine`/`apply` and `?_`

Note: This linter can be disabled with `set_option linter.fugue.byInArg false`
-/
#guard_msgs in
set_option linter.fugue.byInArg true in
example (a b : Nat) (h : a = b) : a = b := by
  refine Eq.trans (by rw [h]) rfl

-- Off by default.
#guard_msgs in
example (a b : Nat) (h : a = b) : a = b := by
  refine Eq.trans (by rw [h]) rfl
