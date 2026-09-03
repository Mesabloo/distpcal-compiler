module

import CustomPrelude

/-! Tests for `linter.fugue.inductionWith`. -/

/--
warning: `induction`/`fun_induction` without `with` — carry the cases in `with | … => …`

Note: This linter can be disabled with `set_option linter.fugue.inductionWith false`
-/
#guard_msgs in
example (n : Nat) : n = n := by
  induction n
  · rfl
  · rfl

-- `with` is fine.
#guard_msgs in
example (n : Nat) : n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rfl
