module

import CustomPrelude

/-! Tests for `linter.fugue.renameI`. -/

/--
warning: never `rename_i` — use `next x y => …`, or name it where it is bound

Note: This linter can be disabled with `set_option linter.fugue.renameI false`
-/
#guard_msgs in
example (n : Nat) : n = n := by
  cases n
  · rfl
  · rename_i k
    rfl

/--
warning: never `expose_names` — name the hypotheses where they are bound

Note: This linter can be disabled with `set_option linter.fugue.renameI false`
-/
#guard_msgs in
example : True := by
  expose_names
  trivial

-- `next` is fine.
#guard_msgs in
example (n : Nat) : n = n := by
  cases n
  · rfl
  · next k => rfl
