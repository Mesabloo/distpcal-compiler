module

import CustomPrelude

/-! Tests for `linter.fugue.byAssumption`. -/

/--
warning: `by assumption` as a term argument → `‹_›`

Note: This linter can be disabled with `set_option linter.fugue.byAssumption false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := id (by assumption)

-- `‹_›` is fine.
#guard_msgs in
example (p : Prop) (h : p) : p := id ‹_›
