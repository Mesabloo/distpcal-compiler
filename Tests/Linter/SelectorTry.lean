module

import CustomPrelude

/-! Tests for `linter.fugue.selectorTry`. -/

/--
warning: selector body is a bare `try` — hides which goals it closed; name the goals it applies to, or drop `try` and the selector if it closes them all

Note: This linter can be disabled with `set_option linter.fugue.selectorTry false`
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩
  all: try assumption

/--
warning: selector body is a bare `try` — hides which goals it closed; name the goals it applies to, or drop `try` and the selector if it closes them all

Note: This linter can be disabled with `set_option linter.fugue.selectorTry false`
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩
  1-2: try assumption

-- Naming the goals the tactic applies to is fine.
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩
  all: assumption

-- `try` outside a selector is not this linter's concern.
#guard_msgs in
example (p : Prop) (hp : p) : p := by
  try skip
  assumption
