module

import CustomPrelude

/-! Tests for `linter.fugue.byExact`. -/

/--
warning: `by exact e` in term position → just `e`

Note: This linter can be disabled with `set_option linter.fugue.byExact false`
-/
#guard_msgs in
example (h : True) : True := by exact h

/--
warning: `by classical exact e` — `e` elaborates without `classical`; hoist `classical` (`open Classical in` on the declaration, or above the branch that needs it), or drop it

Note: This linter can be disabled with `set_option linter.fugue.byExact false`
-/
#guard_msgs in
example (p : Prop) : p ∨ ¬p := by classical exact em p

-- A plain term is fine.
#guard_msgs in
example (h : True) : True := h

-- `by exact` where the term genuinely needs the tactic context stays.
#guard_msgs in
example (p : Prop) (h : Decidable p → True) : True := by classical exact h inferInstance
