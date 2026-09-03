module

import CustomPrelude

/-! Tests for `linter.fugue.selectorFirst`. -/

/--
warning: blanket selector over a multi-branch `first`/`solve` — tailor a selector per alternative

Note: This linter can be disabled with `set_option linter.fugue.selectorFirst false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p ∧ p := by
  refine ⟨?_, ?_⟩
  all: first | rfl | assumption

-- A per-alternative selector is fine.
#guard_msgs in
example (p : Prop) (h : p) : p ∧ p := by
  refine ⟨?_, ?_⟩
  all: exact h
