module

import CustomPrelude

/-! Tests for `linter.fugue.exactAbsurd`. -/

-- `by exact absurd …` also trips `byExact`; both warnings are correct here.
/--
warning: `exact absurd x y` — use the `absurd` tactic, `nomatch h`, or a `have` + `contradiction`

Note: This linter can be disabled with `set_option linter.fugue.exactAbsurd false`
---
warning: `by exact e` in term position → just `e`

Note: This linter can be disabled with `set_option linter.fugue.byExact false`
-/
#guard_msgs in
example (p : Prop) (h : p) (hn : ¬p) : False := by exact absurd h hn

-- The `absurd` tactic is fine.
#guard_msgs in
example (p : Prop) (h : p) (hn : ¬p) : False := by absurd h; exact hn
