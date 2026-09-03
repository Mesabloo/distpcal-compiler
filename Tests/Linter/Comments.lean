module

import CustomPrelude

/-! Tests for `linter.fugue.comments`. -/

/--
warning: plan/task reference in a comment — state the fact, not the document

Note: This linter can be disabled with `set_option linter.fugue.comments false`
-/
#guard_msgs in
def planRef : Nat :=
  -- see PLAN.md for the rationale
  0

/--
warning: plan/task reference in a comment — state the fact, not the document

Note: This linter can be disabled with `set_option linter.fugue.comments false`
-/
#guard_msgs in
def sectionRef : Nat :=
  -- per §9.2 the binder opens
  0

/--
warning: paper citation in a comment — record it in reference/SPEC_MAP.md

Note: This linter can be disabled with `set_option linter.fugue.comments false`
-/
#guard_msgs in
def paperRef : Nat :=
  -- Definition 3.2 of the thesis
  0

/--
warning: prior-art comparison — state the current invariant, not what it replaced

Note: This linter can be disabled with `set_option linter.fugue.comments false`
-/
#guard_msgs in
def priorArt : Nat :=
  -- the earlier design threaded a monad here
  0

/--
warning: line-numbered cross-reference — name the declaration, a line number rots

Note: This linter can be disabled with `set_option linter.fugue.comments false`
-/
#guard_msgs in
def lineRef : Nat :=
  -- mirrors Subst.lean:412
  0

/--
warning: bare separator comment — delete it, or make it a `/-! … -/` header

Note: This linter can be disabled with `set_option linter.fugue.comments false`
-/
#guard_msgs in
def bareSep : Nat :=
  --------------------
  0

/--
warning: subjectless `TODO` — write `TODO(subject): what is owed`

Note: This linter can be disabled with `set_option linter.fugue.comments false`
-/
#guard_msgs in
def todo : Nat :=
  -- TODO handle the empty case
  0

/--
warning: commented-out code — delete it, git has it

Note: This linter can be disabled with `set_option linter.fugue.comments false`
-/
#guard_msgs in
def commentedCode : Nat :=
  -- import Foo.Bar
  0

-- A docstring that says what the declaration is draws no warning.
#guard_msgs in
/-- The answer to everything. -/
def clean : Nat := 42

-- `TODO(subject):` is the sanctioned form.
#guard_msgs in
def okTodo : Nat :=
  -- TODO(subst): open the binder here
  0

/-! ### The `soft` sub-checks — off unless `linter.fugue.comments.soft` is set -/

-- Status prose is silent by default.
#guard_msgs in
def statusProseDefault : Nat :=
  -- not yet threaded through the loop
  0

/--
warning: status prose in a comment — read as if the current state always was the state

Note: This linter can be disabled with `set_option linter.fugue.comments false`
-/
#guard_msgs in
set_option linter.fugue.comments.soft true in
def statusProseOptIn : Nat :=
  -- not yet threaded through the loop
  0
