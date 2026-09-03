module

import CustomPrelude

/-! Tests for `linter.fugue.sigIndent` (opt-in — `default := false`). -/

-- Off by default: a mis-indented signature is silent unless the option is set.
#guard_msgs in
theorem sigQuietByDefault {a : Nat}
    (h : a = a) :
  a = a :=
  h

-- Correct: binder continuation at +2, statement at +4.
#guard_msgs in
set_option linter.fugue.sigIndent true in
theorem sigOk {a : Nat}
  (h : a = a) :
    a = a :=
  h

/--
warning: binder line at column 4 — indent it 2

Note: This linter can be disabled with `set_option linter.fugue.sigIndent false`
-/
#guard_msgs in
set_option linter.fugue.sigIndent true in
theorem sigBadBinder {a : Nat}
    (h : a = a) :
    a = a :=
  h

/--
warning: statement at column 2 — indent it 4

Note: This linter can be disabled with `set_option linter.fugue.sigIndent false`
-/
#guard_msgs in
set_option linter.fugue.sigIndent true in
theorem sigBadStatement {a : Nat}
  (h : a = a) :
  a = a :=
  h
