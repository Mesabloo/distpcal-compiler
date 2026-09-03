module

import CustomPrelude

/-! Tests for `linter.fugue.aesopTerminal`. -/

/--
warning: `aesop` config silences the non-terminal warning — make the `aesop` terminal instead

Note: This linter can be disabled with `set_option linter.fugue.aesopTerminal false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  aesop (config := { warnOnNonterminal := false })

section
/--
warning: `set_option aesop.warn.nonterminal false` — make the `aesop` terminal instead

Note: This linter can be disabled with `set_option linter.fugue.aesopTerminal false`
-/
#guard_msgs in
set_option aesop.warn.nonterminal false
end

-- A terminal `aesop` is fine.
#guard_msgs in
example (p : Prop) (h : p) : p := by aesop
