module

public meta import Batteries.Tactic.SeqFocus

/-!
# `t <;> [t₁ | t₂ | …]`

`seq_focus`'s own notation, respelled with `|` separators to pair with the project's other
bracketed tactic lists.
-/

open Lean Lean.Parser Lean.Parser.Tactic

namespace CustomPrelude.Tactic

@[inherit_doc Batteries.Tactic.seq_focus]
macro:1 t:tactic " <;> " "[" ts:sepBy(tactic, " | ") "]" : tactic => `(tactic| $t <;> [$[$ts];*])

end CustomPrelude.Tactic
