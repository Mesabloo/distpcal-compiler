module

public meta import Lean.Elab.Tactic

/-!
# `injections … with`

`injections`, followed by a `rename_i` so the equalities it introduces arrive named.
-/

open Lean Lean.Parser Lean.Parser.Tactic

namespace CustomPrelude.Tactic

/-- `injections`, naming the hypotheses it introduces. -/
macro "injections " "with " names:(ppSpace colGt binderIdent)+ : tactic =>
  `(tactic| (injections; rename_i $names*))

end CustomPrelude.Tactic
