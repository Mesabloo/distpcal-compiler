module

public meta import Lean.Elab.Tactic

/-!
# `erwa`

`erwa` is to `erw` what `rwa` is to `rw`: rewrite up to unfolding, then close by `assumption`.
-/

open Lean Lean.Parser.Tactic

namespace CustomPrelude.Tactic

/-- `erwa` is to `erw` what `rwa` is to `rw`. -/
macro "erwa " c:optConfig s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| (rw $[$(getConfigItems c)]* (transparency := .default) $s:rwRuleSeq $(loc)?; assumption))

end CustomPrelude.Tactic
