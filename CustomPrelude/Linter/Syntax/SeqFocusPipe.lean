module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.seqFocusPipe`

Batteries' `seq_focus` notation is `t <;> [t₁; t₂; …]` (`;`-separated). `CustomPrelude` respells
it `t <;> [t₁ | t₂ | …]` (`|`-separated) to pair with the project's other bracketed tactic
lists. Deterministic — one right spelling.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `t <;> [a; b]` → `t <;> [a | b]`. -/
register_option linter.fugue.seqFocusPipe : Bool := {
  defValue := true
  descr := "flag Batteries' `;`-separated `<;> [ … ]` — use the project's `|`-separated form"
}

/-- Every Batteries `seq_focus` node. -/
def seqFocusPipeCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.getKind == `Batteries.Tactic.seq_focus then
      hit s m!"`t <;> [a; b]` → `t <;> [a | b]` (the project's spelling)"
    else #[]

/-- The `linter.fugue.seqFocusPipe` linter. -/
def seqFocusPipe : Linter where run := mkFugueLinter linter.fugue.seqFocusPipe seqFocusPipeCore

initialize addLinter seqFocusPipe

end CustomPrelude.Linter
