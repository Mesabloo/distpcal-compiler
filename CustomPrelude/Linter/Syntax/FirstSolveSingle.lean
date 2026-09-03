module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.firstSolveSingle`

`first | t` with a single alternative is `t`; `solve | t` is `t` too (bar an error-message
nuance not worth the wrapper). Deterministic — no choice being expressed.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `first | t` / `solve | t` with one alternative → `t`. -/
register_option linter.fugue.firstSolveSingle : Bool := {
  defValue := true
  descr := "flag single-alternative `first` / `solve` — drop the wrapper"
}

/-- Every `first` / `solve` with exactly one alternative. -/
def firstSolveSingleCore : Syntax → Array Finding :=
  scan λ s ↦
    let kw? := if s.isOfKind ``Lean.Parser.Tactic.first then some "first"
               else if s.getKind == `Lean.solveTactic then some "solve"
               else none
    match kw? with
    | some kw => if s[1].getNumArgs == 1 then hit s m!"`{kw} | t` is just `t`" else #[]
    | none => #[]

/-- The `linter.fugue.firstSolveSingle` linter. -/
def firstSolveSingle : Linter where
  run := mkFugueLinter linter.fugue.firstSolveSingle firstSolveSingleCore

initialize addLinter firstSolveSingle

end CustomPrelude.Linter
