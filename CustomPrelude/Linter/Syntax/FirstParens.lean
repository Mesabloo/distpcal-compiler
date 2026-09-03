module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.firstParens`

`| pat => first` on one line, then its `| alt` branches indented under it — the `first`
alternatives sit one column in from the arm's `|`, so indentation already says which `|` is
whose. A wrapping `( … )` around the `first` adds nothing.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- No parens around a `first` over a `cases`/`rcases`/`match` arm. -/
register_option linter.fugue.firstParens : Bool := {
  defValue := true
  descr := "flag `(first | …)` — the parentheses add nothing over an arm"
}

/-- Every `( … )` tactic grouping whose sole content is a `first`. -/
def firstParensCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.isOfKind ``Lean.Parser.Tactic.paren
        && (unwrapTac s[1]).isOfKind ``Lean.Parser.Tactic.first then
      hit s m!"parentheses around `first` add nothing — `| pat => first` then the `|` branches under it"
    else #[]

/-- The `linter.fugue.firstParens` linter. -/
def firstParens : Linter where run := mkFugueLinter linter.fugue.firstParens firstParensCore

initialize addLinter firstParens

end CustomPrelude.Linter
