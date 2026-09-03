module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.goalSelector`

`CustomPrelude`'s Rocq-style `tac_selector` covers what `all_goals` / `on_goal` do and more:
`all: tac`, `3: tac`, `1,3-5,9-12: tac`, also in `conv`. `any_goals` is useless — drop it.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Use `all:` / `n:`, not `all_goals` / `any_goals` / `on_goal`. -/
register_option linter.fugue.goalSelector : Bool := {
  defValue := true
  descr := "flag `all_goals` / `any_goals` / `on_goal` — use the `tac_selector` syntax"
}

/-- Every `all_goals` / `any_goals` / `on_goal`. -/
def goalSelectorCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.isOfKind ``Lean.Parser.Tactic.allGoals then
      hit s m!"`all_goals tac` → `all: tac`"
    else if s.isOfKind ``Lean.Parser.Tactic.anyGoals then
      hit s m!"`any_goals` is useless — drop it, or `all: tac` if a selector is meant"
    else if s.getKind == `Batteries.Tactic.«tacticOn_goal-_=>_» then
      hit s m!"`on_goal n => tac` → `n: tac`"
    else #[]

/-- The `linter.fugue.goalSelector` linter. -/
def goalSelector : Linter where run := mkFugueLinter linter.fugue.goalSelector goalSelectorCore

initialize addLinter goalSelector

end CustomPrelude.Linter
