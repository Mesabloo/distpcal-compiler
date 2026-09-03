module

public meta import CustomPrelude.Linter.Basic
public meta import Lean.Server.InfoUtils

/-!
# `linter.fugue.selectorOneGoal`

`all:` / `all_goals` reads as "every branch"; over a *single* remaining goal there is no branch,
and a reader stops to look for the others. One goal, one `·` bullet.

The check is semantic: the selector's `TacticInfo` records exactly one goal before it ran.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `all:` / `all_goals` over one goal → `·` bullet. -/
register_option linter.fugue.selectorOneGoal : Bool := {
  defValue := true
  descr := "flag `all:` / `all_goals` applied when only one goal is open — use a `·` bullet"
}

/-- The selector word for `s` if it is `all_goals` or an `all:` `tac_selector`; `none` otherwise
(a numbered/range `tac_selector` is deliberately explicit and left alone). -/
private def allSelectorWord? (s : Syntax) : Option String :=
  if s.isOfKind ``Lean.Parser.Tactic.allGoals then some "all_goals"
  else if s.getKind == `CustomPrelude.Tactic.«tactic_:_»
      && (s[0].find? (·.getAtomVal == "all")).isSome then some "all:"
  else none

/-- Every `all:` / `all_goals` whose `TacticInfo` sees a single goal before it runs. -/
def selectorOneGoalCore : Syntax → CommandElabM (Array Finding) := λ stx ↦ do
  let cands := collect (λ s ↦ (allSelectorWord? s).isSome) stx
  if cands.isEmpty then return #[]
  let keyed := cands.filterMap λ s ↦ do
    let r ← s.getRange?
    let w ← allSelectorWord? s
    return (r.start.byteIdx, s, w)
  -- per selector node (keyed by start position): the goal counts it ran with, across the tree.
  -- A `| _ =>` wildcard arm or a post-`simp_all` VC block runs the selector several times with a
  -- varying count; flag only when *every* run saw exactly one goal.
  let mut counts : Std.HashMap Nat (Array Nat) := {}
  for tree in (← getInfoTrees) do
    counts ← tree.foldInfoM (init := counts) λ _ info acc ↦ do
      let .ofTacticInfo ti := info | return acc
      let some r := ti.stx.getRange? | return acc
      unless keyed.any (·.1 == r.start.byteIdx) do return acc
      return acc.insert r.start.byteIdx ((acc.getD r.start.byteIdx #[]).push ti.goalsBefore.length)
  return keyed.filterMap λ (k, s, w) ↦
    let ns := counts.getD k #[]
    if !ns.isEmpty && ns.all (· == 1) then
      some ⟨s, m!"`{w}` over a single goal — use a `·` bullet"⟩
    else none

/-- The `linter.fugue.selectorOneGoal` linter. -/
def selectorOneGoal : Linter where run := mkFugueLinterM linter.fugue.selectorOneGoal selectorOneGoalCore

initialize addLinter selectorOneGoal

end CustomPrelude.Linter
