module

public meta import CustomPrelude.Linter.Basic
public meta import Lean.Elab.Command
public meta import Lean.Parser.Term
public meta import Lean.Server.InfoUtils

/-!
# `linter.fugue.bulletSubgoals`

A tactic that splits the goal is followed by one `·` per branch — always. Run unbulleted, nothing
marks where one branch ends and the next begins, and a later edit to the first branch silently
changes which goal the rest applies to.

This is a port of Mathlib's `linter.style.multiGoal`: its `getManyGoals` walk and its `exclusions`
/ `ignoreBranch` sets are reproduced verbatim (they have no extension point upstream), then
`exclusions` gains the project's deliberately-many-goals combinators — the `tac_selector`
(`1,2: tac`, `all: tac`) and the `<;> [t₁ | t₂]` pipe. `all_goals` / `any_goals` stay in
`ignoreBranch`, so this linter is quiet on them and `linter.fugue.goalSelector` is what flags
them. Do not also enable `linter.style.multiGoal`.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Bullet every subgoal a splitting tactic produces. -/
register_option linter.fugue.bulletSubgoals : Bool := {
  defValue := true
  descr := "flag a tactic run with several goals open that leaves some untouched — bullet each branch with `·`"
}

namespace BulletSubgoals

/-- Verbatim from `Mathlib.Linter.Style.multiGoal.exclusions`, plus the project's `tac_selector`
and `<;> [ … ]` pipe (both deliberately act on many goals at once). -/
abbrev exclusions : Std.HashSet SyntaxNodeKind := .ofArray #[
    -- structuring a proof
    ``Lean.Parser.Term.cdot,
    ``cdot,
    ``cdotTk,
    ``Lean.Parser.Tactic.tacticSeqBracketed,
    `«;»,
    `«<;>»,
    ``Lean.Parser.Tactic.«tactic_<;>_»,
    `«{»,
    `«]»,
    `null,
    `then,
    `else,
    ``Lean.Parser.Tactic.«tacticNext_=>_»,
    ``Lean.Parser.Tactic.tacticSeq1Indented,
    ``Lean.Parser.Tactic.tacticSeq,
    `focus,
    ``Lean.Parser.Tactic.focus,
    -- grind interactive mode
    ``Lean.Parser.Tactic.Grind.grindSeq1Indented,
    ``Lean.Parser.Tactic.Grind.grindSeq,
    ``Lean.Parser.Tactic.Grind.«grind·_»,
    ``Lean.Parser.Tactic.Grind.grindSeqBracketed,
    ``Lean.Parser.Tactic.Grind.«grind_<;>_»,
    ``Lean.Parser.Tactic.Grind.skip,
    ``Lean.Parser.Tactic.Grind.focus,
    ``Lean.Parser.Tactic.Grind.next,
    ``Lean.Parser.Tactic.Grind.cases,
    -- re-ordering goals
    `Batteries.Tactic.tacticSwap,
    ``Lean.Parser.Tactic.rotateLeft,
    ``Lean.Parser.Tactic.rotateRight,
    ``Lean.Parser.Tactic.skip,
    `Batteries.Tactic.«tacticOn_goal-_=>_»,
    `Mathlib.Tactic.«tacticSwap_var__,,»,
    -- tactic combinators
    ``Lean.Parser.Tactic.tacticRepeat_,
    ``Lean.Parser.Tactic.tacticTry_,
    -- creating new goals
    ``Lean.Parser.Tactic.paren,
    ``Lean.Parser.Tactic.case,
    ``Lean.Parser.Tactic.constructor,
    `Mathlib.Tactic.tacticAssumption',
    ``Lean.Parser.Tactic.induction,
    ``Lean.Parser.Tactic.cases,
    ``Lean.Parser.Tactic.intros,
    ``Lean.Parser.Tactic.injections,
    ``Lean.Parser.Tactic.substVars,
    `Batteries.Tactic.«tacticPick_goal-_»,
    ``Lean.Parser.Tactic.case',
    `«tactic#adaptation_note_»,
    `tacticSleep_heartbeats_,
    -- project combinators that deliberately run over many goals
    `CustomPrelude.Tactic.«tactic_:_»,
    `CustomPrelude.Tactic.«tactic_<;>[_|]»,
    `Batteries.Tactic.seq_focus
  ]

/-- Verbatim from `Mathlib.Linter.Style.multiGoal.ignoreBranch`. -/
abbrev ignoreBranch : Std.HashSet SyntaxNodeKind := .ofArray #[
    ``Lean.Parser.Tactic.Conv.conv,
    `Mathlib.Tactic.Conv.convLHS,
    `Mathlib.Tactic.Conv.convRHS,
    ``Lean.Parser.Tactic.first,
    ``Lean.Parser.Tactic.tacticRepeat_,
    ``Lean.Parser.Tactic.repeat',
    ``Lean.Parser.Tactic.tacticIterate____,
    ``Lean.Parser.Tactic.anyGoals,
    ``Lean.Parser.Tactic.allGoals,
    ``Lean.Parser.Tactic.failIfSuccess,
    ``Lean.Parser.Tactic.Grind.anyGoals,
    ``Lean.Parser.Tactic.Grind.allGoals,
    ``Lean.Parser.Tactic.Grind.first,
    ``Lean.Parser.Tactic.Grind.failIfSuccess,
    ``Lean.Parser.Tactic.Grind.grindRepeat_,
    `Mathlib.Tactic.successIfFailWithMsg
  ]

/-- `getManyGoals t`: the tactic nodes of `t` that leave a goal that was already open, with the
before/after/untouched counts. Verbatim from `Mathlib.Linter.Style.multiGoal.getManyGoals`, with
the two exempt sets swapped for the ones above. -/
partial def getManyGoals : InfoTree → Array (Syntax × Nat × Nat × Nat)
  | .node info args =>
    let kargs := (args.map getManyGoals).toArray.flatten
    if let .ofTacticInfo info := info then
      if ignoreBranch.contains info.stx.getKind then #[]
      else if info.goalsBefore.length == 1 && info.goalsAfter.length ≤ 1 then kargs
      else if let .original .. := info.stx.getHeadInfo then
        let backgroundGoals := info.goalsAfter.filter (info.goalsBefore.contains ·)
        if backgroundGoals.length != 0 && !exclusions.contains info.stx.getKind then
          kargs.push (info.stx,
                      info.goalsBefore.length, info.goalsAfter.length, backgroundGoals.length)
        else kargs
      else kargs
    else kargs
  | .context _ t => getManyGoals t
  | _ => #[]

end BulletSubgoals

/-- Every tactic run with several goals open that leaves some of them untouched. -/
def bulletSubgoalsCore : Syntax → CommandElabM (Array Finding) := λ _ ↦ do
  let mut out : Array Finding := #[]
  let mut seen : Std.HashSet Nat := {}
  for tree in (← getInfoTrees) do
    for (s, before, _after, n) in BulletSubgoals.getManyGoals tree do
      let some p := s.getRange?.map (·.start.byteIdx) | continue
      unless seen.contains p do
        seen := seen.insert p
        out := out.push ⟨s, m!"{before} goals open here, {n} left untouched — bullet each branch with `·`"⟩
  return out

/-- The `linter.fugue.bulletSubgoals` linter. -/
def bulletSubgoals : Linter where run := mkFugueLinterM linter.fugue.bulletSubgoals bulletSubgoalsCore

initialize addLinter bulletSubgoals

end CustomPrelude.Linter
