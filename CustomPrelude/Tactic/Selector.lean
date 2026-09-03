module

public meta import Lean.Elab.Tactic

/-!
# Rocq-style goal selectors

`n: tac`, `1,3-5: tac`, `all: tac` — apply a tactic sequence to a chosen range of subgoals,
and the matching form in `conv`.
-/

open Lean Elab Term Meta Tactic

namespace CustomPrelude.Tactic

declare_syntax_cat range_selector
syntax num : range_selector
syntax num "-" num : range_selector
declare_syntax_cat tac_selector
/-- Select multiple ranges of subgoals. -/
syntax (range_selector),+ : tac_selector
/-- Select all the subgoals. -/
syntax "all" : tac_selector

/-- Select the subgoals onto which to apply a given tactic sequence, Rocq style. -/
syntax tac_selector ": " tacticSeq : tactic

private meta def selectGoals (stx : TSyntax `tac_selector) (mvarIds : List MVarId) : MetaM ((List MVarId) × (List MVarId)) :=
  match stx with
    | `(tac_selector|all) => return (mvarIds,[])
    | `(tac_selector| $[$r:range_selector],* ) => do
      let mut set := Std.HashSet.emptyWithCapacity
      for r in r do
        match r with
          | `(range_selector|$n:num) => set := set.insert n.getNat
          | `(range_selector|$n₁:num - $n₂:num) => for n in [n₁.getNat:n₂.getNat+1] do set := set.insert n
          | _ => throwUnsupportedSyntax
      return mvarIds.zipIdx 1 |>.partitionMap λ (mvar, i) ↦ if i ∈ set then .inl mvar else .inr mvar
    | _ => throwUnsupportedSyntax

elab_rules : tactic
  | `(tactic| $select:tac_selector : $t:tacticSeq) => do
    let mvarIds ← getUnsolvedGoals
    let (mvarIds,unselectedMVarIds) ← selectGoals select mvarIds
    let mut mvarIdsNew := unselectedMVarIds
    let mut abort := false
    for mvarId in mvarIds do
      setGoals [mvarId]
      let saved ← saveState
      abort ← Tactic.tryCatch
        (do
          evalTactic t
          pure abort)
        (λ ex ↦ do
          if (← read).recover then
            logException ex
            let msgLog ← Core.getMessageLog
            saved.restore
            Core.setMessageLog msgLog
            admitGoal mvarId
            pure true
          else
            throw ex)
      mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
    if abort then
      throwAbortTactic
    setGoals mvarIdsNew

open Lean.Parser.Tactic.Conv in
/-- Select the subgoals onto which to apply a given `conv` sequence, Rocq style. -/
macro sel:tac_selector ": " s:convSeq : conv =>
  `(conv| tactic' => $sel:tac_selector : conv' => $s)

end CustomPrelude.Tactic
