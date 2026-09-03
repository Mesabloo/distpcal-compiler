module

public meta import CustomPrelude.Linter.Basic
public meta import Mathlib.Tactic.Linter.HaveLetLinter

/-!
# `linter.fugue.setNotLet`

`set x := e` exists to abstract a term `e` that *already occurs* in the goal — it rewrites every
occurrence to `x` and hands back `x = e`. When `e` occurs nowhere, `set` rewrites nothing: the
goal is unchanged, and a proof-local definition with no abstraction to do is a `let`.

The check is exactly that: the goal type before the `set` equals the goal type after. `let m :=
Nat.find hall` for a fresh `m`, `set m := Nat.find hall` where `Nat.find hall` is in the goal —
the first trips this, the second does not.

`set … with h` is left alone: the equation is doing work, and `let (eq := h)` (the replacement)
binds it in the opposite direction, which is not a mechanical swap.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `set x := e` that leaves the goal unchanged → `let`. -/
register_option linter.fugue.setNotLet : Bool := {
  defValue := true
  descr := "flag `set x := e` that does not change the goal — a proof-local definition is a `let`"
}

/-- Every `set` whose goal type is the same before and after. -/
def setNotLetCore : Syntax → CommandElabM (Array Finding) := λ stx ↦ do
  let sets := collect (·.getKind == `Mathlib.Tactic.setTactic) stx
  if sets.isEmpty then return #[]
  let keys := sets.filterMap λ s ↦ s.getRange?.map (·.start.byteIdx)
  let mut out : Array Finding := #[]
  let mut seen : Std.HashSet Nat := {}
  for tree in (← getInfoTrees) do
    let hits ← tree.foldInfoM (init := (#[] : Array (Nat × Finding))) λ ctx info acc ↦ do
      let .ofTacticInfo ti := info | return acc
      unless ti.stx.getKind == `Mathlib.Tactic.setTactic do return acc
      -- `set … with h` stays: `let (eq := h)` is the replacement, and it is not mechanical
      unless ti.stx[2][4].getArgs.isEmpty do return acc
      let some r := ti.stx.getRange? | return acc
      unless keys.contains r.start.byteIdx do return acc
      let some gb := ti.goalsBefore.head? | return acc
      let some ga := ti.goalsAfter.head? | return acc
      let unchanged ← ctx.runMetaM {} do
        let before ← Meta.withMCtx ti.mctxBefore (instantiateMVars (← gb.getType))
        let after ← Meta.withMCtx ti.mctxAfter (instantiateMVars (← ga.getType))
        return before == after
      if unchanged then
        let nm := (identsUnder ti.stx[2][0])[0]?.getD "x"
        return acc.push (r.start.byteIdx, ⟨ti.stx, m!"`set {nm} := …` leaves the goal unchanged — use `let`"⟩)
      return acc
    for (p, f) in hits do
      unless seen.contains p do
        seen := seen.insert p
        out := out.push f
  return out

/-- The `linter.fugue.setNotLet` linter. -/
def setNotLet : Linter where run := mkFugueLinterM linter.fugue.setNotLet setNotLetCore

initialize addLinter setNotLet

end CustomPrelude.Linter
