module

public meta import CustomPrelude.Linter.Basic
public meta import Lean.Server.InfoUtils

/-!
# `linter.fugue.unusedHave`

A `have` / `haveI` whose hypothesis the rest of the proof never touches is dead weight: it
survives every refactor that made it dead, and — for an instance `haveI` — Lean's
`unusedVariables` does not flag it at all.

The check reads the `InfoTree`. A tactic `have h : T := v` runs as `assert` + `intro`, leaving a
continuation goal `g'` with `h` in its local context; `h` is used exactly when its free variable
occurs in `g'`'s final assignment. That assignment is read from the command's last-finishing
tactic snapshot (every goal solved by then). Uses of `h` under the `fun h => …` the `have`
compiles to would read as bound variables, so the continuation goal is inspected directly, not
the whole proof term.

A continuation whose instantiated term still carries `sorry` or an unassigned metavariable is
skipped: the linter could not read the finished proof there (a `decreasing_by` block, elaborated
in its own later pass, is the usual reason), so it says nothing rather than guess "unused".
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Delete a `have` / `haveI` the proof does not use. -/
register_option linter.fugue.unusedHave : Bool := {
  defValue := true
  descr := "flag a `have` / `haveI` whose hypothesis the rest of the proof never uses"
}

private def isHaveKind (k : SyntaxNodeKind) : Bool :=
  k == ``Lean.Parser.Tactic.tacticHave__ || k == ``Lean.Parser.Tactic.tacticHaveI__

/-- Every tactic `have` / `haveI` whose introduced hypothesis is never used. -/
def unusedHaveCore : Syntax → CommandElabM (Array Finding) := λ stx ↦ do
  if (collect (λ s ↦ isHaveKind s.getKind) stx).isEmpty then return #[]
  let mut out : Array Finding := #[]
  let mut seen : Std.HashSet Nat := {}
  for tree in (← getInfoTrees) do
    -- The final `mctx` of the command — the `mctxAfter` of the last-finishing tactic (latest tail
    -- position). By then every `have`'s continuation goal is solved, across every `by` block the
    -- command elaborated. Also keep any one `ContextInfo` (only its env/options matter).
    let (best?, ctx?) ← tree.foldInfoM
      (init := ((none : Option (Nat × MetavarContext)), (none : Option ContextInfo)))
      λ ctx info acc ↦ do
        let .ofTacticInfo ti := info | return acc
        let some r := ti.stx.getRange? | return acc
        let b := r.stop.byteIdx
        let best := match acc.1 with
          | some (cur, m) => if b > cur then (b, ti.mctxAfter) else (cur, m)
          | none => (b, ti.mctxAfter)
        return (some best, acc.2 <|> some ctx)
    let some ctx := ctx? | continue
    let some (_, fmctx) := best? | continue
    let hits ← tree.foldInfoM (init := (#[] : Array (Nat × Finding))) λ _ info acc ↦ do
      let .ofTacticInfo ti := info | return acc
      unless isHaveKind ti.stx.getKind do return acc
      let .original .. := ti.stx.getHeadInfo | return acc
      let some r := ti.stx.getRange? | return acc
      let m := ti.mctxAfter
      let oldF := (ti.goalsBefore.filterMap (m.findDecl? ·)).flatMap (·.lctx.getFVarIds.toList)
      let newDecls := ti.goalsAfter.filterMap (m.findDecl? ·) |>.flatMap λ md ↦
        md.lctx.decls.toList.reduceOption.filter λ d ↦
          !oldF.contains d.fvarId && !d.isImplementationDetail
      if newDecls.isEmpty then return acc
      let contTerms ← ctx.runMetaM {} <| Meta.withMCtx fmctx do
        ti.goalsAfter.mapM λ g ↦ instantiateMVars (mkMVar g)
      -- an unfinished / unreachable continuation (e.g. a deferred `decreasing_by` proof) — say nothing
      if contTerms.any λ e ↦ e.hasSorry || e.hasExprMVar then return acc
      let word := if ti.stx.getKind == ``Lean.Parser.Tactic.tacticHaveI__ then "haveI" else "have"
      let mut acc := acc
      for d in newDecls do
        unless contTerms.any (·.containsFVar d.fvarId) do
          acc := acc.push (r.start.byteIdx,
            ⟨ti.stx, m!"`{word} {d.userName}` is never used — delete it"⟩)
      return acc
    for (p, f) in hits do
      unless seen.contains p do
        seen := seen.insert p
        out := out.push f
  return out

/-- The `linter.fugue.unusedHave` linter. -/
def unusedHave : Linter where run := mkFugueLinterM linter.fugue.unusedHave unusedHaveCore

initialize addLinter unusedHave

end CustomPrelude.Linter
