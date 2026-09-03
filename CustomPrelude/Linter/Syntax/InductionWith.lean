module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.inductionWith`

`induction` / `fun_induction` carry their cases in `with | name => …`, checked for
exhaustiveness — a forgotten constructor is an error at the `induction`, not a goal that
survives to the end of the proof. Never bare `case name =>` blocks after the tactic.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `induction`/`fun_induction` cases in `with`, no trailing bare `case`. -/
register_option linter.fugue.inductionWith : Bool := {
  defValue := true
  descr := "flag `induction`/`fun_induction` without `with`, or with a trailing `case`/`next`"
}

/-- Whether `t` is an `induction`/`fun_induction` node, and whether it has a `with`. `cases`
is excluded — a bare `cases h` on a single-constructor type is ordinary destructuring. -/
private def elimWith? (t : Syntax) : Option Bool :=
  if t.isOfKind ``Lean.Parser.Tactic.induction || t.getKind == `Lean.Parser.Tactic.funInduction then
    some (t.find? (·.isOfKind ``Lean.Parser.Tactic.inductionAlts)).isSome
  else none

private def isCaseOrNext (t : Syntax) : Bool :=
  t.isOfKind ``Lean.Parser.Tactic.case
    || t.getKind == `Lean.Parser.Tactic.case'
    || t.getKind == `Lean.Parser.Tactic.«tacticNext_=>_»

/-- Every `induction`/`fun_induction` lacking `with`, and every one followed by a bare
`case`/`next` sibling. -/
def inductionWithCore : Syntax → Array Finding :=
  scan λ seq ↦
    if seq.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
      let tacs := seqTactics seq
      tacs.zipIdx.foldl (init := #[]) λ out (t, i) ↦
        match elimWith? t with
        | some hasWith =>
          if !hasWith then
            out.push ⟨t, m!"`induction`/`fun_induction` without `with` — carry the cases in `with | … => …`"⟩
          else if (tacs[i + 1]?.any isCaseOrNext) then
            out.push ⟨t, m!"trailing bare `case`/`next` after `induction` — move it into the `with` block"⟩
          else out
        | none => out
    else #[]

/-- The `linter.fugue.inductionWith` linter. -/
def inductionWith : Linter where run := mkFugueLinter linter.fugue.inductionWith inductionWithCore

initialize addLinter inductionWith

end CustomPrelude.Linter
