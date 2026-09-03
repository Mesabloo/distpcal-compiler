module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.haveBareName`

`have x : Y := z` for a bare name `z` — a lone identifier, no dots — is never right. If `z` is a
hypothesis, retyping it by defeq is `change Y at z`; if `z` is a nullary global, inline it at its
use site.

A dotted right-hand side (`sim.mem_agree'`, `hpr.field`) is a projection, not a bare name, and a
clarifying type on it is often the point — those are left alone.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- No `have x : Y := <bare name>`. -/
register_option linter.fugue.haveBareName : Bool := {
  defValue := true
  descr := "flag `have x : Y := z` for a bare identifier `z` — `change … at z`, or inline the global"
}

/-- A lone identifier with no namespace component — a hypothesis or nullary global referenced
directly. `rfl` (a defeq fact) and dotted projections (`a.b`) are not this. -/
private def isBareName (stx : Syntax) : Bool :=
  match stx with
  | .ident _ _ n _ => match n.eraseMacroScopes with
    | .str .anonymous s => s ≠ "rfl"
    | _ => false
  | _ => false

/-- Every `have … : … := <bare identifier>`. -/
def haveBareNameCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.isOfKind ``Lean.Parser.Tactic.tacticHave__ then
      match s.find? (·.isOfKind ``Lean.Parser.Term.letIdDecl) with
      | some d =>
        if d[2].getArgs.size > 0 && isBareName d[4] then
          hit d[4] m!"`have x : Y := <bare name>` — `change Y at z` for a hypothesis, or inline a global at its use"
        else #[]
      | none => #[]
    else #[]

/-- The `linter.fugue.haveBareName` linter. -/
def haveBareName : Linter where run := mkFugueLinter linter.fugue.haveBareName haveBareNameCore

initialize addLinter haveBareName

end CustomPrelude.Linter
