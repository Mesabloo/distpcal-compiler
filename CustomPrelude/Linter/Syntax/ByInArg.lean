module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.byInArg`

A tactic proof passed as an argument is a step with no name and no goal displayed. Two
replacements: a term when one exists (often the side condition is a hypothesis up to defeq), else
a `?_` and the next line — `exact f (g (by tac))` becomes `refine f (g ?_)` then `tac`.

`LEAN_STYLE.md` calls this "too common to mechanize", so the linter ships **off** — flip it on
(`set_option linter.fugue.byInArg true in …`) for a deliberate one-file sweep.

Covers both application arguments (`f (by …)`) and anonymous-constructor components
(`⟨…, by …, …⟩`) — the latter is more common and takes longer to work off.

The solely-`assumption` case is `linter.fugue.byAssumption`'s; this linter leaves it alone.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- No `(by …)` in argument position. Off by default (`LEAN_STYLE.md`: too common to mechanize). -/
register_option linter.fugue.byInArg : Bool := {
  defValue := false
  descr := "flag `(by …)` in application-argument position — use a term, or `refine` + `?_`"
}

/-- Whether `a` is a `by` block that is not solely `assumption` (that case is `byAssumption`'s). -/
private def flaggableBy (a : Syntax) : Bool :=
  a.isOfKind ``Lean.Parser.Term.byTactic &&
    let tacs := seqTactics a[1]
    ! (tacs.size == 1 && (tacs[0]?.any (·.isOfKind ``Lean.Parser.Tactic.assumption)))

/-- Every `(by …)` in application-argument or anonymous-constructor position, bar the
solely-`assumption` case. -/
def byInArgCore : Syntax → Array Finding :=
  scan λ s ↦
    let candidates :=
      if s.isOfKind ``Lean.Parser.Term.anonymousCtor then s[1].getArgs
      else appArgs s
    candidates.filterMap λ a ↦
      if flaggableBy a then
        some ⟨a, m!"`(by …)` in argument position — a term if one exists, else `refine`/`apply` and `?_`"⟩
      else none

/-- The `linter.fugue.byInArg` linter. -/
def byInArg : Linter where run := mkFugueLinter linter.fugue.byInArg byInArgCore

initialize addLinter byInArg

end CustomPrelude.Linter
