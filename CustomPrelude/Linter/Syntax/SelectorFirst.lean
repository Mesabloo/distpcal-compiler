module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.selectorFirst`

A blanket selector (`all:` / `all_goals` / `any_goals`) wrapping a `first | …` or `solve | …`
with two or more alternatives runs the same search on every goal. Tailor a selector per
alternative instead — `1,2,9-14: tac₁` / `3-8: tac₂` / … — so the script says which goal gets
which tactic. Nested `first`/`solve` inside one alternative is fine.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- No blanket selector over a `first`/`solve` with ≥2 alternatives. -/
register_option linter.fugue.selectorFirst : Bool := {
  defValue := true
  descr := "flag `all:` / `all_goals` / `any_goals` wrapping a multi-branch `first` / `solve`"
}

/-- Every blanket selector whose (unwrapped) body is a `first`/`solve` with ≥2 alternatives. -/
def selectorFirstCore : Syntax → Array Finding :=
  scan λ s ↦
    match selectorBody? s with
    | some body =>
      match firstOrSolveAlts? (unwrapTac body) with
      | some n => if n ≥ 2 then
          hit s m!"blanket selector over a multi-branch `first`/`solve` — tailor a selector per alternative"
        else #[]
      | none => #[]
    | none => #[]

/-- The `linter.fugue.selectorFirst` linter. -/
def selectorFirst : Linter where run := mkFugueLinter linter.fugue.selectorFirst selectorFirstCore

initialize addLinter selectorFirst

end CustomPrelude.Linter
