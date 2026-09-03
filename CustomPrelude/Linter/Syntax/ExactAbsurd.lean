module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.exactAbsurd`

`exact absurd x y` opens no goal and reads backwards. Use the `absurd` tactic, `nomatch h`, or a
named `have` that `contradiction` finds.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- No `exact absurd x y`. -/
register_option linter.fugue.exactAbsurd : Bool := {
  defValue := true
  descr := "flag `exact absurd x y` — use the `absurd` tactic, `nomatch`, or `contradiction`"
}

/-- Every `exact` whose term is a `absurd …` application. -/
def exactAbsurdCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.isOfKind ``Lean.Parser.Tactic.exact then
      let t := s[1]
      let head := if t.isOfKind ``Lean.Parser.Term.app then t[0] else t
      if identLast? head == some "absurd" then
        hit s m!"`exact absurd x y` — use the `absurd` tactic, `nomatch h`, or a `have` + `contradiction`"
      else #[]
    else #[]

/-- The `linter.fugue.exactAbsurd` linter. -/
def exactAbsurd : Linter where run := mkFugueLinter linter.fugue.exactAbsurd exactAbsurdCore

initialize addLinter exactAbsurd

end CustomPrelude.Linter
