module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.noConfusion`

`Option.noConfusion` (and friends) need their implicit arguments to line up, and fail with an
application-type-mismatch when they do not. `contradiction` does the same job without the
bookkeeping.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `contradiction`, not `*.noConfusion`. -/
register_option linter.fugue.noConfusion : Bool := {
  defValue := true
  descr := "flag `*.noConfusion` — use `contradiction`"
}

/-- Every identifier or projection field named `noConfusion`. -/
def noConfusionCore : Syntax → Array Finding :=
  scan λ s ↦
    match s with
    | .ident .. => if nameHasComponent s.getId "noConfusion" then
        hit s m!"use `contradiction`, not `noConfusion` — `noConfusion` needs its implicits to line up"
      else #[]
    | _ => #[]

/-- The `linter.fugue.noConfusion` linter. -/
def noConfusion : Linter where run := mkFugueLinter linter.fugue.noConfusion noConfusionCore

initialize addLinter noConfusion

end CustomPrelude.Linter
