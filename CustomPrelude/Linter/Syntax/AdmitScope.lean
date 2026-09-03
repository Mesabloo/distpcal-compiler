module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.admitScope`

A `sorry` in tactic position is written `admit` — the tactic keyword makes the syntactic scope
explicit. In term position `sorry` stays. This is the inverse of Mathlib's `linter.style.admit`.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Tactic-position `sorry` → `admit`. -/
register_option linter.fugue.admitScope : Bool := {
  defValue := true
  descr := "flag a tactic-position `sorry` — write `admit`"
}

/-- Every tactic-position `sorry`. -/
def admitScopeCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.isOfKind ``Lean.Parser.Tactic.tacticSorry then
      hit s m!"tactic-position `sorry` → `admit`"
    else #[]

/-- The `linter.fugue.admitScope` linter. -/
def admitScope : Linter where run := mkFugueLinter linter.fugue.admitScope admitScopeCore

initialize addLinter admitScope

end CustomPrelude.Linter
