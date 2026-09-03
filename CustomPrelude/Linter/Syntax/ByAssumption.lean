module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.byAssumption`

`f (by assumption)` opens a tactic block to do what a term already says, and hides which
hypothesis is meant. Write `‹_›`, or `‹T›` when the type reads.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- No `by assumption` as a term argument. -/
register_option linter.fugue.byAssumption : Bool := {
  defValue := true
  descr := "flag `(by assumption)` in argument position — write `‹_›`"
}

/-- Whether `t` is a `by` block whose sequence is exactly `assumption`. -/
private def isByAssumption (t : Syntax) : Bool :=
  t.isOfKind ``Lean.Parser.Term.byTactic
    && (seqTactics t[1]).size == 1
    && ((seqTactics t[1])[0]?.any (·.isOfKind ``Lean.Parser.Tactic.assumption))

/-- Every `(by assumption)` in application-argument position. -/
def byAssumptionCore : Syntax → Array Finding :=
  scan λ s ↦
    (appArgs s).filterMap λ a ↦
      if isByAssumption a then some ⟨a, m!"`by assumption` as a term argument → `‹_›`"⟩ else none

/-- The `linter.fugue.byAssumption` linter. -/
def byAssumption : Linter where run := mkFugueLinter linter.fugue.byAssumption byAssumptionCore

initialize addLinter byAssumption

end CustomPrelude.Linter
