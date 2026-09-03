module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.rwShow`

An inline `show … by …` inside a rewrite argument hides a real proof step. State it as a `have`
and rewrite with that.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- No `rw [show … by …]`. -/
register_option linter.fugue.rwShow : Bool := {
  defValue := true
  descr := "flag `show … by …` inside a rewrite argument — hoist it to a `have`"
}

/-- Every `show … by …` inside a `rw`/`rwa`/`simp_rw`/`erw` rule list. -/
def rwShowCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.isOfKind ``Lean.Parser.Tactic.rwRuleSeq then
      match s.find? (λ n ↦ n.isOfKind ``Lean.Parser.Term.show
          && (n.find? (λ p ↦ p.isOfKind ``Lean.Parser.Term.byTactic
              || p.isOfKind ``Lean.Parser.Term.byTactic')).isSome) with
      | some sh => hit sh m!"no `rw [show … by …]` — state it as a `have` and rewrite with that"
      | none => #[]
    else #[]

/-- The `linter.fugue.rwShow` linter. -/
def rwShow : Linter where run := mkFugueLinter linter.fugue.rwShow rwShowCore

initialize addLinter rwShow

end CustomPrelude.Linter
