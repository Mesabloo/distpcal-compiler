module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.seqSolveBracket`

`t <;> solve | s₁ | … | sₙ` with pairwise-distinct scripts runs a search on each of `t`'s goals
when the author already knows which goal gets which script. `t <;> [s₁ | … | sₙ]` (the project's
pipe form) says so positionally. All-equal scripts ⇒ one shared script ⇒ keep `<;> solve | s`.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `t <;> solve | s₁ | … | sₙ` (distinct sᵢ) → `t <;> [s₁ | … | sₙ]`. -/
register_option linter.fugue.seqSolveBracket : Bool := {
  defValue := true
  descr := "flag `t <;> solve | s₁ | … | sₙ` with distinct scripts — use `t <;> [s₁ | … | sₙ]`"
}

/-- Every `t <;> solve | …` whose alternatives are pairwise distinct. -/
def seqSolveBracketCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.getKind == ``Lean.Parser.Tactic.«tactic_<;>_» && s[2].getKind == `Lean.solveTactic then
      let alts := s[2][1].getArgs.map λ g ↦ g[1]
      if alts.size ≥ 2 && allDistinctShape alts then
        hit s m!"`t <;> solve | s₁ | … | sₙ` with distinct scripts → `t <;> [s₁ | … | sₙ]`"
      else #[]
    else #[]

/-- The `linter.fugue.seqSolveBracket` linter. -/
def seqSolveBracket : Linter where
  run := mkFugueLinter linter.fugue.seqSolveBracket seqSolveBracketCore

initialize addLinter seqSolveBracket

end CustomPrelude.Linter
