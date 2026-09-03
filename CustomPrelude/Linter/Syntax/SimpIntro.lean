module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.simpIntro`

When a subgoal is `intro`'d only to be finished by a bare closing `simp`, `simp_intro` does
both — it introduces the binders and simplifies as each arrives.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `intro …` then a closing `simp` → `simp_intro …`. -/
register_option linter.fugue.simpIntro : Bool := {
  defValue := true
  descr := "flag `intro` immediately before a terminal `simp` — use `simp_intro`"
}

/-- Every tactic sequence ending `… ; intro … ; simp`. -/
def simpIntroCore : Syntax → Array Finding :=
  scan λ seq ↦
    if seq.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
      let tacs := seqTactics seq
      if tacs.size ≥ 2 then
        let last := tacs[tacs.size - 1]!
        let prev := tacs[tacs.size - 2]!
        if last.getKind == ``Lean.Parser.Tactic.simp && prev.getKind == ``Lean.Parser.Tactic.intro then
          hit prev m!"`intro …` then a closing `simp` → `simp_intro …`"
        else #[]
      else #[]
    else #[]

/-- The `linter.fugue.simpIntro` linter. -/
def simpIntro : Linter where run := mkFugueLinter linter.fugue.simpIntro simpIntroCore

initialize addLinter simpIntro

end CustomPrelude.Linter
