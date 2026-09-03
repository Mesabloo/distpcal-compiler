module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.selectorTry`

`all: try tac` — and every other selector over a bare `try` (`1-3: try tac`,
`all_goals try tac`) — runs `tac` under `try`, so a goal where `tac` fails is silently left
untouched and the proof no longer records which goals the selector closed. Name the goals the
tactic applies to (`1,3: tac`), or drop the `try` and the selector both if it closes them all.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- No `try` as the whole body of a goal selector. -/
register_option linter.fugue.selectorTry : Bool := {
  defValue := true
  descr := "flag a goal selector (`all:` / `n-m:` / `all_goals`) whose body is a bare `try`"
}

/-- Every selector whose (unwrapped) body is a lone `try …`. -/
def selectorTryCore : Syntax → Array Finding :=
  scan λ s ↦
    match selectorBody? s with
    | some body =>
      if (unwrapTac body).isOfKind ``Lean.Parser.Tactic.tacticTry_ then
        hit s m!"selector body is a bare `try` — hides which goals it closed; name the goals it applies to, or drop `try` and the selector if it closes them all"
      else #[]
    | none => #[]

/-- The `linter.fugue.selectorTry` linter. -/
def selectorTry : Linter where run := mkFugueLinter linter.fugue.selectorTry selectorTryCore

initialize addLinter selectorTry

end CustomPrelude.Linter
