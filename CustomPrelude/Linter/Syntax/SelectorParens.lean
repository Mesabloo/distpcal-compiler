module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.selectorParens`

A goal selector already scopes its tactic block — `all: tac₁; tac₂`, `1,3: …`, `all_goals …`.
Wrapping that block in `( … )` adds nothing. Put the sequence directly after the `:` (indented
on the next line if it spans lines).
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- No `( … )` around a selector's tactic block. -/
register_option linter.fugue.selectorParens : Bool := {
  defValue := true
  descr := "flag `all: ( … )` / `all_goals ( … )` — the selector already groups"
}

/-- The tactic block a selector applies, if `s` is one. -/
private def selectorBlock? (s : Syntax) : Option Syntax :=
  if s.isOfKind ``Lean.Parser.Tactic.allGoals || s.isOfKind ``Lean.Parser.Tactic.anyGoals then
    some s[1]
  else if s.getKind == `CustomPrelude.Tactic.«tactic_:_» then some s[2]
  else if s.getKind == `Batteries.Tactic.«tacticOn_goal-_=>_» then s.find? (·.isOfKind ``Lean.Parser.Tactic.tacticSeq)
  else none

/-- Every selector whose block is a single parenthesised tactic. -/
def selectorParensCore : Syntax → Array Finding :=
  scan λ s ↦
    match selectorBlock? s with
    | some blk =>
      match seqTactics blk with
      | #[t] => if t.isOfKind ``Lean.Parser.Tactic.paren then
          hit t m!"a selector already groups its block — drop the `( … )`"
        else #[]
      | _ => if blk.isOfKind ``Lean.Parser.Tactic.paren then
          hit blk m!"a selector already groups its block — drop the `( … )`"
        else #[]
    | none => #[]

/-- The `linter.fugue.selectorParens` linter. -/
def selectorParens : Linter where
  run := mkFugueLinter linter.fugue.selectorParens selectorParensCore

initialize addLinter selectorParens

end CustomPrelude.Linter
