module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.lambda`

`pp.unicode.fun` is on project-wide, so anonymous functions are written `λ x ↦ y`. This linter
flags the `fun` keyword — the inverse of Mathlib's `linter.style.lambdaSyntax`.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Write `λ x ↦ y`, not `fun x => y`. -/
register_option linter.fugue.lambda : Bool := {
  defValue := true
  descr := "flag the `fun` keyword — write `λ x ↦ y` (`pp.unicode.fun` is on)"
}

/-- Every `fun` keyword under `stx` (quotation interiors excepted). -/
def lambdaCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.isOfKind ``Lean.Parser.Term.fun then
      match s[0] with
      | .atom _ "fun" => hit s[0] m!"write `λ x ↦ y`, not `fun x => y`"
      | _ => #[]
    else #[]

/-- The `linter.fugue.lambda` linter. -/
def lambda : Linter where run := mkFugueLinter linter.fugue.lambda lambdaCore

initialize addLinter lambda

end CustomPrelude.Linter
