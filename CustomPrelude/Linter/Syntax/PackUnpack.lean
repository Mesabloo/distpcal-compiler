module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.packUnpack`

`obtain ⟨a, b, c⟩ : ∃ …, … := ⟨x, y, z⟩` builds an existential out of components that already
have names and destructures it on the same line; the ascription then restates types those
components already carried. Write the `have`s.

`obtain ⟨…⟩ : T := by tac` is a different tactic and stays fine — there the ascription is the
tactic block's goal.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Never pack a term only to unpack it. -/
register_option linter.fugue.packUnpack : Bool := {
  defValue := true
  descr := "flag `obtain ⟨…⟩ : T := ⟨…⟩` — write the `have`s"
}

/-- Every `obtain <tuple pattern> : T := ⟨a, b, c⟩` where every component of the right-hand tuple
is a plain identifier — the components already have names, so the ascription only restates their
types. A computed witness (`⟨k.toNat - 1, by omega⟩`) is genuine existential intro and stays. -/
def packUnpackCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.isOfKind ``Lean.Parser.Tactic.obtain then
      let hasType := s[2].getArgs.size > 0
      let patTuple := (s[1].find? (·.isOfKind ``Lean.Parser.Tactic.rcasesPat.tuple)).isSome
      let val := s[3][1][0]
      let allIdentCtor := val.isOfKind ``Lean.Parser.Term.anonymousCtor
        && (val[1].getArgs.all λ a ↦ a.isIdent || a matches .atom _ ",")
      if hasType && patTuple && allIdentCtor then
        hit s m!"`obtain ⟨…⟩ : T := ⟨…⟩` packs and unpacks in one line — write the `have`s"
      else #[]
    else #[]

/-- The `linter.fugue.packUnpack` linter. -/
def packUnpack : Linter where run := mkFugueLinter linter.fugue.packUnpack packUnpackCore

initialize addLinter packUnpack

end CustomPrelude.Linter
