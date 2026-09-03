module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.rflHaveSimp`

`have h : x = y := rfl` followed by `simp only [h, …]` states the new goal *and* pays a traversal
to arrive at it. `change` states it once, and the traversal was never doing anything.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Defeq massage: `change`, not `simp only` over a `rfl`-`have`. -/
register_option linter.fugue.rflHaveSimp : Bool := {
  defValue := true
  descr := "flag `have _ := rfl` consumed by a following `simp only` — use `change`"
}

/-- Every `have h : _ := rfl` whose next `simp only` names `h`. -/
def rflHaveSimpCore : Syntax → Array Finding :=
  scan λ seq ↦
    if seq.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
      let tacs := seqTactics seq
      tacs.zipIdx.foldl (init := #[]) λ out (t, i) ↦
        if t.getKind != ``Lean.Parser.Tactic.tacticHave__ then out
        else match t.find? (·.isOfKind ``Lean.Parser.Term.letIdDecl) with
        | none => out
        | some d =>
          let rhsRfl := identLast? d[4] == some "rfl"
          let hName := identLast? d[0][0]
          match hName, tacs[i + 1]? with
          | some h, some n =>
            let simpNamesH := n.getKind == ``Lean.Parser.Tactic.simp
              && (n.find? (·.isOfKind `Lean.Parser.Tactic.simpLemma)).isSome
              && (identsUnder n).contains h
            if rhsRfl && simpNamesH then
              out.push ⟨t, m!"`have {h} : _ := rfl` then `simp only [{h}, …]` → `change`"⟩
            else out
          | _, _ => out
    else #[]

/-- The `linter.fugue.rflHaveSimp` linter. -/
def rflHaveSimp : Linter where run := mkFugueLinter linter.fugue.rflHaveSimp rflHaveSimpCore

initialize addLinter rflHaveSimp

end CustomPrelude.Linter
