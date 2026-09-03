module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.simpaUsing`

`have h := e` then `simp only [S] at h` then `exact h` is `simpa only [S] using e` — the
hypothesis exists only to be simplified and handed over, so it needs no name and no line.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `have h := e; simp only [S] at h; exact h` → `simpa only [S] using e`. -/
register_option linter.fugue.simpaUsing : Bool := {
  defValue := true
  descr := "flag the `have` / `simp … at h` / `exact h` window — use `simpa … using`"
}

/-- The name a `have` binds (its `letId`), if it binds one. -/
private def haveName? (t : Syntax) : Option String :=
  if t.getKind == ``Lean.Parser.Tactic.tacticHave__ then
    (t.find? (·.isOfKind ``Lean.Parser.Term.letIdDecl)).bind (identLast? ·[0][0])
  else none

/-- Every `have h := e` / `simp[ only] [S] at h` / `exact h` triple where `h` is used nowhere
else. -/
def simpaUsingCore : Syntax → Array Finding :=
  scan λ seq ↦
    if seq.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
      let tacs := seqTactics seq
      tacs.zipIdx.foldl (init := #[]) λ out (t, i) ↦
        match haveName? t, tacs[i + 1]?, tacs[i + 2]? with
        | some h, some s, some e =>
          let simpAtH := s.getKind == ``Lean.Parser.Tactic.simp && (locationHyps s).contains h
          let exactH := e.getKind == ``Lean.Parser.Tactic.exact && identLast? e[1] == some h
          -- `h` must not appear after the `exact`
          let usedLater := (tacs.extract (i + 3) tacs.size).any λ u ↦ (identsUnder u).contains h
          if simpAtH && exactH && !usedLater then
            out.push ⟨t, m!"`have {h} := e; simp … at {h}; exact {h}` → `simpa … using e`"⟩
          else out
        | _, _, _ => out
    else #[]

/-- The `linter.fugue.simpaUsing` linter. -/
def simpaUsing : Linter where run := mkFugueLinter linter.fugue.simpaUsing simpaUsingCore

initialize addLinter simpaUsing

end CustomPrelude.Linter
