module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.rwaExact`

`rw [...] at h` then `exact h`, or `rw [...]` then `exact h` for a hypothesis already in context,
is `rwa` — the rewrite absorbs the closing `assumption`. Same for `erw` / `erwa`.

This linter covers the `at h` form (the name is right there in the rewrite). The bare
`rw […]; exact <hyp>` form needs an is-local check — `linter.fugue.rwaExactBare` (Sem).
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `rw … at h; exact h` → `rwa … at h`. -/
register_option linter.fugue.rwaExact : Bool := {
  defValue := true
  descr := "flag `rw [...] at h` immediately followed by `exact h` — use `rwa`"
}

/-- In each tactic sequence, a `rw`/`erw`/`simp_rw` `… at h` whose next sibling is `exact h`. -/
def rwaExactCore : Syntax → Array Finding :=
  scan λ seq ↦
    if seq.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
      let tacs := seqTactics seq
      tacs.zipIdx.foldl (init := #[]) λ out (t, i) ↦
        let isRw := t.getKind == ``Lean.Parser.Tactic.rwSeq
          || t.getKind == `Lean.Parser.Tactic.tacticErw__
          || t.getKind == `Mathlib.Tactic.tacticSimp_rw___
        match (if isRw then (locationHyps t)[0]? else none), tacs[i + 1]? with
        | some h, some n =>
          if n.getKind == ``Lean.Parser.Tactic.exact && identLast? n[1] == some h then
            out.push ⟨t, m!"`rw … at {h}` then `exact {h}` → `rwa … at {h}`"⟩
          else out
        | _, _ => out
    else #[]

/-- The `linter.fugue.rwaExact` linter. -/
def rwaExact : Linter where run := mkFugueLinter linter.fugue.rwaExact rwaExactCore

initialize addLinter rwaExact

end CustomPrelude.Linter
