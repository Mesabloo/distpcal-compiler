module

public meta import CustomPrelude.Linter.Basic
public meta import Lean.Server.InfoUtils

/-!
# `linter.fugue.rwaExactBare`

`rw [S]` (no `at`) immediately followed by `exact h` for a hypothesis `h` already in context is
`rwa [S]` — the rewrite absorbs the closing `assumption`. Same for `erw` / `simp_rw`.

The `rw [S] at h` form is `linter.fugue.rwaExact` (Syn): there the name in the rewrite already
says `h` is a hypothesis. In the bare form the identifier could be a global lemma — and `rwa`
(`rw` then `assumption`) closes the goal only from a *local* hypothesis — so this linter reads the
`InfoTree` and flags only when `h` names a local declaration of the goal the `exact` faced.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `rw [S]; exact h` for a local `h` → `rwa [S]`. -/
register_option linter.fugue.rwaExactBare : Bool := {
  defValue := true
  descr := "flag `rw [...]` (no `at`) then `exact h` for a local hypothesis — use `rwa`"
}

/-- The rewrite word to name in the message, `none` for a non-rewrite or a rewrite with `at`. -/
private def bareRwWord? (t : Syntax) : Option String :=
  let w := match t.getKind with
    | ``Lean.Parser.Tactic.rwSeq => some "rw"
    | `Lean.Parser.Tactic.tacticErw__ => some "erw"
    | `Mathlib.Tactic.tacticSimp_rw___ => some "simp_rw"
    | _ => none
  if (t.find? (·.isOfKind ``Lean.Parser.Tactic.location)).isSome then none else w

/-- A `rw [S]; exact h` window with a bare `rw`: the `exact` node (anchor and range key), the
rewrite word, and the hypothesis name. -/
private structure Cand where
  exStx : Syntax
  word : String
  hyp : Name

private def candidates (stx : Syntax) : Array Cand := Id.run do
  let mut out : Array Cand := #[]
  for seq in collect (·.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented) stx do
    let tacs := seqTactics seq
    for h : i in [0:tacs.size] do
      let some word := bareRwWord? tacs[i] | continue
      let some n := tacs[i + 1]? | continue
      unless n.getKind == ``Lean.Parser.Tactic.exact do continue
      unless n[1].isIdent do continue
      out := out.push { exStx := n, word, hyp := n[1].getId }
  return out

/-- Whether `nm` (raw, or with macro scopes erased) names a local declaration of `goal`. -/
private def hypIsLocal (mctx : MetavarContext) (goal : MVarId) (nm : Name) : Bool :=
  match mctx.findDecl? goal with
  | none => false
  | some mdecl =>
    (mdecl.lctx.findFromUserName? nm).isSome
      || (mdecl.lctx.findFromUserName? nm.eraseMacroScopes).isSome

/-- Every bare `rw [S]; exact h` whose `h` is a local hypothesis. -/
def rwaExactBareCore : Syntax → CommandElabM (Array Finding) := λ stx ↦ do
  let cands := candidates stx
  if cands.isEmpty then return #[]
  let keyed := cands.filterMap λ c ↦ c.exStx.getRange?.map λ r ↦ (r.start.byteIdx, c)
  let mut out : Array Finding := #[]
  let mut seen : Std.HashSet Nat := {}
  for tree in (← getInfoTrees) do
    let hits ← tree.foldInfoM (init := (#[] : Array (Nat × Finding))) λ _ info acc ↦ do
      let .ofTacticInfo ti := info | return acc
      let some r := ti.stx.getRange? | return acc
      let some (k, c) := keyed.find? (·.1 == r.start.byteIdx) | return acc
      let some goal := ti.goalsBefore.head? | return acc
      unless hypIsLocal ti.mctxBefore goal c.hyp do return acc
      return acc.push (k, ⟨c.exStx, m!"`{c.word} [S]` then `exact {c.hyp}` → `{c.word}a [S]`"⟩)
    for (p, f) in hits do
      unless seen.contains p do
        seen := seen.insert p
        out := out.push f
  return out

/-- The `linter.fugue.rwaExactBare` linter. -/
def rwaExactBare : Linter where run := mkFugueLinterM linter.fugue.rwaExactBare rwaExactBareCore

initialize addLinter rwaExactBare

end CustomPrelude.Linter
