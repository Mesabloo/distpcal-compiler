module

public meta import CustomPrelude.Linter.Basic
public meta import Lean.Server.InfoUtils

/-!
# `linter.fugue.hypOrder`

`intro` / `rintro` names should run in the order the binders appear, so a reader can match them
without counting. Naming by role rather than by position (`rintro ref₁ ref₃ ref₂` because `ref₃`
was "the aborting one") reads as a slip even when deliberate.

The linter fires only on the unambiguous case: every pattern is a plain identifier, and the names
chosen are a *permutation* of the goal's leading binder names — the same names, reordered. Fresh
names that do not match the binders are a free rename and are left alone; a deliberate reorder
takes the per-site escape.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Name introduced hypotheses in signature order. -/
register_option linter.fugue.hypOrder : Bool := {
  defValue := true
  descr := "flag `intro` / `rintro` whose names are the goal's binder names in a different order"
}

/-- The identifier a plain `intro` / `rintro` pattern binds; `none` for a hole or a compound
pattern. -/
private partial def patIdent? (s : Syntax) : Option Name :=
  if s.isIdent then some s.getId.eraseMacroScopes
  else match s.getKind with
    | `Lean.Parser.Tactic.rintroPat.one
    | `Lean.Parser.Tactic.rcasesPat.one
    | `Lean.Parser.Tactic.binderIdent => patIdent? s[0]
    | _ => none

/-- The `intro` / `rintro` nodes and their raw pattern arguments. -/
private def candidates (stx : Syntax) : Array (Syntax × Array Syntax) :=
  (collect (λ s ↦ s.getKind == ``Lean.Parser.Tactic.intro
                || s.getKind == ``Lean.Parser.Tactic.rintro) stx).map λ s ↦ (s, s[1].getArgs)

private def sortedStrings (ns : Array Name) : Array String := (ns.map toString).qsort (· < ·)

/-- Every `intro` / `rintro` whose plain-ident names permute the goal's leading binder names. -/
def hypOrderCore : Syntax → CommandElabM (Array Finding) := λ stx ↦ do
  let cands := candidates stx
  if cands.isEmpty then return #[]
  let keyed := cands.filterMap λ (s, args) ↦ do
    let r ← s.getRange?
    -- every argument must be a plain identifier
    let names ← args.mapM patIdent?
    guard (names.size ≥ 2)
    return (r.start.byteIdx, s, names)
  if keyed.isEmpty then return #[]
  let mut out : Array Finding := #[]
  let mut seen : Std.HashSet Nat := {}
  for tree in (← getInfoTrees) do
    let hits ← tree.foldInfoM (init := (#[] : Array (Nat × Finding))) λ ctx info acc ↦ do
      let .ofTacticInfo ti := info | return acc
      let some r := ti.stx.getRange? | return acc
      let some (key, s, names) := keyed.find? (·.1 == r.start.byteIdx) | return acc
      let some goal := ti.goalsBefore.head? | return acc
      let bn ← ctx.runMetaM {} <| Meta.withMCtx ti.mctxBefore do
        let ty ← instantiateMVars (← goal.getType)
        Meta.forallBoundedTelescope ty (some names.size) λ xs _ ↦
          xs.mapM λ x ↦ return (← x.fvarId!.getUserName).eraseMacroScopes
      unless bn.size == names.size do return acc
      if sortedStrings bn == sortedStrings names && bn != names then
        let order := String.intercalate " " (bn.map toString).toList
        return acc.push (key, ⟨s, m!"introduced names are out of signature order — the binders run `{order}`"⟩)
      return acc
    for (p, f) in hits do
      unless seen.contains p do
        seen := seen.insert p
        out := out.push f
  return out

/-- The `linter.fugue.hypOrder` linter. -/
def hypOrder : Linter where run := mkFugueLinterM linter.fugue.hypOrder hypOrderCore

initialize addLinter hypOrder

end CustomPrelude.Linter
