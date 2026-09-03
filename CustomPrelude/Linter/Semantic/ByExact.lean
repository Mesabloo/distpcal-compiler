module

public meta import CustomPrelude.Linter.Basic
public meta import Mathlib.Tactic.Linter.HaveLetLinter

/-!
# `linter.fugue.byExact`

`by exact e` in term position is `e`. `by classical exact e` is `e` when `e` does not actually
need the classical instance — and when it does, `classical` belongs further up (an `open
Classical in` on the enclosing declaration, or a `classical` hoisted above the branch that needs
it), not wrapped around a single `exact`.

The inner term is re-elaborated against the goal *before* the `by` block ran — for the
`classical` case that context has no extra instance, so a success means `classical` did nothing
here.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `by exact e` → `e`; `by classical exact e` → hoist `classical` or drop it. -/
register_option linter.fugue.byExact : Bool := {
  defValue := true
  descr := "flag `by exact e` / `by classical exact e` whose inner term stands on its own"
}

/-- A `by` block that is exactly `exact e` or `classical exact e`: `(byStx, hasClassical, headTac,
term)`. -/
private structure Cand where
  byStx : Syntax
  hasClassical : Bool
  head : Syntax
  term : Syntax

private def candidates (stx : Syntax) : Array Cand :=
  (collect (·.isOfKind ``Lean.Parser.Term.byTactic) stx).filterMap λ b ↦ do
    let seq := seqTactics b[1]
    let head ← seq[0]?
    if head.getKind == `Lean.Parser.Tactic.classical then
      let inner := seqTactics head[1]
      let ex ← inner[0]?
      guard (inner.size == 1 && ex.getKind == ``Lean.Parser.Tactic.exact)
      return { byStx := b, hasClassical := true, head := head, term := ex[1] }
    else
      guard (seq.size == 1 && head.getKind == ``Lean.Parser.Tactic.exact)
      return { byStx := b, hasClassical := false, head := head, term := head[1] }

/-- Whether `e` elaborates at `goal`'s type in `goal`'s context under `mctx`. -/
private def standsAlone (ctx : ContextInfo) (mctx : MetavarContext) (goal : MVarId) (e : Syntax) :
    BaseIO Bool := do
  let some decl := mctx.decls.find? goal | return false
  match ← (ctx.runMetaM decl.lctx (Meta.withMCtx mctx do
      let ty ← goal.getType
      Term.TermElabM.run' do
        Term.withoutErrToSorry do
          Term.withSynthesize do
            discard <| Term.elabTermEnsuringType e (some ty))).toBaseIO with
  | .ok _ => return true
  | .error _ => return false

/-- Every term-position `by exact e` / `by classical exact e` whose inner term stands alone. -/
def byExactCore : Syntax → CommandElabM (Array Finding) := λ stx ↦ do
  let cands := candidates stx
  if cands.isEmpty then return #[]
  -- index each candidate's leading tactic by source range
  let ranges := cands.filterMap λ c ↦ c.head.getRange? |>.map (·, c)
  let mut out : Array Finding := #[]
  let mut seen : Std.HashSet Nat := {}
  for tree in (← getInfoTrees) do
    let hits ← tree.foldInfoM (init := (#[] : Array (Nat × Finding))) λ ctx info acc ↦ do
      let .ofTacticInfo ti := info | return acc
      let some r := ti.stx.getRange? | return acc
      let some (_, c) := ranges.find? (·.1 == r) | return acc
      let some goal := ti.goalsBefore.head? | return acc
      unless ← standsAlone ctx ti.mctxBefore goal c.term do return acc
      let msg := if c.hasClassical then
          m!"`by classical exact e` — `e` elaborates without `classical`; hoist `classical` (`open Classical in` on the declaration, or above the branch that needs it), or drop it"
        else
          m!"`by exact e` in term position → just `e`"
      return acc.push (r.start.byteIdx, ⟨c.byStx, msg⟩)
    for (p, f) in hits do
      unless seen.contains p do
        seen := seen.insert p
        out := out.push f
  return out

/-- The `linter.fugue.byExact` linter. -/
def byExact : Linter where run := mkFugueLinterM linter.fugue.byExact byExactCore

initialize addLinter byExact

end CustomPrelude.Linter
