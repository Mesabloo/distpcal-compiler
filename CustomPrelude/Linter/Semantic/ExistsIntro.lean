module

public meta import CustomPrelude.Linter.Basic
public meta import Lean.Server.InfoUtils

/-!
# `linter.fugue.existsIntro`

`exists w₁, w₂` supplies the witnesses for an existential goal and leaves what remains as the
goal — no `?_` to count, no closing `⟩` to match, and it descends through `∧`. `refine ⟨w₁, w₂,
?_, …⟩` on a goal whose head is `Exists`, with every hole trailing and bare, is that pattern
spelled the long way.

`use` is the sibling to reach for when `exists`'s trailing `try trivial` would close a goal that
should stay open (it discharges at *reducible* transparency, and `use (discharger := skip)` turns
it off), or when the last conjunct also needs supplying (`exists` must leave one goal, `use` need
not). Both also split `∧` and any one-constructor structure/inductive — but this linter flags only
an `Exists`-headed goal (see the note in `existsIntroCore`).

A hole nested in a term (`Or.inr ?_`, `λ i ↦ ?_`) has no `exists`/`use` spelling, so an element
that is not either hole-free or a bare `?_`/`_` disqualifies the whole `refine`. The existential
check is semantic — the goal the `refine` faced.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Existential goal → `exists`, not `refine ⟨…⟩`. -/
register_option linter.fugue.existsIntro : Bool := {
  defValue := true
  descr := "flag `refine ⟨…, ?_⟩` on an existential goal — use `exists` for the leading witnesses"
}

private def isHoleKind (k : SyntaxNodeKind) : Bool :=
  k == ``Lean.Parser.Term.syntheticHole || k == ``Lean.Parser.Term.hole

private def hasHole (s : Syntax) : Bool := (s.find? (isHoleKind ·.getKind)).isSome

/-- For a `refine ⟨…⟩` whose `⟨…⟩` is `⟨t₁, …, tₖ, ?_, …, ?_⟩` (`k ≥ 1` hole-free terms then
`≥ 1` bare holes, nothing else), the witness count `k`; `none` otherwise. -/
private def trailingHoleCtor? (refineStx : Syntax) : Option Nat := do
  guard (refineStx.getKind == ``Lean.Parser.Tactic.refine)
  let ctor := refineStx[1]
  guard (ctor.getKind == ``Lean.Parser.Term.anonymousCtor)
  let elems := ctor[1].getArgs.getSepElems
  let k ← elems.findIdx? hasHole
  guard (k ≥ 1)
  guard ((elems.extract k elems.size).all λ e ↦ isHoleKind e.getKind)
  return k

/-- Every `refine ⟨…, ?_⟩` with trailing bare holes that faced an existential goal. -/
def existsIntroCore : Syntax → CommandElabM (Array Finding) := λ stx ↦ do
  let cands := (collect (λ s ↦ (trailingHoleCtor? s).isSome) stx).filterMap λ s ↦ do
    let r ← s.getRange?
    return (r.start.byteIdx, s)
  if cands.isEmpty then return #[]
  let mut out : Array Finding := #[]
  let mut seen : Std.HashSet Nat := {}
  for tree in (← getInfoTrees) do
    let hits ← tree.foldInfoM (init := (#[] : Array (Nat × Finding))) λ ctx info acc ↦ do
      let .ofTacticInfo ti := info | return acc
      let some r := ti.stx.getRange? | return acc
      let some (key, s) := cands.find? (·.1 == r.start.byteIdx) | return acc
      let some goal := ti.goalsBefore.head? | return acc
      -- `exists`/`use` also break `∧` and any one-constructor structure, but `refine ⟨_, ?_⟩`
      -- over a two-field `∧` is idiomatic and not the "count the `?_`, match the `⟩`" problem
      -- this rule is about; only an `Exists` head is flagged.
      let isEx ← ctx.runMetaM {} <| Meta.withMCtx ti.mctxBefore do
        let ty ← instantiateMVars (← goal.getType)
        pure ((← Meta.whnfR ty).isAppOf ``Exists)
      unless isEx do return acc
      return acc.push (key, ⟨s, m!"existential goal — `exists` (or `use`) the witnesses, not `refine ⟨…, ?_⟩`"⟩)
    for (p, f) in hits do
      unless seen.contains p do
        seen := seen.insert p
        out := out.push f
  return out

/-- The `linter.fugue.existsIntro` linter. -/
def existsIntro : Linter where run := mkFugueLinterM linter.fugue.existsIntro existsIntroCore

initialize addLinter existsIntro

end CustomPrelude.Linter
