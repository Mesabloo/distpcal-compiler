module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.mvcgenLayout`

`mvcgen`'s `invariants` and `with` clauses read like a `match`: the keyword sits on its own line
and its `| alt` / `· alt` branches are its *siblings*, at the keyword's own column — not indented
under it as if they were arguments to it.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `mvcgen`'s `invariants`/`with` alternatives align to the keyword, like a `match`. -/
register_option linter.fugue.mvcgenLayout : Bool := {
  defValue := true
  descr := "flag `mvcgen` `invariants`/`with` whose keyword is mid-line or whose alternatives are indented past it"
}

/-- `mvcgen`'s alternative node kinds — `Name` literals, not resolved, so this module needs no
import of `Std.Tactic.Do.Syntax`. -/
private def altKinds : List Name :=
  [`Lean.Parser.Tactic.invariantDotAlt, `Lean.Parser.Tactic.invariantCaseAlt,
   `Lean.Parser.Tactic.vcAlt]

/-- `p` sits at the start of its source line — only whitespace precedes it. -/
private def atLineStart (fm : FileMap) (p : String.Pos.Raw) : Bool :=
  let ss : Substring.Raw := ⟨fm.source, fm.lineStart (fm.toPosition p).line, p⟩
  ss.toString.all (·.isWhitespace)

/-- Findings for the `invariants`/`with` clauses under `stx`. -/
def mvcgenLayoutCore (stx : Syntax) : CommandElabM (Array Finding) := do
  let clauses := collect (λ s ↦ s.isOfKind `Lean.Parser.Tactic.invariantAlts
    || s.isOfKind `Lean.Parser.Tactic.vcAlts) stx
  if clauses.isEmpty then return #[]
  let fm ← getFileMap
  let mut out : Array Finding := #[]
  for cl in clauses do
    let kw := cl[0]
    let some kwPos := kw.getPos? | continue
    let kwName := if cl.isOfKind `Lean.Parser.Tactic.vcAlts then "with" else "invariants"
    unless atLineStart fm kwPos do
      out := out.push ⟨kw, m!"`{kwName}` starts mid-line — give it its own line, like a `match`"⟩
    let kwCol := (fm.toPosition kwPos).column
    for alt in collect (altKinds.contains ·.getKind) cl do
      let some aPos := alt.getPos? | continue
      if (fm.toPosition aPos).column > kwCol then
        out := out.push ⟨alt,
          m!"`mvcgen` alternative is indented past `{kwName}` — align it to the keyword's column"⟩
  return out

/-- The `linter.fugue.mvcgenLayout` linter. -/
def mvcgenLayout : Linter where run := mkFugueLinterM linter.fugue.mvcgenLayout mvcgenLayoutCore

initialize addLinter mvcgenLayout

end CustomPrelude.Linter
