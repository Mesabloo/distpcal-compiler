module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.sigIndent`

Signature continuation lines: a line that carries binders/hypotheses indents two past the
declaration keyword, and the line that carries the statement itself — after the top-level `:` —
indents four, so the statement stays visually distinct from what it quantifies over.

`default := false`: most existing signatures in the tree put their binders at four, so this
carries a large backlog and is opt-in until that is worked through.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Signature continuation indent: binders +2, statement +4. -/
register_option linter.fugue.sigIndent : Bool := {
  defValue := false
  descr := "flag signature continuation lines whose binders are not indented +2 or statement not +4"
}

/-- The indentation (first non-whitespace column) of the source line holding `p`. -/
private def lineIndent (fm : FileMap) (p : String.Pos.Raw) : Nat :=
  let ss : Substring.Raw := ⟨fm.source, fm.lineStart (fm.toPosition p).line, p⟩
  (ss.toString.toList.takeWhile (·.isWhitespace)).length

/-- `p` is the first non-whitespace on its source line. -/
private def atLineStart (fm : FileMap) (p : String.Pos.Raw) : Bool :=
  let ss : Substring.Raw := ⟨fm.source, fm.lineStart (fm.toPosition p).line, p⟩
  ss.toString.all (·.isWhitespace)

/-- The statement term of a `declSig` / `optDeclSig` node, if it carries one. -/
private def sigStatement? (sig : Syntax) : Option Syntax :=
  let t := sig[1]
  if t.isOfKind ``Lean.Parser.Term.typeSpec then some t[1]
  else if t[0].isOfKind ``Lean.Parser.Term.typeSpec then some t[0][1]
  else none

/-- Findings for the signatures under `stx`. -/
def sigIndentCore (stx : Syntax) : CommandElabM (Array Finding) := do
  let sigs := collect (λ s ↦ s.isOfKind ``Lean.Parser.Command.declSig
    || s.isOfKind ``Lean.Parser.Command.optDeclSig) stx
  if sigs.isEmpty then return #[]
  let ids := collect (·.isOfKind ``Lean.Parser.Command.declId) stx
  let some idPos := ids[0]?.bind (·.getPos?) | return #[]
  let fm ← getFileMap
  let base := lineIndent fm idPos
  let mut out : Array Finding := #[]
  for sig in sigs do
    for b in sig[0].getArgs do
      let some bp := b.getPos? | continue
      if atLineStart fm bp && (fm.toPosition bp).column != base + 2 then
        out := out.push ⟨b, m!"binder line at column {(fm.toPosition bp).column} — indent it {base + 2}"⟩
    if let some t := sigStatement? sig then
      if let some tp := t.getPos? then
        if atLineStart fm tp && (fm.toPosition tp).column != base + 4 then
          out := out.push ⟨t, m!"statement at column {(fm.toPosition tp).column} — indent it {base + 4}"⟩
  return out

/-- The `linter.fugue.sigIndent` linter. -/
def sigIndent : Linter where run := mkFugueLinterM linter.fugue.sigIndent sigIndentCore

initialize addLinter sigIndent

end CustomPrelude.Linter
