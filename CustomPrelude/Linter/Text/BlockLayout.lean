module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.blockLayout`

A tactic-grouping block — `( … )` or `{ … }` — that spans lines keeps its opening bracket on the
line that opens it, puts the first tactic on the *next* line, and closes with the bracket alone on
the last line, dedented back to the opening line's indentation. One-liners stay one-liners.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Multi-line `( … )` / `{ … }` tactic blocks are opened, indented, and closed like a block. -/
register_option linter.fugue.blockLayout : Bool := {
  defValue := true
  descr := "flag a multi-line `( … )` / `{ … }` tactic block whose first tactic shares the opening line or whose closing bracket is not alone and dedented"
}

/-- The indentation (first non-whitespace column) of the source line holding `p`. -/
private def lineIndent (fm : FileMap) (p : String.Pos.Raw) : Nat :=
  let ls := fm.lineStart (fm.toPosition p).line
  let ss : Substring.Raw := ⟨fm.source, ls, p⟩
  (ss.toString.toList.takeWhile (·.isWhitespace)).length

/-- `p` sits at the start of its source line — only whitespace precedes it. -/
private def atLineStart (fm : FileMap) (p : String.Pos.Raw) : Bool :=
  let ss : Substring.Raw := ⟨fm.source, fm.lineStart (fm.toPosition p).line, p⟩
  ss.toString.all (·.isWhitespace)

/-- The block's tactics are `;`-separated — a one-liner `(a; b)` that only wrapped for length,
not a deliberately block-formatted sequence. -/
private partial def hasSemiSep : Syntax → Bool
  | s => match s.getKind with
    | ``Lean.Parser.Tactic.tacticSeq => hasSemiSep s[0]
    | ``Lean.Parser.Tactic.tacticSeq1Indented => s[0].getArgs.any (·.getAtomVal == ";")
    | ``Lean.Parser.Tactic.tacticSeqBracketed => hasSemiSep s[1]
    | _ => false

/-- Findings for the multi-line grouping blocks under `stx`. -/
def blockLayoutCore (stx : Syntax) : CommandElabM (Array Finding) := do
  let blocks := collect (λ s ↦ s.isOfKind ``Lean.Parser.Tactic.paren
    || s.isOfKind ``Lean.Parser.Tactic.tacticSeqBracketed) stx
  if blocks.isEmpty then return #[]
  let fm ← getFileMap
  let mut out : Array Finding := #[]
  for b in blocks do
    let some op := b[0].getPos? | continue
    let some cl := b[2].getPos? | continue
    let openLine := (fm.toPosition op).line
    let closeLine := (fm.toPosition cl).line
    if openLine == closeLine then continue        -- a one-liner is fine
    if hasSemiSep b[1] then continue               -- `(a; b)` that only wrapped for length
    let tacs := seqTactics b[1]
    if let some t0 := tacs[0]? then
      if let some tp := t0.getPos? then
        if (fm.toPosition tp).line == openLine then
          out := out.push ⟨t0,
            m!"first tactic shares the opening `{b[0].getAtomVal}` line — put it on the next line"⟩
    let want := lineIndent fm op
    if !atLineStart fm cl || (fm.toPosition cl).column != want then
      out := out.push ⟨b[2],
        m!"closing `{b[2].getAtomVal}` is not alone on its line, dedented to column {want}"⟩
  return out

/-- The `linter.fugue.blockLayout` linter. -/
def blockLayout : Linter where run := mkFugueLinterM linter.fugue.blockLayout blockLayoutCore

initialize addLinter blockLayout

end CustomPrelude.Linter
