module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.comments`

The mechanically-checkable half of `INSTRUCTIONS.md` §Comments, in one pass over each command's
source span (leading trivia, doc comment, and inline `--` notes included):

* **commented-out code** — a `--` line that is really a pasted declaration / directive / proof;
* **plan reference** — `PLAN.md`, `OPEN_QUESTIONS.md`, `.claude/`, `§N`;
* **paper citation** — `arXiv`, `reference/*.pdf`, `[HFP`, `Specifying Systems`, `Definition N.N`;
* **prior-art comparison** — "prior art", "distpcal-compiler", "earlier design", "once already";
* **line-numbered cross-reference** — `Foo.lean:123`;
* **bare separator** — a comment that is only dashes;
* **subjectless `TODO`** — a `TODO` not written `TODO(subject):`;
* **expiring URL** — a signed `githubusercontent.com` link;
* **long module doc** — a `/-! … -/` over 25 lines is a design essay;
* **status prose** — "still owed", "not yet", "for now": a docstring reads as if the current
  state always was the state.

The judgment half — proof narration, consumer notes, a weak docstring — stays a reader's call.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- The comment-discipline linter. -/
register_option linter.fugue.comments : Bool := {
  defValue := true
  descr := "flag comment-discipline violations from INSTRUCTIONS.md §Comments"
}

/--
The two heuristic sub-checks — long module docs and status prose — that carry enough false
positives to be opt-in. Off by default; `linter.fugue.comments` still gates them.
-/
register_option linter.fugue.comments.soft : Bool := {
  defValue := false
  descr := "also flag module docs over 25 lines and status prose (\"not yet\", \"for now\", …)"
}

namespace Comments

/-- `needle` occurs contiguously somewhere in `hay`. -/
private partial def infixOf (needle hay : List Char) : Bool :=
  needle.isPrefixOf hay || (match hay with | [] => false | _ :: t => infixOf needle t)

/-- `l` ends with `suf`. -/
private def suffixOf (suf l : List Char) : Bool := suf.reverse.isPrefixOf l.reverse

/-- `needle` occurs contiguously somewhere in `hay`. -/
private def has (hay : List Char) (needle : String) : Bool := infixOf needle.toList hay

/-- `hay` starts with `pat`. -/
private def pre (pat : String) (hay : List Char) : Bool := pat.toList.isPrefixOf hay

/-- Drop leading ASCII whitespace. -/
private def trimL (l : List Char) : List Char := l.dropWhile (·.isWhitespace)

/-- Drop leading and trailing ASCII whitespace. -/
private def trimC (l : List Char) : List Char :=
  (trimL l).reverse.dropWhile (·.isWhitespace) |>.reverse

/-- Lowercase. -/
private def low (l : List Char) : List Char := l.map Char.toLower

/-- The per-line char walk behind `viewOf`. -/
private partial def viewGo : List Char → Nat → Array Char → Bool → List Char × Nat
  | [], d, acc, _ => (acc.toList, d)
  | [c], d, acc, _ => if d > 0 then ((acc.push c).toList, d) else (acc.toList, d)
  | c :: c' :: rest, d, acc, inStr =>
    if d > 0 then
      if c == '-' && c' == '/' then viewGo rest (d - 1) acc false
      else if c == '/' && c' == '-' then viewGo rest (d + 1) acc false
      else viewGo (c' :: rest) d (acc.push c) false
    else if inStr then
      if c == '\\' then viewGo rest d acc true
      else if c == '"' then viewGo (c' :: rest) d acc false
      else viewGo (c' :: rest) d acc true
    else if c == '"' then viewGo (c' :: rest) d acc true
    else if c == '/' && c' == '-' then
      match rest with
      | m :: rest' => if m == '-' || m == '!' then viewGo rest' 1 acc false else viewGo rest 1 acc false
      | [] => ([], 1)
    else if c == '-' && c' == '-' then (c :: c' :: rest, d)
    else viewGo (c' :: rest) d acc false

/--
The comment-only view of one source line, given the block-comment nesting `depth` on entry:
`--` line comments keep their marker and text, `/- … -/` block interiors are kept without the
delimiters, code and string literals become nothing. Returns the view and the nesting depth on
exit (a command's span is self-contained, so it always returns to `0`).
-/
private def viewOf (cs : List Char) (depth : Nat) : List Char × Nat := viewGo cs depth #[] false

/-- Every suffix of `hay` beginning immediately after an occurrence of `marker`. -/
private partial def afterMarker (marker : List Char) (hay : List Char) : List (List Char) :=
  let here := if marker.isPrefixOf hay then [hay.drop marker.length] else []
  match hay with
  | [] => here
  | _ :: t => here ++ afterMarker marker t

/-- Some occurrence of `marker` in `v` is followed (optionally past spaces) by text `p` accepts. -/
private def markerThen (v : List Char) (marker : String) (skipSpace : Bool)
    (p : List Char → Bool) : Bool :=
  (afterMarker marker.toList v).any λ rest ↦
    p (if skipSpace then rest.dropWhile (· == ' ') else rest)

/-- Text begins with a digit. -/
private def digitHead : List Char → Bool
  | c :: _ => c.isDigit
  | [] => false

/-- Text begins `<digits>.<digit>` — a `Definition 3.2`-shaped citation number. -/
private def digitDotDigit (s : List Char) : Bool :=
  let ds := s.takeWhile (·.isDigit)
  !ds.isEmpty && (match s.drop ds.length with
    | '.' :: d :: _ => d.isDigit
    | _ => false)

/-- The tail of `v` after its first `--`, left-trimmed; `none` if there is no `--`. -/
private def afterDashes (v : List Char) : Option (List Char) :=
  (afterMarker "--".toList v).head?.map trimL

private def directiveKw : List String :=
  ["import ", "open ", "set_option ", "#guard", "@[", "deriving instance"]

private def declKw : List String :=
  ["theorem ", "lemma ", "def ", "abbrev ", "instance ", "structure ", "inductive ", "class ",
   "partial ", "private ", "protected ", "macro "]

/-- The last whitespace-separated token of `v`. -/
private def lastToken (v : List Char) : List Char :=
  (trimC v).reverse.takeWhile (!·.isWhitespace) |>.reverse

/-- One source line is a non-empty `--` comment. -/
private def isDashLine (v : List Char) : Bool :=
  pre "--" (trimL v) && !(trimC ((trimL v).drop 2)).isEmpty

/-- `v` (a comment view) is a pasted declaration / directive line. -/
private def commentedCodeSingle (v : List Char) : Bool :=
  match afterDashes v with
  | none => false
  | some ct =>
    directiveKw.any (pre · ct)
      || (declKw.any (pre · ct)
          && (has v ":=" || lastToken v == "by".toList || lastToken v == "where".toList))

/-- `v` trimmed is `--` followed only by more dashes. -/
private def bareSeparator (v : List Char) : Bool :=
  let t := trimC v
  t.length ≥ 2 && t.all (· == '-')

/-- Findings for one command's source span. -/
def core (stx : Syntax) : CommandElabM (Array Finding) := do
  if stx.isOfKind ``Lean.Parser.Module.header then return #[]
  let some sstr := stx.getSubstring? (withTrailing := false) | return #[]
  let soft := getLinterValue linter.fugue.comments.soft (← getLinterOptions)
  let lines := (sstr.splitOn "\n").toArray
  let mut out : Array Finding := #[]
  if soft && stx.isOfKind ``Lean.Parser.Command.moduleDoc && lines.size > 25 then
    out := out.push ⟨stx, m!"module doc over 25 lines — a design essay belongs in PLAN.md, \
      not a docstring"⟩
  let mut views : Array (List Char × Syntax) := #[]
  let mut depth := 0
  for ln in lines do
    let (v, d) := viewOf ln.toString.toList depth
    views := views.push (v, Syntax.ofRange ⟨ln.startPos, ln.stopPos⟩)
    depth := d
  for h : i in [0:views.size] do
    let (v, ref) := views[i]
    if v.isEmpty then continue
    let lv := low v
    if has v "PLAN.md" || has v "OPEN_QUESTIONS.md" || has v ".claude/"
        || markerThen v "§" true digitHead then
      out := out.push ⟨ref, m!"plan/task reference in a comment — state the fact, not the document"⟩
    if has v "arXiv" || has v ".pdf" || has v "[HFP" || has v "Specifying Systems"
        || ["Definition ", "Remark ", "Listing ", "Example ", "Def. "].any
             (markerThen v · false digitDotDigit) then
      out := out.push ⟨ref, m!"paper citation in a comment — record it in reference/SPEC_MAP.md"⟩
    if has lv "prior art" || has lv "distpcal-compiler" || has lv "earlier design"
        || has lv "once already" then
      out := out.push ⟨ref, m!"prior-art comparison — state the current invariant, not what it replaced"⟩
    if markerThen v ".lean:" false digitHead then
      out := out.push ⟨ref, m!"line-numbered cross-reference — name the declaration, a line number rots"⟩
    if bareSeparator v then
      out := out.push ⟨ref, m!"bare separator comment — delete it, or make it a `/-! … -/` header"⟩
    if markerThen v "TODO" false (λ rest ↦ match rest with
        | '(' :: _ => false
        | ':' :: _ => false
        | _ => true) then
      out := out.push ⟨ref, m!"subjectless `TODO` — write `TODO(subject): what is owed`"⟩
    if has v "githubusercontent.com" && has v "jwt=" then
      out := out.push ⟨ref, m!"expiring URL — the signed link is already dead, delete it"⟩
    if soft && ["still owed", "not yet", "for now", "as it now stands", "will produce", "so far"].any
        (has lv ·) then
      out := out.push ⟨ref, m!"status prose in a comment — read as if the current state always was the state"⟩
    if commentedCodeSingle v
        || (isDashLine v && i ≥ 2 && isDashLine views[i-1]!.1 && isDashLine views[i-2]!.1
            && ["by".toList, ":=".toList, "⟩".toList].any (suffixOf · (trimC v))) then
      out := out.push ⟨ref, m!"commented-out code — delete it, git has it"⟩
  return out

end Comments

/-- The `linter.fugue.comments` linter. -/
def comments : Linter where run := mkFugueLinterM linter.fugue.comments Comments.core

initialize addLinter comments

end CustomPrelude.Linter
