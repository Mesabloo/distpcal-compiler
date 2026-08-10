/-
Extract every hand-written local theorem into a JSONL fact database.

Run it from the project root, against an already-built project:

    lake env lean --run scripts/DumpFacts.lean [OUT]

`OUT` defaults to `.claude/facts/lemmas.jsonl`. One JSON object per line:

    n  fully qualified name          K  conclusion key heads (the primary search key)
    k  "thm" | "def" | "field"       c  every constant in the conclusion
    m  module name                   h  every constant in the hypotheses
    f  project-relative source path  a  attributes, as written
    l  line of the declared name     d  docstring, whitespace-collapsed
    t  pretty-printed type           s  the conclusion alone, what search results show
                                     H  number of hypotheses

Local means *declared in this project*. Imported developments are out of scope by design:
Mathlib is what `Loogle` and `lean_local_search` are for.

The script deliberately imports nothing but `Lean` and loads the environment at runtime, so it
compiles in a second and never interacts with the module system's `public import` rules.
-/
import Lean

open Lean Meta

/-! ## Deciding what is local -/

/-- Directories that hold no Lean source, or hold source we did not write. -/
def ignoredDirs : List String :=
  [".lake", ".claude", ".git", ".fugue", "reference", "runtime", "persistent", "docs",
   "tests", "scripts"]

/-- Module roots belonging to this project, read off the working directory rather than parsed out
of `lakefile.lean`: every top-level `.lean` file and every top-level directory containing one is a
root some `lean_lib` claims. Filesystem and lakefile cannot drift apart, because Lake resolves
modules through the same layout. -/
def localRoots : IO NameSet := do
  let mut roots : NameSet := {}
  for entry in ← System.FilePath.readDir "." do
    let name := entry.fileName
    if ignoredDirs.contains name || name.startsWith "." then continue
    if name.endsWith ".lean" then
      roots := roots.insert (Name.mkSimple ((name.dropEnd 5).toString))
    else if (← entry.path.isDir) then
      roots := roots.insert (Name.mkSimple name)
  return roots

/-- Module name to project-relative source path. -/
def modPath (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString)) ++ ".lean"

/-! ## Filtering noise out of the constant table -/

/-- The name as the source spells it. A `private` declaration is stored under a mangled name
(`_private.Guarded2Network.Lemmas.Precondition.0.Guarded2Network.Walk.reorder`), which every
consumer here would otherwise either reject as compiler-generated or record verbatim. -/
def userName (n : Name) : Name :=
  privateToUserName? n |>.getD n

/-- Compiler-generated names, whatever their shape. Most auto-generated constants are already
excluded by having no declaration range at all; this catches the rest. -/
def isInternal (n : Name) : Bool :=
  let n := userName n
  n.isInternal || n.hasMacroScopes ||
    n.components.any λ c ↦
      let s := c.toString
      ["rec", "recOn", "casesOn", "below", "brecOn", "ndrec", "ndrecOn", "noConfusion",
       "injEq", "sizeOf_spec", "eq_def"].contains s
        || s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "eq_"

/-- Instance and coercion plumbing (`Set.instHasSubset`, `MulOneClass.toMulOne`, …). Real constants,
but indexing a lemma under them buries the one head symbol a reader would actually search for. -/
def isPlumbing (n : Name) : Bool :=
  (userName n).components.any λ c ↦
    let s := c.toString
    s.startsWith "inst" || s.startsWith "to"

/-- Relations whose own name says nothing about what a lemma is *about*: indexing under `Eq` alone
would match a third of the database, so their arguments supply the key instead. -/
def bareRelations : List Name :=
  [`Eq, `Iff, `HasSubset.Subset, `HasSubset.Subset, `LE.le, `LT.lt, `Membership.mem, `Ne]

/-- Type formers and anonymous constructors that carry no search value as a conclusion key. The
constructors matter as much as the formers: `(x, e, y) ∈ R` would otherwise index under `Prod.mk`
rather than under whatever `R` is. -/
def uninformativeHeads : List Name :=
  [`Set, `Prod, `Option, `List, `Sigma, `PProd, `Subtype, `Type, `Sort,
   `Prod.mk, `Sigma.mk, `PProd.mk, `Subtype.mk, `Option.some]

/-! ## Reading the declaration's own source window -/

/-- What the source says about a constant, over the window from the start of its declaration to the
line naming it.

`findDeclarationRanges?` reports two ranges: `range` opens at the docstring or attribute line,
`selectionRange` points at the declared name. Everything between the two is the declaration's own
preamble, so a single scan of that window answers three questions at once — was this written by
hand, which attributes does it carry, and what does its docstring say.

Reading the docstring here rather than through `findDocString?` is not a shortcut: that function
returns `none` for every imported module in this setup, even with `loadExts := true`. -/
structure SrcInfo where
  /-- A `theorem` or `lemma` keyword appears in the window. -/
  isTheorem : Bool
  /-- A `def`/`abbrev`/`inductive`/`structure`/`class` keyword appears in the window. -/
  isDefinition : Bool
  /-- The window's last line binds the constant's own name — a `structure`/`class` field. -/
  isField : Bool
  /-- Attributes as written, one entry per comma-separated item. -/
  attrs : Array String
  /-- The docstring, collapsed to a single line. -/
  doc : Option String

/-- Split an `@[...]` line into its individual attributes.

Bracket-aware on purpose: `@[aesop safe apply (rule_sets := [sem])]` both closes on an inner `]`
and carries no comma at the top level, so neither the terminator nor the separator can be found by
scanning for a character. Which lemmas belong to the `sem` rule set is exactly the fact worth
recording — it says `sem_side` already discharges them, and applying them by hand is wasted work. -/
def parseAttrs (line : String) : Array String := Id.run do
  let opened := (line.dropWhile (· != '[')).drop 1
  let mut depth := 0
  let mut current := ""
  let mut out := #[]
  for c in opened.toString.toList do
    if c == '[' || c == '(' then
      depth := depth + 1
      current := current.push c
    else if c == ')' then
      depth := depth - 1
      current := current.push c
    else if c == ']' then
      if depth == 0 then break
      depth := depth - 1
      current := current.push c
    else if c == ',' && depth == 0 then
      out := out.push current.trimAscii.toString
      current := ""
    else
      current := current.push c
  let final := current.trimAscii.toString
  return if final.isEmpty then out else out.push final

/-- A source line with its leading attribute block and any declaration modifiers removed, so that
the declaration keyword — if there is one — is the first word.

Stripping beats enumerating: the modifiers combine freely (`public private theorem`,
`public noncomputable def`), and spelling out every combination is how a real declaration ends up
missing from the database. -/
partial def stripModifiers (line : String) : String :=
  let line := line.trimAsciiStart.toString
  let line := if line.startsWith "@[" then (line.splitOn "] ").getD 1 "" else line
  match ["private ", "protected ", "public ", "noncomputable ", "partial ", "unsafe ", "nonrec ",
      "scoped ", "local "].find? (λ modifier ↦ line.startsWith modifier) with
  | some modifier => stripModifiers (line.drop modifier.length).toString
  | none => line

/-- Keywords that introduce a definition worth indexing. `instance` is deliberately absent:
instances are found by synthesis, not by search, and `isPlumbing` filters their names anyway. -/
def definitionKeywords : List String :=
  ["def ", "abbrev ", "inductive ", "structure ", "class "]

/-- Scan the source window `[declStart, nameLine]` of a declaration in `file`. -/
def scanSource (file : String) (declStart nameLine : Nat) (leafName : String) : IO SrcInfo := do
  if !(← System.FilePath.pathExists file) then return ⟨false, false, false, #[], none⟩
  let src ← IO.FS.lines file
  let mut attrs := #[]
  let mut docLines := #[]
  let mut inDoc := false
  for i in [declStart - 1 : nameLine] do
    let some raw := src[i]? | continue
    let line := raw.trimAsciiStart.toString
    if inDoc then
      if line.endsWith "-/" then
        inDoc := false
        docLines := docLines.push ((line.dropEnd 2).trimAscii.toString)
      else
        docLines := docLines.push line
    else if line.startsWith "/--" then
      let body := (line.drop 3).trimAscii.toString
      if line.endsWith "-/" then
        docLines := docLines.push ((body.dropEnd 2).trimAscii.toString)
      else
        inDoc := true
        docLines := docLines.push body
    else if line.startsWith "@[" then
      attrs := attrs ++ parseAttrs line
  -- The keyword is read off the name line alone, never the rest of the window: a `structure`'s
  -- projections have declaration ranges that start at the `structure` keyword, so a window-wide
  -- scan reports every field as a definition of its own.
  let keywordLine := stripModifiers (src[nameLine - 1]?.getD "")
  let isTheorem := ["theorem ", "lemma "].any (λ keyword ↦ keywordLine.startsWith keyword)
  let isDefinition := definitionKeywords.any (λ keyword ↦ keywordLine.startsWith keyword)
  -- The line the selection range points at must actually spell the constant's own name.
  -- Attribute-generated companions inherit their source theorem's range, so `@[ext] theorem
  -- Block.ext_iff` otherwise contributes a phantom `Block.ext_iff_iff` sitting on the same line.
  let namesItself :=
    (src[nameLine - 1]?.map λ l ↦ decide ((l.splitOn leafName).length > 1)).getD false
  let declaresTheorem := isTheorem && namesItself
  let declaresDefinition := isDefinition && namesItself
  -- A class field is named by the window's own last line, with no keyword in front of it.
  let isField := !declaresTheorem && !declaresDefinition &&
    ((src[nameLine - 1]?.map λ l ↦
      let t := l.trimAsciiStart.toString
      t.startsWith (leafName ++ " ") || t.startsWith (leafName ++ ":")
        || t.startsWith (leafName ++ " :") || t.startsWith (leafName ++ "{")).getD false)
  let doc :=
    if docLines.isEmpty then none
    else some (" ".intercalate (docLines.toList.filter (!·.isEmpty)))
  return ⟨declaresTheorem, declaresDefinition, isField, attrs, doc⟩

/-- Attributes applied by a standalone `attribute [...] name₁ name₂ …` command, keyed by the name
each was applied to.

Unavoidably a second pass: these commands sit far from the declarations they tag — the `sem` aesop
rule set is populated in blocks of a dozen names at the end of a section — so no per-declaration
source window can see them. They are also where nearly all of the rule-set membership lives, which
is the single most useful attribute in this project: a lemma in `sem` is already discharged by
`sem_side`, and applying it by hand is wasted work.

Names are written relative to the enclosing `namespace`, and resolving that properly would mean
tracking `namespace`/`section`/`end` nesting. Suffix matching against the facts *of the same file*
is enough instead, because a file that declares two constants with the same suffix could not
mention either unqualified without ambiguity itself. -/
def scanAttributeCommands (file : String) : IO (Array (String × String)) := do
  if !(← System.FilePath.pathExists file) then return #[]
  let src ← IO.FS.lines file
  let mut out := #[]
  let mut i := 0
  while h : i < src.size do
    let line := src[i].trimAsciiStart.toString
    i := i + 1
    unless line.startsWith "attribute [" do continue
    let attrs := parseAttrs ((line.drop "attribute ".length).toString)
    -- Names run from after the closing `]` to the end of the indented continuation block.
    let mut names := ((line.splitOn "] ").getD 1 "").splitOn " " |>.toArray
    while hj : i < src.size do
      let cont := src[i]
      let trimmed := cont.trimAscii.toString
      if trimmed.isEmpty || trimmed.startsWith "--" || !(cont.startsWith " " || cont.startsWith "\t")
        then break
      names := names ++ (trimmed.splitOn " ").toArray
      i := i + 1
    for name in names do
      let name := name.trimAscii.toString
      unless name.isEmpty do
        for attr in attrs do
          out := out.push (name, attr)
  return out

/-- Collapse the pretty-printer's line breaks and indentation into single spaces. -/
def oneLine (s : String) : String :=
  " ".intercalate ((s.replace "\n" " ").splitOn " " |>.filter (!·.isEmpty))

/-- Everything after the module counter in one mangled private name: the components up to and
including the first purely numeric one are the `_private.<module>.<n>.` prefix. -/
def dropPrivatePrefix (s : String) : String :=
  let rec go : List String → List String
    | [] => []
    | c :: cs => if !c.isEmpty && c.all Char.isDigit then cs else go cs
  ".".intercalate (go (s.splitOn "."))

/-- Undo the mangling `pp.privateNames` prints. That option is on because the alternative is worse:
without it the delaborator renders a private constant as `Walk✝`, which is neither searchable nor
copy-pasteable, and two private constants sharing a leaf name become `Walk✝` and `Walk✝¹`. -/
def demanglePrivateNames (s : String) : String :=
  match s.splitOn "_private." with
  | [] => s
  | head :: rest => head ++ String.join (rest.map dropPrivatePrefix)

/-! ## Locally defined tactics

A project tactic nobody knows about is worse than no tactic: the proof gets written the long way,
and the tactic rots. They are scanned from source rather than curated by hand because their
docstrings are already the documentation — `sem_red` explains its own dispatch, `refines_match`
explains its own goal order — and a hand-kept list is one rename away from lying. -/

/-- Every `.lean` file beneath `dir`. -/
partial def leanFilesIn (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for entry in ← dir.readDir do
    if entry.fileName.startsWith "." then continue
    if ← entry.path.isDir then
      out := out ++ (← leanFilesIn entry.path)
    else if entry.fileName.endsWith ".lean" then
      out := out.push entry.path
  return out

/-- A tactic this project defines. -/
structure TacticFact where
  /-- The leading token, as written in the `macro`/`syntax` declaration. -/
  name : String
  /-- Project-relative source path. -/
  file : String
  /-- Line of the declaration. -/
  line : Nat
  /-- The declaration line itself, which spells out the tactic's arguments. -/
  spec : String
  /-- Its docstring, if it has one. -/
  doc : Option String

/-- Scan one file for tactic declarations and the docstrings immediately above them.

Only the leading quoted token is taken as the name, which is exact for `macro "sem_red"` and
approximate for the notation-shaped ones (`macro:1 t:tactic " <;> " …` reports `<;>`). That is
good enough: search runs over the docstring and the declaration line too. -/
def scanTactics (path : System.FilePath) (file : String) : IO (Array TacticFact) := do
  let src ← IO.FS.lines path
  let mut out := #[]
  let mut docLines : Array String := #[]
  let mut inDoc := false
  for i in [0 : src.size] do
    let some raw := src[i]? | continue
    let line := raw.trimAsciiStart.toString
    if inDoc then
      if line.endsWith "-/" then
        inDoc := false
        docLines := docLines.push ((line.dropEnd 2).trimAscii.toString)
      else docLines := docLines.push line
      continue
    if line.startsWith "/--" then
      let body := (line.drop 3).trimAscii.toString
      docLines := #[]
      if line.endsWith "-/" then
        docLines := #[(body.dropEnd 2).trimAscii.toString]
      else
        inDoc := true
        docLines := #[body]
      continue
    let isDecl :=
      (line.startsWith "macro " || line.startsWith "macro:" || line.startsWith "syntax ")
        && (line.splitOn ": tactic").length > 1
    if isDecl then
      -- The name is the first quoted token on the line.
      let afterQuote := line.dropWhile (· != '"') |>.drop 1
      let name := (afterQuote.takeWhile (· != '"')).trimAscii.toString
      unless name.isEmpty do
        out := out.push {
          name, file, line := i + 1
          spec := oneLine line
          doc := if docLines.isEmpty then none
                 else some (oneLine (" ".intercalate docLines.toList))
        }
      docLines := #[]
    else if !line.startsWith "@[" && !line.isEmpty then
      docLines := #[]
  return out

/-- Serialize a tactic as one compact JSON object, in the same shape the fact rows use so that
one index covers both. -/
def TacticFact.toJson (t : TacticFact) : Json :=
  Json.mkObj <|
    [("n", Json.str t.name), ("k", Json.str "tac"), ("f", Json.str t.file),
     ("l", Json.num t.line), ("t", Json.str t.spec), ("s", Json.str t.spec)]
    ++ (match t.doc with | some d => [("d", Json.str d)] | none => [])

/-! ## Facts -/

/-- One row of the database. Field names match the JSON keys the CLI reads. -/
structure Fact where
  /-- Fully qualified constant name, as the source spells it: a `private` declaration is recorded
  under its user-facing name, with `private` among its attributes. -/
  name : Name
  /-- `"thm"` for a source theorem, `"def"` for a definition or inductive predicate, `"field"` for
  a Prop-valued class field. -/
  kind : String
  /-- Declaring module. -/
  module : Name
  /-- Project-relative path of the declaring source file. -/
  file : String
  /-- Line of the declared name. -/
  line : Nat
  /-- Pretty-printed statement, on one line. -/
  type : String
  /-- The conclusion alone, with binders and hypotheses discharged. What a search result shows:
  the full statement of a lemma is mostly implicit-binder boilerplate. -/
  concise : String
  /-- How many hypotheses the lemma takes. -/
  hypCount : Nat
  /-- Conclusion key heads: the primary search key. -/
  keys : Array Name
  /-- Every informative constant in the conclusion. -/
  concl : Array Name
  /-- Every informative constant in the hypotheses. -/
  hyps : Array Name
  /-- Attributes as written. -/
  attrs : Array String
  /-- Docstring, collapsed to one line. -/
  doc : Option String

/-- Constants worth indexing, in first-seen order and without duplicates. -/
def informative (ns : Array Name) : Array Name :=
  (ns.filter λ n ↦ !isInternal n && !isPlumbing n).map userName

/-- The head symbols a reader would search a conclusion under.

The conclusion's own head comes first. When that head is a bare relation it says nothing on its
own, so the heads of its explicit arguments join it — `x ⊆ y` indexes under `HasSubset.Subset`
*and* under whatever `x` and `y` are built from. -/
def conclusionKeys (body : Expr) : Array Name := Id.run do
  let .const head _ := body.getAppFn | return #[]
  let mut keys := #[head]
  if bareRelations.contains head then
    for arg in body.getAppArgs do
      if let .const argHead _ := arg.getAppFn then
        if !isPlumbing argHead && !isInternal argHead && !uninformativeHeads.contains argHead
            && !keys.contains argHead then
          keys := keys.push argHead
  return keys

/-- Build a fact from a constant, given what its source window says. -/
def mkFact (n : Name) (ci : ConstantInfo) (m : Name) (line : Nat)
    (src : SrcInfo) : MetaM Fact := do
  let pp (e : Expr) : MetaM String :=
    withOptions (λ o ↦ (o.setBool `pp.unicode.fun true).setBool `pp.privateNames true) do
      return demanglePrivateNames (oneLine ((← ppExpr e).pretty (width := 1000)))
  let (hyps, concl, keys, concise, hypCount) ← forallTelescope ci.type λ binders body ↦ do
    let hyps ← binders.foldlM (init := (∅ : NameSet)) λ acc binder ↦ do
      return (← inferType binder).getUsedConstants.foldl NameSet.insert acc
    let hypCount ← binders.foldlM (init := 0) λ acc binder ↦ do
      return if (← isProp (← inferType binder)) then acc + 1 else acc
    let concl := body.getUsedConstants.foldl NameSet.insert (∅ : NameSet)
    return (hyps, concl, conclusionKeys body, ← pp body, hypCount)
  let type ← pp ci.type
  return {
    name := userName n
    kind := if src.isTheorem then "thm" else if src.isDefinition then "def" else "field"
    module := m
    file := modPath m
    line, type, hypCount
    -- A definition's conclusion is its result type, which for a predicate is the word `Prop`. Its
    -- signature is what a reader wants, and its own name is the key they will search under.
    concise := if src.isDefinition then type else concise
    keys := if src.isDefinition then #[userName n] else informative keys
    concl := informative concl.toArray
    hyps := informative hyps.toArray
    -- Whether a fact is reachable from another file is part of what it is: a `private` lemma is
    -- only usable through `import all`, and finding one without being told that wastes a search.
    attrs := if isPrivateName n then src.attrs.push "private" else src.attrs
    doc := src.doc.map oneLine
  }

/-- Serialize a fact as one compact JSON object. -/
def Fact.toJson (f : Fact) : Json :=
  let names (ns : Array Name) : Json := Json.arr (ns.map λ n ↦ Json.str n.toString)
  Json.mkObj <|
    [("n", Json.str f.name.toString), ("k", Json.str f.kind),
     ("m", Json.str f.module.toString), ("f", Json.str f.file),
     ("l", Json.num f.line), ("t", Json.str f.type),
     ("s", Json.str f.concise), ("H", Json.num f.hypCount),
     ("K", names f.keys), ("c", names f.concl), ("h", names f.hyps),
     ("a", Json.arr (f.attrs.map Json.str))]
    ++ (match f.doc with | some d => [("d", Json.str d)] | none => [])

/-- Fold each file's standalone `attribute` commands into the facts that file declares. -/
def applyAttributeCommands (facts : Array Fact) : IO (Array Fact) := do
  let mut byFile : Std.HashMap String (Array (String × String)) := {}
  for file in facts.map (·.file) do
    unless byFile.contains file do
      byFile := byFile.insert file (← scanAttributeCommands file)
  return facts.map λ f ↦
    let extra := (byFile.getD f.file #[]).filterMap λ (name, attr) ↦
      if f.name.toString == name || f.name.toString.endsWith ("." ++ name) then some attr else none
    { f with attrs := f.attrs ++ extra.filter (!f.attrs.contains ·) }

/-! ## Driver -/

/-- Every tactic declared under a local root, in path order. -/
def collectTactics (roots : NameSet) : IO (Array TacticFact) := do
  let mut out := #[]
  for entry in ← System.FilePath.readDir "." do
    let stem := if entry.fileName.endsWith ".lean"
                then entry.fileName.dropEnd 5 |>.toString else entry.fileName
    unless roots.contains (Name.mkSimple stem) do continue
    let paths ← if ← entry.path.isDir then leanFilesIn entry.path else pure #[entry.path]
    for path in paths do
      let file := path.toString.stripPrefix "./"
      out := out ++ (← scanTactics path file)
  return out.qsort λ a b ↦ if a.file == b.file then a.line < b.line else a.file < b.file

/-- Collect every local fact from an imported environment. -/
def collect (env : Environment) (roots : NameSet) : MetaM (Array Fact) := do
  let mut facts := #[]
  for (n, ci) in env.constants.toList do
    unless ci matches .thmInfo _ | .defnInfo _ | .inductInfo _ | .opaqueInfo _ do continue
    if isInternal n then continue
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless roots.contains m.getRoot do continue
    -- Auto-generated constants carry no declaration range, which is most of the filtering.
    let some range ← findDeclarationRanges? n | continue
    let nameLine := range.selectionRange.pos.line
    let src ← scanSource (modPath m) range.range.pos.line nameLine (userName n).getString!
    -- A field is a projection, which is a theorem exactly when the field is `Prop`-valued; the
    -- non-`Prop` projections a `structure` also generates are not facts and stay out.
    let keep := if ci matches .thmInfo _ then src.isTheorem || src.isField else src.isDefinition
    if keep then
      facts := facts.push (← mkFact n ci m nameLine src)
  let tagged ← applyAttributeCommands facts
  return tagged.qsort λ a b ↦
    if a.file == b.file then a.line < b.line else a.file < b.file

/-- `enableInitializersExecution` is `unsafe`, and loading environment extensions needs it: the
attribute and declaration-range tables this script reads are populated by module initializers. -/
unsafe def main (args : List String) : IO Unit := do
  let out := args.headD ".claude/facts/lemmas.jsonl"
  let roots ← localRoots
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Fugue }] {} (loadExts := true)
  let facts ← Prod.fst <$>
    (collect env roots |>.run' : CoreM (Array Fact)).toIO
      { fileName := "<DumpFacts>", fileMap := default } { env }
  let tactics ← collectTactics roots
  if let some dir := (System.FilePath.mk out).parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile out (String.join
    (facts.toList.map (λ f ↦ f.toJson.compress ++ "\n")
      ++ tactics.toList.map (λ t ↦ t.toJson.compress ++ "\n")))
  let theorems := facts.filter (·.kind == "thm") |>.size
  let definitions := facts.filter (·.kind == "def") |>.size
  let fields := facts.size - theorems - definitions
  let files := facts.foldl (init := (∅ : NameSet)) (λ s f ↦ s.insert (Name.mkSimple f.file))
  let documented := (facts.filter (·.doc.isSome)).size + (tactics.filter (·.doc.isSome)).size
  let total := facts.size + tactics.size
  IO.println s!"{total} facts ({theorems} theorems, {definitions} definitions, \
    {fields} class fields, {tactics.size} tactics) from {files.size} files, \
    {documented} documented -> {out}"
