module

public import Cli.Basic
public import Common.Flags
import Common.Errors
public import Driver.Pipeline
import ProgressBar
import Colorized

public section

open Cli
open Colorized (Colorized)

/-- The input source: a file path, or `-` to read from standard input. -/
inductive Input : Type
  | path : System.FilePath → Input
  | stdin
  deriving Inhabited

@[no_expose]
instance : ToString Input where
  toString
    | .path p => toString p
    | .stdin => "-"

instance : ParseableType System.FilePath where
  name := "path"
  parse? str := some ↑str

instance : ParseableType Input where
  name := "path|-"
  parse?
    | "-" => some .stdin
    | str => some (.path ↑str)

/-- The `<name>[=<value>]` shape shared by `-d`/`-f`'s options. -/
structure NamedOption : Type where
  name : String
  value : Option String
  deriving Inhabited

instance : ParseableType NamedOption where
  name := "<name>[=<value>]"
  parse? str := match str.splitOn "=" with
    | [name, value] => some { name, value := some value }
    | [name] => some { name, value := none }
    | _ => none

/-- The `<name>` (enable) / `no-<name>` (disable) shape of `-W`'s per-warning toggles. -/
structure WarningToggle : Type where
  name : String
  enabled : Bool
  deriving Inhabited

instance : ParseableType WarningToggle where
  name := "<name>|no-<name>"
  parse? str :=
    if str.take 3 == "no-" then
      let name := str.drop 3 |>.toString
      if name.isEmpty then none else some { name, enabled := false }
    else if str.isEmpty then
      none
    else
      some { name := str, enabled := true }

instance : ParseableType Target where
  name := "go|join"
  parse?
    | "go" => some .go
    | "join" => some .join
    | _ => none

/-- `-d<name>` options recognized so far — extend as later phases add more dump points. -/
private def knownDebugOptions : Array String := #["dump-tokens", "dump-cst", "dump-desugared", "dump-typed", "dump-computable", "dump-guarded", "dump-network", "dump-go", "dump-dir"]

/-- `-f<name>` toggles recognized so far — extend as later phases add more. -/
private def knownFeatures : Array String := #["no-color", "no-progress"]

/-- `-W<name>` names recognized so far — matches every `ParserWarning.name`
(`Parser_/Common.lean`) and `DesugarWarning.name` (`Desugarer/Errors.lean`), extend likewise. -/
private def knownWarnings : Array String := #["fair", "duplicate-parameter"]

/-- `-X<name>[=<value>]` backend options. One table, not one per backend: an option a backend does
not understand is a mistake worth reporting either way, and the alternative is a table whose
contents depend on a flag parsed in the same pass.

`go-package` names the Go package the emitted file declares, defaulting to `main`. It is not a
`-f` toggle because it is a property of the *output*, not of how the compiler behaves; and not a
Go build tag, unlike the integer representation, because the compiler is what writes the
`package` clause. -/
private def knownTargetOptions : Array String := #["go-package"]

/-- Collect `<name>[=<value>]` options into a map, rejecting an unknown or duplicate `name`. -/
private def NamedOption.toMap (kind : String) (known : Array String) (opts : Array NamedOption) : IO (Std.HashMap String (Option String)) := do
  let mut map : Std.HashMap String (Option String) := {}
  for opt in opts do
    unless known.contains opt.name do
      throw ↑s!"unknown {kind} option '{opt.name}'. Known {kind} options: {String.intercalate ", " known.toList}."
    if map.contains opt.name then
      throw ↑s!"{kind} option '{opt.name}' specified multiple times."
    map := map.insert opt.name opt.value
  return map

/-- Collect `-W`'s toggles into a map, rejecting an unknown or duplicate `name`. -/
private def WarningToggle.toMap (known : Array String) (toggles : Array WarningToggle) : IO (Std.HashMap String Bool) := do
  let mut map : Std.HashMap String Bool := {}
  for toggle in toggles do
    unless known.contains toggle.name do
      throw ↑s!"unknown warning '{toggle.name}'. Known warnings: {String.intercalate ", " known.toList}."
    if map.contains toggle.name then
      throw ↑s!"warning '{toggle.name}' specified multiple times."
    map := map.insert toggle.name toggle.enabled
  return map

/-- Cancel the given `spinner` with a persistent error message. -/
private abbrev Spinner.fail (spinner : Spinner) (msg : String) : IO Unit :=
  spinner.cancel (.persist "💥" msg)

/-- Cancel the given `spinner` with a persistent success message. -/
private abbrev Spinner.success (spinner : Spinner) (msg : String) : IO Unit :=
  spinner.cancel (.persist "🎉" msg)

/-- A real animated `Spinner`, or a quiet stand-in when `-fno-progress` disables the animation
(e.g. output being piped/logged, where a `\r`-redrawing spinner is just noise) — `runCli` calls
`.log`/`.setTitle`/`.fail`/`.success` the same way either way. `.quiet` never spins up a `Spinner`
at all (no background task), rather than merely hiding one's output. -/
private inductive Progress : Type
  | spinner (s : Spinner)
  | quiet

/-- Print `line` as its own line — matches `Spinner.log`, minus the animation. -/
private def Progress.log : Progress → String → IO Unit
  | .spinner s, line => s.log line
  | .quiet, line => IO.eprintln line

/-- Update the current status — a no-op when `.quiet`, since there's nothing ongoing to label. -/
private def Progress.setTitle : Progress → String → IO Unit
  | .spinner s, title => s.setTitle title
  | .quiet, _ => pure ()

private def Progress.fail : Progress → String → IO Unit
  | .spinner s, msg => s.fail msg
  | .quiet, msg => IO.eprintln s!"💥 {msg}"

private def Progress.success : Progress → String → IO Unit
  | .spinner s, msg => s.success msg
  | .quiet, msg => IO.println s!"🎉 {msg}"

private def withProgress {α : Type} (flags : FlagsEnv) (msg : String) (act : Progress → IO α) : IO α := do
  if flags.features.contains "no-progress" then
    act .quiet
  else
    let spinner ← Spinner.newOnStream Spinners.dotsCircle msg (← IO.getStderr)
    let res ← act (.spinner spinner)
    unless ← spinner.isCancelled do
      spinner.cancel .erase
    return res

/--
  Parses every flag out of `p` (rejecting unknown/duplicate `-d`/`-f`/`-W` names and a
  valueless `-d dump-dir`, per `NamedOption.toMap`/`WarningToggle.toMap` above) into the
  `FlagsEnv` the compile runs under. The one place all CLI-flag validation happens; the
  resulting value is handed to `runPipelineIO`, which supplies it to every pass as a reader.
-/
private def validateFlags (p : Parsed) : IO FlagsEnv := do
  let debug ← NamedOption.toMap "debug" knownDebugOptions <| p.flag? "debug" |>.map (·.as! (Array NamedOption)) |>.getD #[]
  let features ← NamedOption.toMap "feature" knownFeatures <| p.flag? "feature" |>.map (·.as! (Array NamedOption)) |>.getD #[]
  let warnings ← WarningToggle.toMap knownWarnings <| p.flag? "warn" |>.map (·.as! (Array WarningToggle)) |>.getD #[]
  let targetOptions ← NamedOption.toMap "target" knownTargetOptions <| p.flag? "target-option" |>.map (·.as! (Array NamedOption)) |>.getD #[]
  let output := p.flag? "output" |>.map (·.as! System.FilePath)
  let target := p.flag? "target" |>.map (·.as! Target) |>.getD .go
  let searchPath := p.flag? "include" |>.map (·.as! (Array System.FilePath)) |>.getD #[] |>.toList

  match debug.get? "dump-dir" with
  | some none => throw ↑"debug option 'dump-dir' requires a path, e.g. -d dump-dir=.fugue/debug"
  | _ => pure ()

  match targetOptions.get? "go-package" with
  | some none => throw ↑"target option 'go-package' requires a name, e.g. -X go-package=pingpong"
  | _ => pure ()

  return { debug, features, warnings, targetOptions, output, target, searchPath }

private def runCli (p : Parsed) : IO UInt32 := do
  let flags ← validateFlags p

  let colored := !flags.features.contains "no-color"

  let input := p.positionalArg! "input" |>.as! Input
  let dumpName := match input with
    | .path path => path.fileName.getD (toString path)
    | .stdin => "stdin"
  let containingDir := match input with
    | .path path => path.parent
    | .stdin => none

  -- One spinner for the whole compile, Lean-`lake build`-style: just
  -- `[<done>/<discovered>] Running on module '<name>'…`, tracked here (not in
  -- `Driver/Modules.lean`, which only reports raw `onModuleProgress`/`onModuleEvent` facts).
  -- `<discovered>` grows as `EXTENDS` pulls in new modules; completed steps print as
  -- persisted lines via `Spinner.log` without interrupting the animation.
  withProgress flags "Reading input…" λ spinner ↦ do
    let source ← match input with
      | .path path =>
        unless ← path.pathExists do
          spinner.fail s!"File '{path}' does not exist."
          IO.Process.exit 1
        IO.FS.readFile path
      | .stdin => (← IO.getStdin).readToEnd
    -- spinner.log s!"Read {source.utf8ByteSize} bytes from '{input}'."
    let lines := source.split (· == '\n') |>.toList

    let discovered ← IO.mkRef (∅ : Std.HashSet String)
    -- A set, not a counter: `onModuleEvent` can fire more than once for the same name (`.built`
    -- once, `.replayed` for every later cache-hit reference), but must still count each module
    -- only once done.
    let done ← IO.mkRef (∅ : Std.HashSet String)

    -- A file's module must be named after the file; stdin has no filename, so nothing to check.
    let expectedName := match input with
      | .path path => path.fileStem
      | .stdin => none

    let result ← runPipelineIO flags source containingDir dumpName expectedName
      { onModuleEvent := λ name outcome ↦ do
          done.modify (·.insert name)
          let count := s!"[{(← done.get).size}/{(← discovered.get).size}]"
          let (dingbat, color, label) : String × Colorized.Color × String := match outcome with
            | .built hadWarnings => (if hadWarnings then "⚠" else "✔", if hadWarnings then .Yellow else .Green, "Built")
            | .replayed => ("✔", .Cyan, "Replayed")
            | .failed => ("✖", .Red, "Failed")
          spinner.log <| styleIf colored .Bold <| colorizeIf colored color s!"{dingbat} {count} {label} {name}"
        onModuleProgress := λ name ↦ do
          discovered.modify (·.insert name)
          spinner.setTitle s!"[{(← done.get).size}/{(← discovered.get).size}] Running on module '{name}'…"
        logLine := λ line ↦ spinner.log line }

    -- Warnings first, whether or not the compile then failed: they were reported before whatever
    -- error follows them.
    (result.renderWarnings flags lines).forM spinner.log

    -- A driver error ends the spinner with "Build failed."; a failure in a pass past the driver
    -- reports "Compilation failed." without touching the spinner. The third case is
    -- unreachable — an error always renders — and just falls through to the success path.
    match result.error, result.renderError flags lines with
    | some (.driver _), some line =>
      -- Print the error *before* ending the spinner: "Build failed" is the final word, not a
      -- banner ahead of the detail.
      spinner.log line
      spinner.fail "Build failed."
      IO.Process.exit 1
    | some _, some line =>
      IO.eprintln line
      IO.eprintln "Compilation failed."
      IO.Process.exit 1
    | _, _ => pure ()

    -- `-o` names a *file*, not a directory: a compile produces exactly one Go file. Everything
    -- lands in one package, and the only thing that could split it — a file per process — would
    -- buy nothing, since Go compiles a package as a unit and the declarations reference each
    -- other freely. Parent directories are created, so `-o build/spec.go` works without a mkdir.
    if let some code := result.go then
      match flags.output with
      | some path =>
        if let some dir := path.parent then
          IO.FS.createDirAll dir
        IO.FS.writeFile path code
        spinner.log s!"Wrote {path}."
      | none => IO.println code

    spinner.success s!"Build done ({(← done.get).size} job{if (← done.get).size = 1 then "" else "s"})."

    if let some summary := result.renderSummary then
      IO.eprintln summary
  return 0

/-- Directory layouts `fugue explain` accepts a diagnostics corpus in, relative to some ancestor of
the executable: the repository's own `docs/diagnostics`, and the `share/fugue/diagnostics` an
installed copy would use. -/
private def diagnosticsDocsLayouts : List System.FilePath :=
  ["docs" / "diagnostics", "share" / "fugue" / "diagnostics"]

/-- Where `fugue explain` looks for a diagnostic's markdown page. `$FUGUE_DOCS` overrides;
otherwise the search is anchored at the **executable**, walking up from its directory for the
first ancestor containing one of `diagnosticsDocsLayouts`. Anchored there and not at the working
directory, which has no reason to be anywhere near the compiler — in a checkout the binary sits at
`.lake/build/bin/fugue`, three levels under the `docs/` it wants. `none` if no corpus is
installed. -/
private def diagnosticsDocsDir : IO (Option System.FilePath) := do
  if let some dir ← IO.getEnv "FUGUE_DOCS" then
    return some ↑dir
  let mut dir := (← IO.appPath).parent
  -- Bounded: a filesystem root has itself as parent in some spellings, and this must terminate.
  for _ in [0:6] do
    let some here := dir | break
    for layout in diagnosticsDocsLayouts do
      if ← (here / layout).isDir then
        return some (here / layout)
    dir := here.parent
  return none

/-- One registry entry, as `fugue explain --list` prints it. -/
private def Diagnostics.Entry.listLine (entry : Diagnostics.Entry) : String :=
  let code := ToString.toString entry.code
  let stage := entry.stage.name
  s!"{code}{String.replicate (8 - code.length) ' '}{stage}{String.replicate (16 - stage.length) ' '}{entry.summary}"

/-- Print everything known about one code: its registry entry, then its `docs/diagnostics` page if
one has been written. Returns whether the code was a registered one. -/
private def explainCode (raw : String) : IO Bool := do
  let some code := DiagnosticCode.ofString? raw
    | IO.eprintln s!"error: '{raw}' is not a diagnostic code. Codes look like 'E0042' or 'W0003'."
      return false
  let some entry := Diagnostics.find? code
    | IO.eprintln s!"error: no diagnostic is registered under '{code}'. \
Run 'fugue explain --list' to see every code."
      return false
  IO.println s!"{code}: {entry.summary}"
  IO.println s!"Reported by: {entry.stage.name}"
  unless entry.warningName.isEmpty do
    IO.println s!"Suppress with: -Wno-{entry.warningName}"
  IO.println ""
  match ← diagnosticsDocsDir with
  | none =>
    IO.println "No diagnostics corpus was found next to this executable. Set $FUGUE_DOCS to point \
at one."
  | some dir =>
    let page := dir / s!"{code}.md"
    if ← page.pathExists then
      IO.println (← IO.FS.readFile page)
    else
      IO.println s!"No detailed page for {code} has been written yet ({page} does not exist)."
  return true

private def runExplain (p : Parsed) : IO UInt32 := do
  let codes := p.variableArgsAs! String
  if p.hasFlag "list" then
    Diagnostics.entries.forM λ entry ↦ IO.println entry.listLine
    return 0
  if codes.isEmpty then
    IO.eprintln "error: 'fugue explain' needs a diagnostic code, e.g. 'fugue explain E0042'. \
Use '--list' to see every code."
    return 1
  let mut ok := true
  for raw in codes do
    unless ← explainCode raw do
      ok := false
  return if ok then 0 else 1

private def compileCmd : Cmd := `[Cli|
  compile VIA runCli; ["0.1.0"]
  "Compile a TLA+ module."

  FLAGS:
    o, output : System.FilePath; "The file to output compiled code to. If omitted, code is printed to standard output."
    t, target : Target; "Which backend to target: `go` or `join`. Defaults to `go`."
    "I", "include" : Array System.FilePath; "Add a module search path. Repeat by comma-separating: `-I dir1,dir2`."
    d, debug : Array NamedOption; "Debugging options (dump-tokens, dump-cst, dump-desugared, dump-typed, dump-computable, dump-guarded, dump-network, dump-go, dump-dir=<path> — defaults to `.fugue/debug`), comma-separated `name[=value]` pairs."
    f, feature : Array NamedOption; "Feature/config toggles, comma-separated `name[=value]` pairs."
    "W", warn : Array WarningToggle; "Per-warning control: `name` enables, `no-name` disables. Comma-separated."
    "X", "target-option" : Array NamedOption; "Backend options (go-package=<name> — the package the emitted Go declares, default `main`), comma-separated `name[=value]` pairs."

  ARGS:
    input : Input; "The input TLA+ file to compile, or `-` to read from standard input."
]

private def explainCmd : Cmd := `[Cli|
  explain VIA runExplain; ["0.1.0"]
  "Explain a diagnostic code, e.g. 'fugue explain E0042'."

  FLAGS:
    l, list; "List every diagnostic code with its stage and summary."

  ARGS:
    ...codes : String; "The codes to explain."
]

private def cli : Cmd := `[Cli|
  "fugue" NOOP; ["0.1.0"]
  "Fugue — a verified compiler for Distributed PlusCal targeting Go and the Join Calculus."

  SUBCOMMANDS: compileCmd; explainCmd
]

/-- The `fugue` executable's entry point. -/
def main (args : List String) : IO UInt32 := cli.validate args

end
