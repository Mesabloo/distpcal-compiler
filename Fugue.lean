import Cli.Basic
import Common.Flags
import Common.Errors
import Parser_.TLAPlus
import Parser_.Annotations
import Desugarer.TLAPlus
import Desugarer.PlusCal
import Driver.Modules
import ProgressBar.Spinner
import ProgressBar.Spinners
import Colorized

open Cli
open Colorized (Colorized)

/-- The input source: a file path, or `-` to read from standard input. -/
private inductive Input : Type
  | path : System.FilePath → Input
  | stdin
  deriving Inhabited

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
private structure NamedOption : Type where
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
private structure WarningToggle : Type where
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
private def knownDebugOptions : Array String := #["dump-tokens", "dump-cst", "dump-desugared", "dump-typed", "dump-computable", "dump-dir"]

/-- `-f<name>` toggles recognized so far — extend as later phases add more. -/
private def knownFeatures : Array String := #["no-color", "no-progress"]

/-- `-W<name>` names recognized so far — matches every `ParserWarning.name`
(`Parser_/Common.lean`) and `DesugarWarning.name` (`Desugarer/Errors.lean`), extend likewise. -/
private def knownWarnings : Array String := #["fair", "duplicate-parameter"]

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

private def withProgress {α : Type} (msg : String) (act : Progress → IO α) : IO α := do
  if ← FlagsEnv.getFeatureFlag "no-progress" then
    act .quiet
  else
    let spinner ← Spinner.newOnStream Spinners.dotsCircle msg (← IO.getStderr)
    let res ← act (.spinner spinner)
    unless ← spinner.isCancelled do
      spinner.cancel .erase
    return res

/--
  Parses every flag out of `p` (rejecting unknown/duplicate `-d`/`-f`/`-W` names and a
  valueless `-d dump-dir`, per `NamedOption.toMap`/`WarningToggle.toMap` above) and
  populates `flagsRef` with the result. The one place all CLI-flag validation happens —
  every later stage of `runCli` just reads back through `FlagsEnv`'s typed accessors.
-/
private def validateAndSetFlags (p : Parsed) : IO Unit := do
  let debug ← NamedOption.toMap "debug" knownDebugOptions <| p.flag? "debug" |>.map (·.as! (Array NamedOption)) |>.getD #[]
  let features ← NamedOption.toMap "feature" knownFeatures <| p.flag? "feature" |>.map (·.as! (Array NamedOption)) |>.getD #[]
  let warnings ← WarningToggle.toMap knownWarnings <| p.flag? "warn" |>.map (·.as! (Array WarningToggle)) |>.getD #[]
  let output := p.flag? "output" |>.map (·.as! System.FilePath)
  let target := p.flag? "target" |>.map (·.as! Target) |>.getD .go
  let searchPath := p.flag? "include" |>.map (·.as! (Array System.FilePath)) |>.getD #[] |>.toList

  match debug.get? "dump-dir" with
  | some none => throw ↑"debug option 'dump-dir' requires a path, e.g. -d dump-dir=.fugue/debug"
  | _ => pure ()

  flagsRef.set { debug, features, warnings, output, target, searchPath }

/-- Print every warning in `warnings` not suppressed by `-Wno-<name>`, in one batch, only once
this module's outcome (`Built`/`Replayed`/`Failed`) is known — never interleaved before it. Each
call site passes only warnings collected for that module's own `compileModule` call; a
dependency's warnings are flushed separately by its own recursive call. `logLine` is pluggable
(defaults to `eprintln`) so `Fugue.lean` can route it through its spinner instead. -/
private def flushWarnings {m} [Monad m] [MonadReaderOf FlagsEnv m] [MonadLiftT IO m]
    (lines : List String.Slice) (colored : Bool) (warnings : List DriverWarning)
    (logLine : String → m Unit) : m Unit :=
  warnings.forM λ warning ↦ do
    if ← FlagsEnv.isWarningEnabled warning.name then
      logLine <| CompilerDiagnostic.pretty warning ((← warning.sourceLines).getD lines) colored

private def runCli (p : Parsed) : IO UInt32 := do
  validateAndSetFlags p

  let colored ← not <$> FlagsEnv.getFeatureFlag "no-color"

  let input := p.positionalArg! "input" |>.as! Input
  let dumpName := match input with
    | .path path => path.fileName.getD (toString path)
    | .stdin => "stdin"
  let containingDir := match input with
    | .path path => path.parent
    | .stdin => none

  -- One spinner for the whole compile, Lean-`lake build`-style: no per-pass titles
  -- ("Lexing…"/"Parsing…"/…) — just `[<done>/<discovered>] Running on module '<name>'…`, `<done>`
  -- and `<discovered>` tracked here (not in `Driver/Modules.lean` — it only reports raw
  -- `onModuleProgress`/`onModuleEvent` facts, this is presentation), `<discovered>` growing as
  -- `EXTENDS` pulls in modules not seen yet this run. Completed steps — reading the input, each
  -- `EXTENDS`ed module `Built`/`Replayed`, warnings — print as their own persisted lines via
  -- `Spinner.log` without interrupting the animation.
  let typedMod ← withProgress "Reading input…" λ spinner ↦ do
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
    -- A set, not a counter: `onModuleEvent` can fire more than once for the same name (e.g.
    -- `.built` the first time, `.replayed` for every later cache-hit reference to it), and this
    -- must still only ever count that module once done.
    let done ← IO.mkRef (∅ : Std.HashSet String)

    let (warnings, result) ← runM <| compileModule source containingDir dumpName
      (onModuleEvent := λ name outcome ↦ do
        done.modify (·.insert name)
        let count := s!"[{(← done.get).size}/{(← discovered.get).size}]"
        let (dingbat, color, label) : String × Colorized.Color × String := match outcome with
          | .built hadWarnings => (if hadWarnings then "⚠" else "✔", if hadWarnings then .Yellow else .Green, "Built")
          | .replayed => ("✔", .Cyan, "Replayed")
          | .failed => ("✖", .Red, "Failed")
        spinner.log <| styleIf colored .Bold <| colorizeIf colored color s!"{dingbat} {count} {label} {name}")
      (onModuleProgress := λ name ↦ do
        discovered.modify (·.insert name)
        spinner.setTitle s!"[{(← done.get).size}/{(← discovered.get).size}] Running on module '{name}'…")
      (logLine := λ line ↦ do spinner.log line)
    flushWarnings lines colored warnings (λ m ↦ spinner.log m)
    match result with
    | .error e =>
      -- Print the actual error *before* ending the spinner — `Compilation failed.` is the final
      -- word, not a banner ahead of the detail explaining it. `e` may have originated in an
      -- `EXTENDS`-ed dependency, not the main module read into `lines` above — render against
      -- the offending module's own source when it has one.
      spinner.log <| CompilerDiagnostic.pretty e ((← e.sourceLines).getD lines) colored
      spinner.fail "Compilation failed."
      IO.Process.exit 1
    | .ok typedMod =>
      spinner.success "Compilation succeeded."
      return typedMod

  IO.println s!"Fugue: type-checked module '{typedMod.name}' (extends {typedMod.extends.length} module(s), \
{typedMod.declarations₁.length + typedMod.declarations₂.length} declaration(s), \
{if typedMod.pcalAlgorithm.isSome then "with" else "without"} an embedded PlusCal algorithm). \
The rest of the pipeline (Phase 6 onward) isn't implemented yet, so it stops here."
  return 0

private def cli : Cmd := `[Cli|
  "fugue" VIA runCli; ["0.1.0"]
  "Fugue — a verified compiler for Distributed PlusCal targeting Go and the Join Calculus."

  FLAGS:
    o, output : System.FilePath; "The file to output compiled code to. If omitted, code is printed to standard output."
    t, target : Target; "Which backend to target: `go` or `join`. Defaults to `go`."
    "I", "include" : Array System.FilePath; "Add a module search path. Repeat by comma-separating: `-I dir1,dir2`."
    d, debug : Array NamedOption; "Debugging options (dump-tokens, dump-cst, dump-desugared, dump-typed, dump-computable, dump-dir=<path> — defaults to `.fugue/debug`), comma-separated `name[=value]` pairs."
    f, feature : Array NamedOption; "Feature/config toggles, comma-separated `name[=value]` pairs."
    "W", warn : Array WarningToggle; "Per-warning control: `name` enables, `no-name` disables. Comma-separated."

  ARGS:
    input : Input; "The input TLA+ file to compile, or `-` to read from standard input."
]

/-- The `fugue` executable's entry point. -/
def main (args : List String) : IO UInt32 := cli.validate args
