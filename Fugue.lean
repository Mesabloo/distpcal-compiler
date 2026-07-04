import Cli.Basic
import Common.Flags
import Common.Errors
import Parser_.TLAPlus
import Parser_.Annotations
import Desugarer.TLAPlus
import Desugarer.PlusCal
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
private def knownDebugOptions : Array String := #["dump-tokens", "dump-cst", "dump-desugared", "dump-dir"]

/-- Default value of `-d dump-dir=<path>`. -/
private def defaultDumpDir : System.FilePath := ".fugue/debug"

/-- `-f<name>` toggles recognized so far — extend as later phases add more. -/
private def knownFeatures : Array String := #["no-color"]

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

private def withSpinner {α : Type} (msg : String) (act : Spinner → IO α) : IO α := do
  let spinner ← Spinner.newOnStream Spinners.dotsCircle msg (← IO.getStderr)
  let res ← act spinner
  unless ← spinner.isCancelled do
    spinner.cancel .erase
  return res

/-- Output a compiler error on `stderr` and exit immediately with an exit code of `1`. -/
@[noinline, specialize]
private def printErrorAndExit {α β ε} [Colorized β] [ToString β] [CompilerDiagnostic ε β] (err : ε) (lines : List String.Slice) (colored : Bool) : IO α := do
  IO.eprintln <| CompilerDiagnostic.pretty err lines colored
  IO.Process.exit 1

/-- Write a `-d dump-*` debugging artifact to `dir/name`, creating `dir` if needed. -/
private def dumpToFile (content : String) (dir : System.FilePath) (name : String) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / name) content

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

private def runCli (p : Parsed) : IO UInt32 := do
  validateAndSetFlags p

  let colored ← not <$> FlagsEnv.getFeatureFlag "no-color"
  let dumpDir : System.FilePath := (← FlagsEnv.getDebugOption "dump-dir").elim defaultDumpDir (↑·)

  let input := p.positionalArg! "input" |>.as! Input
  let dumpName := match input with
    | .path path => path.fileName.getD (toString path)
    | .stdin => "stdin"

  let source ← withSpinner "Reading input…" λ spinner ↦ do
    let source ← match input with
      | .path path =>
        unless ← path.pathExists do
          spinner.fail s!"File '{path}' does not exist."
          IO.Process.exit 1
        IO.FS.readFile path
      | .stdin => (← IO.getStdin).readToEnd
    spinner.success s!"Read {source.utf8ByteSize} bytes from '{input}'."
    return source
  let lines := source.split (· == '\n') |>.toList

  let tokens ← withSpinner "Lexing TLA⁺ file…" λ spinner ↦ do
    match SurfaceTLAPlus.Lexer.lexModule source with
    | .inl e =>
      let _ : ToString Char := ⟨λ c ↦ s!"'{c}'"⟩
      spinner.fail "Failed to lex TLA⁺ file."
      printErrorAndExit e lines colored
    | .inr tokens =>
      spinner.success s!"Lexed {tokens.size} tokens."
      return tokens

  if ← FlagsEnv.getDebugFlag "dump-tokens" then
    dumpToFile (reprStr tokens) dumpDir s!"{dumpName}-tokens"

  let (mod, warnings) ← withSpinner "Parsing TLA⁺ module…" λ spinner ↦ do
    match SurfaceTLAPlus.Parser.parseModule tokens with
    | .inl e =>
      let _ {α} [ToString α] : ToString (Located' α) := ⟨λ x ↦ toString x.data⟩
      spinner.fail "Failed to parse TLA⁺ module."
      printErrorAndExit e lines colored
    | .inr (mod, warnings) =>
      spinner.success s!"Parsed module '{mod.name}'."
      return (mod, warnings)

  if ← FlagsEnv.getDebugFlag "dump-cst" then
    dumpToFile (reprStr mod) dumpDir s!"{dumpName}-cst"

  for warning in warnings do
    if ← FlagsEnv.isWarningEnabled warning.name then
      IO.eprintln <| CompilerDiagnostic.pretty warning lines colored

  let mod ← match resolveAnnotations mod with
    | .error e => printErrorAndExit e lines colored
    | .ok mod => pure mod

  let mod ← withSpinner "Desugaring TLA⁺ expressions…" λ spinner ↦ do
    match mod.runDesugarer with
    | .error e =>
      spinner.fail "Failed to desugar TLA⁺ expressions."
      printErrorAndExit e lines colored
    | .ok mod =>
      match mod.checkTLAPlusAnnotations with
      | .error e =>
        spinner.fail "Failed to desugar TLA⁺ expressions."
        printErrorAndExit e lines colored
      | .ok mod =>
        spinner.success "Desugared TLA⁺ expressions."
        return mod

  if ← FlagsEnv.getDebugFlag "dump-desugared" then
    dumpToFile (reprStr mod) dumpDir s!"{dumpName}-desugared"

  let algo ← match mod.pcalAlgorithm with
    | none => pure none
    | some algo => withSpinner "Desugaring PlusCal algorithm…" λ spinner ↦ do
      match algo.runDesugarer with
      | .error e =>
        spinner.fail "Failed to desugar PlusCal algorithm."
        printErrorAndExit e lines colored
      | .ok algo =>
        match algo.runCheckPlusCalAnnotations with
        | .error e => printErrorAndExit e lines colored
        | .ok (algo, warnings) =>
          for warning in warnings do
            if ← FlagsEnv.isWarningEnabled warning.name then
              IO.eprintln <| CompilerDiagnostic.pretty warning lines colored
          spinner.success "Desugared PlusCal algorithm."
          return some algo

  if let some algo := algo then
    if ← FlagsEnv.getDebugFlag "dump-desugared" then
      dumpToFile (reprStr algo) dumpDir s!"{dumpName}-desugared-algorithm"

  IO.println s!"Fugue: desugared module '{mod.name}' (extends {mod.extends.length} module(s), \
{mod.declarations₁.length + mod.declarations₂.length} declaration(s), \
{if algo.isSome then "with" else "without"} an embedded PlusCal algorithm). \
The type checker (Phase 5) isn't implemented yet, so the pipeline stops here."
  return 0

private def cli : Cmd := `[Cli|
  "fugue" VIA runCli; ["0.1.0"]
  "Fugue — a verified compiler for Distributed PlusCal targeting Go and the Join Calculus."

  FLAGS:
    o, output : System.FilePath; "The file to output compiled code to. If omitted, code is printed to standard output."
    t, target : Target; "Which backend to target: `go` or `join`. Defaults to `go`."
    "I", "include" : Array System.FilePath; "Add a module search path. Repeat by comma-separating: `-I dir1,dir2`."
    d, debug : Array NamedOption; "Debugging options (dump-tokens, dump-cst, dump-desugared, dump-dir=<path> — defaults to `.fugue/debug`), comma-separated `name[=value]` pairs."
    f, feature : Array NamedOption; "Feature/config toggles, comma-separated `name[=value]` pairs."
    "W", warn : Array WarningToggle; "Per-warning control: `name` enables, `no-name` disables. Comma-separated."

  ARGS:
    input : Input; "The input TLA+ file to compile, or `-` to read from standard input."
]

/-- The `fugue` executable's entry point. -/
def main (args : List String) : IO UInt32 := cli.validate args
