import Cli.Basic
import Common.Flags
import ProgressBar.Spinner
import ProgressBar.Spinners

open Cli

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

/-- Collect `<name>[=<value>]` options into a map, rejecting a `name` given more than once. -/
private def NamedOption.toMap (kind : String) (opts : Array NamedOption) : IO (Std.HashMap String (Option String)) := do
  let mut map : Std.HashMap String (Option String) := {}
  for opt in opts do
    if map.contains opt.name then
      throw ↑s!"{kind} option '{opt.name}' specified multiple times."
    map := map.insert opt.name opt.value
  return map

/-- Collect `-W`'s toggles into a map, rejecting a `name` given more than once. -/
private def WarningToggle.toMap (toggles : Array WarningToggle) : IO (Std.HashMap String Bool) := do
  let mut map : Std.HashMap String Bool := {}
  for toggle in toggles do
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

private def runCli (p : Parsed) : IO UInt32 := do
  let debug ← NamedOption.toMap "debug" <| p.flag? "debug" |>.map (·.as! (Array NamedOption)) |>.getD #[]
  let features ← NamedOption.toMap "feature" <| p.flag? "feature" |>.map (·.as! (Array NamedOption)) |>.getD #[]
  let warnings ← WarningToggle.toMap <| p.flag? "warn" |>.map (·.as! (Array WarningToggle)) |>.getD #[]
  let output := p.flag? "output" |>.map (·.as! System.FilePath)
  let target := p.flag? "target" |>.map (·.as! Target) |>.getD .go
  let searchPath := p.flag? "include" |>.map (·.as! (Array System.FilePath)) |>.getD #[] |>.toList

  flagsRef.set { debug, features, warnings, output, target, searchPath }

  let input := p.positionalArg! "input" |>.as! Input

  withSpinner "Reading input…" λ spinner ↦ do
    let source ← match input with
      | .path path =>
        unless ← path.pathExists do
          spinner.fail s!"File '{path}' does not exist."
          IO.Process.exit 1
        IO.FS.readFile path
      | .stdin => (← IO.getStdin).readToEnd
    spinner.success s!"Read {source.utf8ByteSize} bytes from '{input}'."

  IO.println s!"Fugue: CLI wired, flags parsed, input read. The lexer/parser (Phase 3) isn't implemented yet, so the pipeline stops here."
  return 0

private def cli : Cmd := `[Cli|
  "fugue" VIA runCli; ["0.1.0"]
  "Fugue — a verified compiler for Distributed PlusCal targeting Go and the Join Calculus."

  FLAGS:
    o, output : System.FilePath; "The file to output compiled code to. If omitted, code is printed to standard output."
    t, target : Target; "Which backend to target: `go` or `join`. Defaults to `go`."
    "I", "include" : Array System.FilePath; "Add a module search path. Repeat by comma-separating: `-I dir1,dir2`."
    d, debug : Array NamedOption; "Debugging options (AST dumps, timing, …), comma-separated `name[=value]` pairs."
    f, feature : Array NamedOption; "Feature/config toggles, comma-separated `name[=value]` pairs."
    "W", warn : Array WarningToggle; "Per-warning control: `name` enables, `no-name` disables. Comma-separated."

  ARGS:
    input : Input; "The input TLA+ file to compile, or `-` to read from standard input."
]

/-- The `fugue` executable's entry point. -/
def main (args : List String) : IO UInt32 := cli.validate args
