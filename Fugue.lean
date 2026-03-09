import Cli.Basic
import Extra.Monad
import Core.Pretty
import Common.Errors
import Parser_
import Desugarer
import Guarded2Network
import Network2Go
-- import PlusCalCompiler.Passes.SurfaceToGuarded
import ProgressBar.Spinner
import ProgressBar.Spinners

-- run_elab do
--   let env ← Lean.MonadEnv.getEnv
--   let thisMod := env.header.mainModule
--   let graph := env.importGraph.transitiveReduction
--   let graph := graph.insert thisMod (graph.toArray.map Prod.fst)

--   Lean.logInfo <| "digraph {\nroot=" ++ s!"\"{thisMod}\"\n" ++ "node[fontsize=10, shape=point]\n" ++ graph.fold (λ acc k v ↦ s!"{acc}" ++ "\nsubgraph {\n" ++ s!"{Std.Format.joinSep (v.toList.map (λ v ↦ s!"\"{k}\" -> \"{v}\"")) "\n"}\n" ++ "}") "" ++ "\n}"


open Cli
open Colorized (Colorized)

private inductive Input : Type
  | path : System.FilePath → Input
  | stdin
  deriving Inhabited

instance : ToString Input where
  toString
    | .path p => p.fileName.getD ""
    | .stdin => "stdin"

instance : ParseableType System.FilePath where
  name := "FilePath"
  parse? str := ↑↑str

instance : ParseableType Input where
  name := "FilePath|-"
  parse?
    | "-" => ↑Input.stdin
    | str => ↑(Input.path ↑str)

private structure Option' where
  name : String
  value : Option String

instance : ToString Option' where
  toString opt := match opt.value with
    | none => opt.name
    | some value => s!"{opt.name}={value}"

instance : ParseableType Option' where
  name := "<name>[=<value>]"
  parse? str := match str.splitOn "=" with
    | [name, value] => some { name, value := ↑value }
    | [name] => some { name, value := none }
    | _ => none

/--
  Debugging options.
-/
structure DebugOptions where
  /-- The path to the directory where to dump files. -/
  dumpDir : String := ".pcvc"
  /-- Do we dump the internal Guarded PlusCal? -/
  dumpGuarded : Bool := false
  /-- Do we dump the internal Network PlusCal? -/
  dumpNetwork : Bool := false
  /-- Do we dump the internal GoCal? -/
  dumpGoCal : Bool := false

def DebugOptions.from (args : Array Option') : IO DebugOptions := do
  let mut args' : Std.HashMap String (Option String) := ∅
  let mut b := false
  for ⟨k, v⟩ in args do
    if !k.isEmpty then
      ⟨⟨args'⟩, b⟩ := Batteries.HashMap.insert' args' k v
      if b then
        throw ↑s!"Debugging option {k} specified multiple times."

  let opts ← args'.foldM (init := ({} : DebugOptions)) λ opts k v ↦ match k, v with
    | "dumpdir", some path => pure { opts with dumpDir := path }
    | k@"dumpdir", none => throw ↑s!"Missing path argument for debugging option '{k}'"
    | "dump-guarded", none => pure { opts with dumpGuarded := true }
    | k@"dump-guarded", some _ --=> throw ↑s!"Unexpected value for debugging flag '{k}'"
    | k@"dump-network", some _
    | k@"dump-gocal", some _ => throw ↑s!"Unexpected value for debugging flag '{k}'"
    | "dump-network", none => pure { opts with dumpNetwork := true }
    | "dump-gocal", none => pure { opts with dumpGoCal := true }
    | k, v => throw ↑s!"unknown debugging {if v.isSome then "option" else "flag"} '{k}'"
  return opts

/--
  Output a compiler error on `stderr` and exit immediately with an exit code of `1`.
-/
@[noinline, specialize]
private def printErrorAndExit {α β ε} [Colorized β] [ToString β] [CompilerDiagnostic ε β] (err : ε) (lines : List String.Slice) : IO α := do
  IO.eprintln <| CompilerDiagnostic.pretty err lines
  IO.Process.exit 1

-- /--
--   Read a `stream` until the first EOF has been reached and return the content as a single string.
--   Note that some streams may not be finished when the first EOF is reached, so we may want to call this
--   function until the stream is closed and its buffer is empty.
-- -/
-- private partial def IO.FS.Stream.readToEnd (stream : IO.FS.Stream) : IO String := do
--   let mut output := ""
--   let mut input ← stream.getLine
--   while input != "" do
--     output := output ++ input
--     input ← stream.getLine
--   return output

instance : Alternative IO where
  failure := throw ↑"failure"
  orElse act₁ act₂ := try act₁ catch _ => act₂ ()

/-- Cancel the given `spinner` with a persistent error message. -/
private abbrev Spinner.fail (spinner : Spinner) (msg : String) : IO Unit := do
  spinner.cancel (.persist "💥" msg)

/-- Cancel the given `spinner` with a persistent success message. -/
private abbrev Spinner.success (spinner : Spinner) (msg : String) : IO Unit := do
  spinner.cancel (.persist "🎉" msg)

/-- Make a new spinner with a specific style on `stderr`. -/
private abbrev Spinner.mk (msg : String) : IO Spinner := do
  Spinner.newOnStream Spinners.dotsCircle msg (← IO.getStderr)

private abbrev withSpinner {α : Type} (msg : String) (act : Spinner → IO α) : IO α := do
  let spinner ← Spinner.mk msg
  let res ← act spinner
  if !(← spinner.isCancelled) then
    spinner.cancel .erase
  return res

private def dumpFormatToFile.{u} {α : Type u} [Std.ToFormat α] (x : α) (path : System.FilePath) (width : Nat := 120) : IO Unit := do
  unless ← path.pathExists do
    if let some parent := path.parent then
      IO.FS.createDirAll parent
  IO.FS.writeFile path (Std.format x |>.pretty (width := width))

-- TODO: move CLI parsing (and flags) into a separate directory

private partial def runCli (p : Parsed) : IO UInt32 := do
  -- Get debugging options, if there are any
  let dopts : DebugOptions ← match p.flag? "dopt" with
    | none => pure {}
    | some f => DebugOptions.from <| f.as! (Array Option')

  let inputFile := p.positionalArg! "input" |>.as! Input

  -- Parsing file and annotations
  let (mod, lines) ← withSpinner "Parsing TLA⁺ file…" λ spinner ↦ do
    let source ← match inputFile with
      | .path inputFile =>
        guardM (inputFile.pathExists.toIO) <|> do
          spinner.fail s!"File '{inputFile}' does not exist."
          IO.Process.exit 1
        IO.FS.readFile inputFile
      | .stdin =>
        IO.getStdin >>= IO.FS.Stream.readToEnd
    -- Better compute this ahead of time, even if it is not needed, than having to compute it possibly several times
    -- (e.g. in the presence of warnings)
    let lines := source.split (· == '\n') |>.toList

    let tks ← match SurfaceTLAPlus.Lexer.lexModule source with
      | .inl e => do
        let _ : ToString Char := ⟨λ c ↦ s!"'{c}'"⟩
        spinner.fail "Failed to parse TLA⁺ file."
        printErrorAndExit e lines
      | .inr mod => pure mod

    let mod ← match SurfaceTLAPlus.Parser.parseModule tks with
      | .inl e =>
        let _ {α} [ToString α] : ToString (Located' α) := ⟨λ x ↦ toString x.data⟩
        spinner.fail "Failed to parse TLA⁺ file."
        printErrorAndExit e lines
      | .inr mod =>
        pure mod

    spinner.setTitle "Parsing annotations…"
    let mod ← match resolveAnnotations mod with
      | .error e =>
        spinner.fail "Failed to parse annotations."
        printErrorAndExit e lines
      | .ok mod =>
        spinner.success "Finished parsing TLA⁺ file."
        pure (mod, lines)

  if mod.pcalAlgorithm.isNone then
    IO.eprintln "Failed to find a valid PlusCal algorithm within the given TLA+ module.
Please make sure that it is located at the start of a multiline comment."
    return 1

  -- TODO: Import resolving (recursive parsing etc?)

  let mod ← withSpinner "Removing syntax sugar…" λ spinner ↦ do
    spinner.setTitle "Removing syntax sugar in expressions…"
    let mod ← match mod.runDesugarer with
      | .error e =>
        spinner.fail "Failed to remove syntax sugar."
        printErrorAndExit e lines
      | .ok mod =>
        let mod ← match mod.pcalAlgorithm with
          | .some alg =>
            spinner.setTitle "Removing syntax sugar in algorithm…"

            -- TODO: translate `alg` to CorePlusCal
            pure mod
          | .none => pure mod

        spinner.success "Finished removing syntax sugar."
        pure mod

  -- TODO: Annotation checking

  -- Translation to Guarded PlusCal
  -- let alg ← withSpinner "Translating to Guarded PlusCal…" λ spinner ↦ do
  --   let alg ← match SurfacePlusCal.Algorithm.toGuarded.run mod.data.pcalAlgorithm.get! with
  --     | .error e =>
  --       spinner.fail "Failed translating to Guarded PlusCal."
  --       printErrorAndExit e lines
  --     | .ok ⟨mod, warns⟩ =>
  --       spinner.success "Finished translating to Guarded PlusCal."
  --       for warn in warns do IO.eprintln <| CompilerDiagnostic.pretty warn lines
  --       pure mod


  -- if dopts.dumpGuarded then
  --   let _ {α : Type _} [Std.ToFormat α] : Std.ToFormat (Located α) := ⟨λ ⟨pos, x⟩ ↦ f!"(* {pos} *) {x}"⟩
  --   -- pretty print `alg` in file `$CWD/{dopts.dumpDir}/{inputFile}-guarded.pprint`
  --   dumpFormatToFile alg ((← IO.currentDir) / dopts.dumpDir / s!"{inputFile}-guarded.pprint")
  --   pure ()

  -- -- Translation to Network PlusCal
  -- let alg ← withSpinner "Translating to Network PlusCal…" λ spinner ↦ do
  --   let alg := alg <&> λ alg ↦ alg.toNetwork "inbox"
  --   spinner.success "Finished translating to Network PlusCal."
  --   pure alg

  -- if dopts.dumpNetwork then
  --   let _ {α : Type _} [Std.ToFormat α] : Std.ToFormat (Located α) := ⟨λ ⟨pos, x⟩ ↦ f!"(* {pos} *) {x}"⟩
  --   -- pretty print `alg` in file `$CWD/{dopts.dumpDir}/{inputFile}-guarded.pprint`
  --   dumpFormatToFile alg ((← IO.currentDir) / dopts.dumpDir / s!"{inputFile}-network.pprint")
  --   pure ()

  -- -- Translation to Go
  -- let fns ← withSpinner "Compiling to Go…" λ spinner ↦
  --   try do
  --     let fns := traverse (·.toGoCal) alg

  --     -- Pretty print GoCal into file/onto stdout
  --     let pkgName := p.flag? "package" |>.elim "main" (·.as! String)
  --     let header := s!"package {pkgName}\n\nimport . \"github.com/mesabloo/distpcal-compiler/lib\"\n\n"

  --     let _ {α : Type _} [Std.ToFormat α] : Std.ToFormat (List α) := ⟨(.joinSep · (.line ++ .line))⟩
  --     let _ {α : Type _} [Std.ToFormat α] : Std.ToFormat (Located α) := {
  --       format := λ ⟨pos, x⟩ ↦ if pos = default then f!"{x}" else f!"/* {pos} */ {x}"
  --     }

  --     let _ : Std.ToFormat CoreTLAPlus.Typ.{0} := GoCal.instToFormatTyp
  --     let _ : Std.ToFormat (CoreTLAPlus.Expression.{0} CoreTLAPlus.Typ) := GoCal.instToFormatExpression

  --     let maxDepth := 60 -- 120
  --     if let .some path := p.flag? "output" |>.map (·.as! System.FilePath) then
  --       spinner.setTitle s!"Outputting Go file (to '{path.withExtension "go"}')…"
  --       let dir ← (if path.isAbsolute then path.parent else ("." / path).parent)
  --                 |>.getDM do throw ↑"Output path must be a file to be created, not a directory."
  --       guardM (dir.pathExists.toIO) <|> do
  --         throw ↑s!"Directory '{dir}' does not exist."
  --       IO.FS.withFile (path.withExtension "go") .write λ handle ↦ do
  --         let stream := IO.FS.Stream.ofHandle handle
  --         stream.putStrLn header
  --         stream.putStrLn <| (Std.format fns) |>.pretty (width := maxDepth)
  --         stream.flush
  --       spinner.success "Finished outputting Go file."
  --     else
  --       spinner.setTitle "Outputting Go file (to stdout)…"
  --       spinner.success "Finished outputting Go file."
  --       let stream ← IO.getStdout
  --       stream.putStrLn header
  --       stream.putStrLn <| (Std.format fns) |>.pretty (width := maxDepth)
  --       stream.flush

  --     pure fns
  --   catch e =>
  --     spinner.fail e.toString
  --     IO.Process.exit 1


  return 0

private def cli : Cmd := `[Cli|
  "fugue" VIA runCli; ["1.0.0"]
  "Fugue ─ A verified compiler for Distributed PlusCal targeting Go"

  FLAGS:
    o, output : System.FilePath; "The file to output code to. If not specified, the code will be printed on the standard output.\nThe file extension will be replaced no matter what, so it is not necessary to specify it."
    p, package : String; "The package name for the output file.\nOnly applicable with the Go target."
    -- NOTE: Sometimes in the future, perhaps a flag -t|--target to specify which language to target.
    D, dopt : Array Option'; "Debugging options."
    -- TODO: Warning flags (e.g. -Werror)
    -- TODO: -I to specify include directories to lookup TLA⁺ files (for imports)

  ARGS:
    input : Input; "The input TLA+ file containing the (Distributed) PlusCal algorithm to compile, or `-` to read from the standard input."
]

def main (args : List String) : IO UInt32 := cli.validate args
