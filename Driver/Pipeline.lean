module

public import Driver.Modules
public import WellFormedness
public import Typed2Computable
public import Computable2Guarded
public import Guarded2Network

public section

/-!
  One compile, end to end, as a function: source text in, a `PipelineResult` out. No process exit,
  no printing, no progress animation — those belong to whoever is driving.

  `Driver/Modules.lean`'s `compileModule` only takes a module as far as type checking, and caches
  that; every pass after it (well-formedness, `Typed2Computable`, `Computable2Guarded`,
  `Guarded2Network`) runs once, here, against the checked main module rather than per `EXTENDS`
  dependency. Before this file existed that tail lived inline in `Fugue.lean`'s `runCli`,
  interleaved with spinner calls and `IO.Process.exit`, which meant a full compile could only be
  run by being the CLI. Two consumers need it now: the CLI, and `tests/regression`'s runner.
-/

/-- Where a compile is, or where it stopped. Ordered: `Stage.reached` and a failing stage are
compared against each other, so the constructor order is the pipeline order. -/
inductive Stage : Type
  /-- Source text read; nothing compiled yet. -/
  | read
  /-- Lexing (`Parser_/Tokens`). -/
  | lex
  /-- Parsing (`Parser_/TLAPlus.lean`). -/
  | parse
  /-- `@type`/`@mailbox`/`@parameter` annotation resolution. -/
  | annotation
  /-- Surface → Core desugaring. -/
  | desugar
  /-- `EXTENDS` resolution: locating, and recursively compiling, each dependency. -/
  | resolve
  /-- Type checking (`Elaborator`). -/
  | typeCheck
  /-- The well-formedness restrictions (`WellFormedness`). -/
  | wellFormedness
  /-- `Typed2Computable`. -/
  | computable
  /-- `Computable2Guarded`. -/
  | guarded
  /-- `Guarded2Network`. -/
  | network
  deriving DecidableEq, Repr, Inhabited, Ord

/-- The `-d dump-<name>`/expectation-file spelling of a stage. -/
def Stage.name : Stage → String
  | .read => "read" | .lex => "lex" | .parse => "parse" | .annotation => "annotation"
  | .desugar => "desugar" | .resolve => "resolve" | .typeCheck => "typecheck"
  | .wellFormedness => "wellformedness" | .computable => "computable" | .guarded => "guarded"
  | .network => "network"

instance : ToString Stage := ⟨Stage.name⟩

/-- Every stage, in pipeline order. -/
def Stage.all : List Stage :=
  [.read, .lex, .parse, .annotation, .desugar, .resolve, .typeCheck, .wellFormedness,
   .computable, .guarded, .network]

/-- The stage `s` by name, if `s` names one. -/
def Stage.ofName? (s : String) : Option Stage := Stage.all.find? (·.name == s)

/-- The stage immediately before `s`, i.e. the last one that must have completed for `s` to have
started. `.read` is its own predecessor: it is the floor, reached as soon as there is any source
text at all. -/
def Stage.predecessor : Stage → Stage
  | .read | .lex => .read
  | .parse => .lex
  | .annotation => .parse
  | .desugar => .annotation
  | .resolve => .desugar
  | .typeCheck => .resolve
  | .wellFormedness => .typeCheck
  | .computable => .wellFormedness
  | .guarded => .computable
  | .network => .guarded

/-- Did a compile that reached `self` get at least as far as `target`? A plain `Bool` function
rather than an `LE`/`Decidable` instance pair: comparing two stages is a question about pipeline
progress, and nothing here wants order-class machinery. -/
def Stage.reaches (self target : Stage) : Bool := compare self target != .lt

/-- Any way a compile can fail, from any stage. One type so a caller handles one thing;
`PipelineError.stage` recovers where it came from. -/
inductive PipelineError : Type
  /-- Anything up to and including type checking (`Driver/Modules.lean`). -/
  | driver (e : DriverError)
  /-- A well-formedness restriction. -/
  | wellFormedness (e : WellFormednessError)
  /-- `Typed2Computable`. -/
  | computable (e : ComputableError)
  /-- `Computable2Guarded`. -/
  | guarded (e : GuardedError)
  /-- `Guarded2Network`. -/
  | network (e : G2NError)

/-- Which stage produced this error. The driver's own error type already distinguishes its
internal stages, so this is total and exact rather than a guess from message text. -/
def PipelineError.stage : PipelineError → Stage
  | .driver (.lex ..) => .lex
  | .driver (.parse ..) => .parse
  | .driver (.annotation ..) => .annotation
  | .driver (.desugar ..) => .desugar
  | .driver (.moduleNotFound ..) | .driver (.ambiguousModule ..) | .driver (.cyclicExtends ..) =>
    .resolve
  | .driver (.typeCheck ..) => .typeCheck
  | .wellFormedness _ => .wellFormedness
  | .computable _ => .computable
  | .guarded _ => .guarded
  | .network _ => .network

/-- Rendered form of `err`, against the source lines it belongs to: a driver error renders against
its own module's lines (an error inside an `EXTENDS`-ed dependency is not about the main module),
looked up in `sources`; everything past the driver only ever concerns the main module, so it
renders against `mainLines`. Pure — rendering a diagnostic needs no `IO`. -/
def PipelineError.render (sources : SourceRegistry) (mainLines : List String.Slice)
    (colored : Bool) : PipelineError → String
  | .driver e => CompilerDiagnostic.pretty e ((DriverError.sourceLines sources e).getD mainLines) colored
  | .wellFormedness e => CompilerDiagnostic.pretty e mainLines colored
  | .computable e => CompilerDiagnostic.pretty e mainLines colored
  | .guarded e => CompilerDiagnostic.pretty e mainLines colored
  | .network e => CompilerDiagnostic.pretty e mainLines colored

/-- A compile's non-fatal diagnostics. Every pass past the driver reports at `MonadDiagnostic
Empty ε`, i.e. cannot warn at all, so a warning is always a `DriverWarning` — this is an `abbrev`
rather than a one-constructor wrapper to say exactly that, and becomes a real sum the day some
later pass grows a warning. -/
abbrev PipelineWarning := DriverWarning

/-- Everything one compile produced: its diagnostics, how far it got, the sources it read (needed
to render those diagnostics), and each stage's output for whoever wants to inspect or dump it.
An artifact is `none` when its stage never ran — either because the compile failed earlier, or
because the module has no PlusCal algorithm, in which case there is nothing for
`Computable2Guarded` onward to do and `reached` stops at `.computable`. -/
structure PipelineResult : Type where
  /-- Warnings, in the order they were reported. Present whether or not the compile then failed. -/
  warnings : List PipelineWarning := []
  /-- The fatal error, if the compile failed. -/
  error : Option PipelineError := none
  /-- The last stage that completed. -/
  reached : Stage := .read
  /-- Every module's source by `moduleId`, for rendering. -/
  sources : SourceRegistry := {}
  /-- The checked module. -/
  typed : Option TypedModule := none
  /-- `Typed2Computable`'s output. -/
  computable : Option (ComputableTLAPlus.Module ComputablePlusCal.Algorithm ComputableTLAPlus.Typ) := none
  /-- `Computable2Guarded`'s output. -/
  guarded : Option ComputableGuardedPlusCal.Algorithm := none
  /-- `Guarded2Network`'s output. -/
  network : Option ComputableNetworkPlusCal.Algorithm := none

/-- Did the compile succeed? -/
def PipelineResult.succeeded (r : PipelineResult) : Bool := r.error.isNone

/-- What the driver reports as it goes. Plain `IO` actions: a caller drives a spinner, a test
runner collects them into a list, and neither needs to know the driver's monad. -/
structure PipelineHooks : Type where
  /-- A module finished (or failed). -/
  onModuleEvent : String → ModuleOutcome → IO Unit := λ _ _ ↦ pure ()
  /-- Work started, or resumed, on a module. -/
  onModuleProgress : String → IO Unit := λ _ ↦ pure ()
  /-- A line the driver wants shown now, ahead of the final result. -/
  logLine : String → IO Unit := λ s ↦ IO.eprintln s

/-- Run one stage past the driver: run `act`, and on success write `reprStr` of its result to
`<dumpDir>/<dumpName>-<stage>` if `-d dump-<stage>` was given. Every post-driver stage has this
shape, and the debug option is named after the stage, so `stage` supplies both halves.
`checkWellFormed` is the one exception — it produces nothing to dump — and is run directly. -/
private def runStage {ε} {γ} [Repr γ] (dumpName : String) (stage : Stage)
    (act : DiagT Empty ε Base γ) : Base (Except ε γ) := do
  let (_, result) ← DiagT.run act
  if let .ok value := result then
    if ← FlagsEnv.getDebugFlag s!"dump-{stage.name}" then
      dumpToFile (reprStr value) (← getDumpDir) s!"{dumpName}-{stage.name}"
  return result

/-- Compile `source` all the way through, reporting progress through `hooks`.

`containingDir` is where `EXTENDS` resolution starts looking (`none` when the source came from
stdin, which has no directory of its own); `moduleId` is the key this module's source is
registered under, and the one `DriverError`s from it are tagged with.

Never throws and never exits: every failure comes back as `PipelineResult.error`, tagged with the
stage it came from. -/
def runPipeline (source : String) (containingDir : Option System.FilePath) (moduleId : String)
    (hooks : PipelineHooks := {}) : Base PipelineResult := do
  let (warnings, driverResult) ← runM <| compileModule source containingDir moduleId
    (onModuleEvent := λ name outcome ↦ liftM (hooks.onModuleEvent name outcome))
    (onModuleProgress := λ name ↦ liftM (hooks.onModuleProgress name))
    (logLine := λ line ↦ liftM (hooks.logLine line))

  -- The source registry is read back out of the state *after* the driver has run, error or not:
  -- rendering the error is exactly what needs it, and `Base`'s state layer sits under `DiagT`
  -- precisely so a throw does not discard it.
  let sourcesOf : Base SourceRegistry := (·.sources) <$> getThe DriverState

  let typed ← match driverResult with
    | .error e =>
      return { warnings, error := some (.driver e), reached := (PipelineError.stage (.driver e)).predecessor
               sources := ← sourcesOf }
    | .ok typed => pure typed

  let mut result : PipelineResult :=
    { warnings, reached := .typeCheck, sources := ← sourcesOf, typed := some typed }

  match ← DiagT.run (TypedTLAPlus.Module.checkWellFormed typed : DiagT Empty WellFormednessError Base Unit) with
    | (_, .error e) => return { result with error := some (.wellFormedness e) }
    | (_, .ok ()) => result := { result with reached := .wellFormedness }

  let computable ← match ← runStage moduleId .computable
      (TypedTLAPlus.Module.toComputable typed : DiagT Empty ComputableError Base _) with
    | .error e => return { result with error := some (.computable e) }
    | .ok computable => pure computable
  result := { result with reached := .computable, computable := some computable }

  -- `Computable2Guarded` onward only applies to a module with a PlusCal algorithm; an ordinary
  -- TLA⁺ module is finished — and legitimately `reached := .computable` — once it type-checks.
  let some algo := computable.pcalAlgorithm | return result

  let guarded ← match ← runStage moduleId .guarded (algo.toGuarded : DiagT Empty GuardedError Base _) with
    | .error e => return { result with error := some (.guarded e) }
    | .ok guarded => pure guarded
  result := { result with reached := .guarded, guarded := some guarded }

  let network ← match ← runStage moduleId .network (guarded.toNetwork : DiagT Empty G2NError Base _) with
    | .error e => return { result with error := some (.network e) }
    | .ok network => pure network
  return { result with reached := .network, network := some network }

/-- `runPipeline` with its flags and its state supplied: one compile, self-contained, from `IO`.
Each call starts from a fresh `DriverState`, so nothing — module cache, fresh-name counter, source
registry — carries over between two compiles in the same process. -/
def runPipelineIO (flags : FlagsEnv) (source : String) (containingDir : Option System.FilePath)
    (moduleId : String) (hooks : PipelineHooks := {}) : IO PipelineResult :=
  StateT.run' (ReaderT.run (runPipeline source containingDir moduleId hooks) flags) {}

/-- Whether ANSI styling is on for this compile's output (`-fno-color` turns it off). -/
private def FlagsEnv.colored (flags : FlagsEnv) : Bool := !flags.features.contains "no-color"

/-- This compile's warnings, rendered, in the order they were reported — minus any suppressed by
`-Wno-<name>`. Each renders against its own module's source lines, falling back to `mainLines`.
Pure: the caller decides where the lines go (`Fugue.lean` routes them through its spinner, the
regression runner asserts on them). -/
def PipelineResult.renderWarnings (flags : FlagsEnv) (mainLines : List String.Slice)
    (r : PipelineResult) : List String :=
  r.warnings.filterMap λ w ↦
    if flags.warnings.getD (DriverWarning.name w) true then
      some (CompilerDiagnostic.pretty w ((DriverWarning.sourceLines r.sources w).getD mainLines) flags.colored)
    else
      none

/-- This compile's fatal error, rendered, if it failed. -/
def PipelineResult.renderError (flags : FlagsEnv) (mainLines : List String.Slice)
    (r : PipelineResult) : Option String :=
  r.error.map (PipelineError.render r.sources mainLines flags.colored)

/-- Every diagnostic line this result should print, in report order: warnings first, then the
error if there was one. -/
def PipelineResult.renderDiagnostics (flags : FlagsEnv) (mainLines : List String.Slice)
    (r : PipelineResult) : List String :=
  r.renderWarnings flags mainLines ++ (r.renderError flags mainLines).toList

/-- The one-line account of what a successful compile produced, or `none` if it failed before
producing a checked module. -/
def PipelineResult.renderSummary (r : PipelineResult) : Option String :=
  r.typed.map λ typedMod ↦
    s!"Fugue: type-checked and well-formed module '{typedMod.name}' (extends \
{typedMod.extends.length} module(s), {typedMod.declarations₁.length + typedMod.declarations₂.length} \
declaration(s), {if typedMod.pcalAlgorithm.isSome then "with" else "without"} an embedded PlusCal \
algorithm). The rest of the pipeline (the backends, Network2Go/Network2JoinCalculus) isn't \
implemented yet, so it stops after Guarded2Network."

end
