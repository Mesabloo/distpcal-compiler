module

public import Tests.GoBuild
public import Tests.Report
public import Cli.Basic
import Std.Sync.Mutex

public section

open Cli

/-!
  The regression suite's entry point: `lake test -- [FILTER…]`.

  Fixtures are compiled **in-process**, one `runPipelineIO` call each, rather than by spawning the
  `fugue` binary. That is what makes the interesting checks possible at all — where a compile
  stopped, which diagnostic it produced, what it built — none of which survives the trip through a
  process boundary and an exit code. It also means the runner and the compiler are built together,
  so a fixture can never be checked against a stale binary.

  One failure mode is still not caught: a hard crash in native code, which takes the process down
  before any report can be made. A Lean exception, the common case, *is* caught — `IO.asTask` hands
  it back as an `Except`, and the fixture reports a failed "no crash" check — and a fixture that
  never terminates is abandoned by `withTimeout` and reported by name.
-/

/-- One fixture: a `.tla` file and what its name says about it. -/
structure Fixture : Type where
  /-- The filename, e.g. `reject_bad_arity.tla`. Also the `moduleId` the compile runs under, so
  diagnostics are tagged with something a reader can find. -/
  name : String
  /-- Its full path. -/
  path : System.FilePath
  /-- What it claims. -/
  expectation : Expectation
  /-- Why its sidecar could not be read, when it could not be. -/
  sidecarError : Option String := none
  deriving Inhabited

/-- Where the fixtures live, relative to the repository root. Two spellings because the directory
holding them also holds this runner's own modules, whose Lean module names capitalise it: the
working tree calls it `Tests`, and git's index still records the fixtures under `tests`. On a
case-insensitive filesystem those are one directory and either entry finds it; on a case-sensitive
one they may genuinely be two, and the runner should not care which. -/
private def fixturesLayouts : List System.FilePath := ["Tests" / "regression", "tests" / "regression"]

/-- The fixture directory. `$FUGUE_FIXTURES` overrides; otherwise the search is anchored at the
**executable** and walks up looking for `tests/regression`, exactly as `fugue explain` finds its
docs corpus. Anchoring at the working directory would be wrong for the same reason it is there:
`lake test` can be run from anywhere in (or outside) the checkout, and the binary always knows
where it was built. -/
private def findFixturesDir : IO (Option System.FilePath) := do
  if let some dir ← IO.getEnv "FUGUE_FIXTURES" then
    return some ↑dir
  let mut dir := (← IO.appPath).parent
  -- Bounded: a filesystem root is its own parent in some spellings, and this must terminate.
  for _ in [0:6] do
    let some here := dir | break
    for layout in fixturesLayouts do
      if ← (here / layout).isDir then
        return some (here / layout)
    dir := here.parent
  return none

/-- Every `.tla` file in `dir`, in filename order, paired with its expectation: what the filename
implies, with `<fixture>.expect.json` applied on top.

A name matching no convention still yields a `Fixture` — reported as a skip with a note rather
than silently dropped, since a mistyped prefix would otherwise take a fixture out of the suite
with nothing to show for it. A sidecar that will not load yields one too, carrying the parse error
as `sidecarError`: the fixture is then reported as a failure rather than run, because a sidecar
nobody can read is a broken assertion, not an absent one. -/
private def discover (dir : System.FilePath) : IO (List Fixture) := do
  let entries ← dir.readDir
  let names : Array String := entries.map (·.fileName)
  let sorted : Array String := names.filter (λ name ↦ (System.FilePath.mk name).extension == some "tla")
    |>.qsort (· < ·)
  sorted.toList.mapM λ (name : String) ↦ do
    let path := dir / name
    let base := (Expectation.ofFilename name).getD
      { status := .skip, reason := "name doesn't start with accept_/reject_/skip_" }
    match ← Expectation.load path base with
    | .ok expectation => return { name, path, expectation }
    | .error e => return { name, path, expectation := base, sidecarError := some e }

/-- The `FlagsEnv` a fixture compiles under: bare apart from colour, plus whichever `-W` names
`suppressed` turns off and whichever `-I` directories its sidecar asked for. Bare so that what a
fixture asserts is what the compiler does by *default* — a fixture that needs a flag to be
interesting should say so, not inherit it from the harness, which is exactly what the sidecar's
`searchPath` is. Colour follows the runner's own setting, since the only place these diagnostics go
is its failure output. -/
private def compileFlags (colored : Bool) (searchPath : List System.FilePath := [])
    (suppressed : List String := []) (goPackage : Bool := false) : FlagsEnv :=
  { features := if colored then {} else Std.HashMap.ofList [(Feature.noColor.name, none)]
    warnings := Std.HashMap.ofList (suppressed.map (·, false))
    -- The one exception to "bare": a fixture that asks for a `go build` is emitted under a
    -- library package rather than `main`, which nothing else asserts on. See `Tests/GoBuild.lean`
    -- for why `main` would not do.
    targetOptions :=
      if goPackage then Std.HashMap.ofList [("go-pkg", some GoBuild.packageName)] else {}
    searchPath }

/-- Run `act`, giving up after `timeoutMs`. `none` means it did not finish in time.

Lean has no timed wait, so this races the real work against a sleeper and takes whichever lands
first. What it cannot do is *stop* the loser: a Lean task has no cancellation, so an abandoned
compile keeps running — and keeps a core — until the process exits. That is the honest cost of
reporting the culprit instead of hanging forever with no indication of which fixture is at fault,
and it is why the timeout is a backstop rather than something a fixture should ever reach. -/
private def withTimeout {α : Type} (timeoutMs : Nat) (act : IO α) : IO (Option α) := do
  let work ← IO.asTask act .dedicated
  let alarm ← IO.asTask (do IO.sleep timeoutMs.toUInt32) .dedicated
  match ← IO.waitAny [work.map (·.map Sum.inl), alarm.map (·.map Sum.inr)] with
  | .error e => throw e
  | .ok (.inl a) => return some a
  | .ok (.inr _) => return none

/-- Compile one fixture and judge it.

`suppressible` costs one extra compile per name: `-W` is a flag, and the only honest way to check
that a flag suppresses something is to pass it and look. Those re-runs contribute their own checks
and nothing else — their diagnostics are not reported, since the first compile's are the ones that
describe the fixture. -/
def runFixture (style : ReportStyle) (timeoutMs : Nat) (repoRoot : System.FilePath)
    (fx : Fixture) : IO FixtureReport := do
  if let some e := fx.sidecarError then
    let broken : CheckResult := { name := "sidecar", status := .fail, detail := e }
    return { name := fx.name, verdict := .fail, checks := [broken] }

  if fx.expectation.status == .skip then
    return { name := fx.name, verdict := .skip, reason := fx.expectation.reason }

  let source ← IO.FS.readFile fx.path
  let flags := compileFlags style.colored fx.expectation.searchPath
                 (goPackage := fx.expectation.goBuild)

  let start ← IO.monoMsNow
  let finished ← withTimeout timeoutMs
    (runPipelineIO flags source fx.path.parent fx.name fx.path.fileStem).toBaseIO
  let elapsedMs := (← IO.monoMsNow) - start

  let some outcome := finished
    | return { name := fx.name, verdict := .timeout, elapsedMs,
               reason := s!"gave up after {timeoutMs}ms" }

  match outcome with
  | .error e =>
    let crashed : CheckResult :=
      { name := "no crash", status := .fail, detail := s!"the compiler threw: {e}" }
    return { name := fx.name, verdict := .ofChecks fx.expectation.status [crashed],
             checks := [crashed], elapsedMs, reason := fx.expectation.reason }
  | .ok result =>
    let suppressionChecks ← fx.expectation.suppressible.mapM λ warningName ↦ do
      let suppressedFlags := compileFlags style.colored fx.expectation.searchPath [warningName]
      match ← (runPipelineIO suppressedFlags source fx.path.parent fx.name fx.path.fileStem).toBaseIO with
      | .error e =>
        return { name := s!"suppression of -W{warningName}", status := .fail,
                 detail := s!"the compiler threw under -Wno-{warningName}: {e}" }
      | .ok suppressed => return checkSuppression fx.expectation suppressedFlags warningName suppressed
    let goCheck ← GoBuild.checkGoBuild fx.expectation repoRoot fx.path result
    let checks := runChecks fx.expectation result ++ suppressionChecks ++ [goCheck]
    let lines := source.split (· == '\n') |>.toList
    return { name := fx.name, verdict := .ofChecks fx.expectation.status checks, checks,
             elapsedMs, reason := fx.expectation.reason,
             diagnostics := result.renderDiagnostics flags lines }

/-- Split `xs` into `jobs` lists, round-robin. Round-robin rather than contiguous blocks because
fixtures are in filename order and cost is not evenly spread along it — the `accept_*` half is
generally the expensive one, and contiguous blocks would hand one worker most of it. -/
private def roundRobin {α : Type} (jobs : Nat) (xs : List α) : List (List α) :=
  (List.range jobs).map λ i ↦ xs.zipIdx.filterMap λ (x, k) ↦ if k % jobs == i then some x else none

/-- Run `fxs` sequentially, printing each report as it lands. `printer` serialises the printing:
several workers finish at once, and a fixture's report is several lines, so without the lock two
failing fixtures' diagnostics would interleave. -/
private def runWorker (style : ReportStyle) (timeoutMs : Nat) (repoRoot : System.FilePath)
    (printer : Std.Mutex Unit) (fxs : List Fixture) : IO (List FixtureReport) :=
  fxs.mapM λ fx ↦ do
    let report ← runFixture style timeoutMs repoRoot fx
    -- One `IO.print` of the whole block, not a `println` per line: the lock already orders
    -- workers against each other, and a single write keeps a report atomic even for anything
    -- reading this runner's stdout through a pipe.
    let text := String.intercalate "\n" (report.lines style) ++ "\n"
    printer.atomically (liftM (IO.print text : IO Unit))
    return report

/-- Run every fixture, `jobs` at a time.

Everything the *driver* owns is per-compile — flags, the fresh-name counter, the source registry,
the module cache all live in `DriverState` — so on that count two compiles in this process cannot
see each other. One thing below the driver is not: `Common/Position.lean`'s `Internal.sourceMap`,
the process-global `IO.Ref` that `@@`/`posOf` use to attach spans to AST nodes by pointer address.
`runPipelineIO` clears it per compile (`forgetSourcePositions`), which is what makes a *sequential*
run of many fixtures behave like one fixture per process — but clearing is itself the thing that
makes concurrency worse, not better: one worker's clear lands in the middle of another's compile
and drops the spans it has registered so far. The result is not a crash but wrong-and-plausible
line numbers, which is the more expensive failure for a suite that is about to start asserting on
spans.

Hence the default of 1. The parallelism is real and stays here — it is a flag away once positions
are per-compile state rather than a global keyed on addresses. -/
private def runAll (style : ReportStyle) (jobs timeoutMs : Nat) (repoRoot : System.FilePath)
    (fxs : List Fixture) : IO (List FixtureReport) := do
  let printer ← Std.Mutex.new ()
  let tasks ← (roundRobin (max jobs 1) fxs).mapM λ chunk ↦
    IO.asTask (runWorker style timeoutMs repoRoot printer chunk) .dedicated
  let results ← tasks.mapM λ t ↦ do IO.ofExcept (← IO.wait t)
  return results.flatten

/-- One fixture, as `--list` prints it. -/
private def Fixture.listLine (fx : Fixture) : String :=
  let status := match fx.expectation.status with
    | .ok => "" | .xfail => " [xfail]" | .skip => " [skip]"
  s!"{fx.name}  ({fx.expectation.outcome}){status}"

/-- Whether the runner's own output is styled: `-f no-color` turns it off, as everywhere else in
this project; so do `NO_COLOR` (https://no-color.org) and a non-terminal stdout, since neither
wants escape codes it cannot render. -/
private def wantsColor (noColorFlag : Bool) : IO Bool := do
  if noColorFlag then return false
  if (← IO.getEnv "NO_COLOR").isSome then return false
  (← IO.getStdout).isTty

/-- Does `name` contain `pattern`? Spelled through `String.splitOn` rather than a substring
search: the standard library's has changed name and home twice recently, and this is not a hot
path — it runs once per fixture per filter. -/
private def matchesFilter (name pattern : String) : Bool :=
  pattern.isEmpty || (name.splitOn pattern).length > 1

/-- `-f<name>` toggles the runner recognises: deliberately a *subset* of the compiler's `Feature`
set, not all of it — the runner draws no spinner, so `-fno-progress` would have nothing to turn
off. Spelled through `Feature` all the same, so the name cannot drift from the compiler's. -/
private def knownFeatures : Array String := #[Feature.noColor.name]

private def runTests (p : Parsed) : IO UInt32 := do
  let features := p.flag? "feature" |>.map (·.as! (Array String)) |>.getD #[]
  for feature in features do
    unless knownFeatures.contains feature do
      IO.eprintln s!"error: unknown feature '{feature}'. Known features: \
{String.intercalate ", " knownFeatures.toList}."
      return 2

  let style : ReportStyle :=
    { colored := ← wantsColor (features.contains Feature.noColor.name), verbose := p.hasFlag "verbose" }
  let jobs := p.flag? "jobs" |>.map (·.as! Nat) |>.getD 1
  -- Generous on purpose: the slowest fixture in the corpus runs in a quarter of a second, so
  -- anything near this limit is a hang, not a slow test.
  let timeoutMs := p.flag? "timeout" |>.map (·.as! Nat) |>.getD 30000

  let some dir ← findFixturesDir
    | IO.eprintln "error: no fixture directory found. Expected 'tests/regression' in an ancestor \
of this executable, or $FUGUE_FIXTURES set."
      return 2

  let filters := p.variableArgsAs! String
  let all ← discover dir
  let fixtures := if filters.isEmpty then all
    else all.filter λ fx ↦ filters.any (matchesFilter fx.name)

  if p.hasFlag "list" then
    fixtures.forM λ fx ↦ IO.println fx.listLine
    return 0

  if fixtures.isEmpty then
    IO.eprintln s!"error: no fixture in '{dir}' matched {filters.toList}."
    return 2

  -- `dir` is `<root>/tests/regression`, so the checkout root is two levels up: what
  -- `Tests/GoBuild.lean`'s generated `go.mod` resolves the runtime library against.
  let repoRoot := (dir.parent.bind (·.parent)).getD "."
  let reports ← runAll style jobs timeoutMs repoRoot fixtures
  IO.println ""
  let ⟨summary, hasFailed⟩ := summaryLine style reports
  IO.println summary
  return if hasFailed then 1 else 0

private def cli : Cmd := `[Cli|
  test VIA runTests; ["0.1.0"]
  "Run the regression suite in tests/regression."

  FLAGS:
    j, jobs : Nat; "How many fixtures to compile at once. Defaults to 1 — anything higher races on Common/Position.lean's global source map (see `runAll`)."
    v, verbose; "Show every check, not just the failing ones."
    "timeout" : Nat; "Milliseconds before a fixture is abandoned and reported as TIMEOUT. Defaults to 30000."
    l, list; "List the matching fixtures and what they claim, without running them."
    f, feature : Array String; "Feature toggles, comma-separated. Only `no-color` so far."

  ARGS:
    ...filters : String; "Only run fixtures whose filename contains one of these."
]

/-- The `lake test` driver's entry point. -/
def main (args : List String) : IO UInt32 := cli.validate args

end
