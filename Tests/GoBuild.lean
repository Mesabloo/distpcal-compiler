module

public import Tests.Check

public section

/-!
  Compiling a fixture's emitted Go with `go build`.

  Every other check in this suite is structural: the pipeline stops at a `String`
  (`Driver/Pipeline.lean`), and nothing ever asks Go whether that string is a Go program. That is
  a real gap rather than a theoretical one — the backend builds an AST, and an AST can be
  perfectly well-formed while naming an identifier that does not exist, using a `switch` head Go
  cannot match against integer cases, or leaving a local unused. None of those is visible to a
  check that only looks at how far the compile got.

  So this one is not a pure function of a `PipelineResult`: it writes the emitted file to a
  temporary directory, gives it a `go.mod` that points `github.com/mesabloo/fugue` at this
  checkout, and runs the real `go build`.

  **Opt-in, per fixture** (`"goBuild": true` in the sidecar). Two reasons it cannot be the default
  for every accepting fixture. It costs a process spawn and a compile of the runtime library, which
  is orders of magnitude more than the in-process checks beside it. And most fixtures would fail
  it for a reason that is not a bug: a `CONSTANT` compiles to a Go identifier the *user* is
  expected to define, so a fixture declaring one emits code that legitimately does not build on its
  own. A fixture supplies those definitions in `_stubs/<Fixture>.go`, copied into the build
  directory alongside the emitted code. The directory is named with a leading underscore because
  the `go` tool ignores such directories outright — otherwise the stubs would all be one Go
  package in the fixture corpus, and every one of them declaring its own `PID` would break the
  repository's own `go build ./...`.

  **`go` missing from `PATH` is a SKIP, not a failure.** The Lean build has no Go dependency and
  should not grow one just because the suite would like to run this check.
-/

namespace GoBuild

/-- The Go package the emitted file declares under this check.

Not `main`, which is the compiler's own default: a `main` package with no `func main` is itself a
build error, and it would mask every error this check exists to find. A fixture's
`<Fixture>.stub.go` has to declare this same package. -/
def packageName : String := "fixture"

/-- The module path the runtime library is published under, as generated code imports it. -/
private def runtimeModule : String := "github.com/mesabloo/fugue"

/-- The `go` directive to give the generated `go.mod`, read from the repository's own so the two
cannot drift. Absent — which should not happen — the directive is simply omitted, and Go falls
back to its own default language version. -/
private def goDirective (repoRoot : System.FilePath) : IO (Option String) := do
  let path := repoRoot / "go.mod"
  unless ← path.pathExists do return none
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").find? λ line ↦ "go ".isPrefixOf line.trim

/-- The `go.mod` the emitted file is built under: its own throwaway module, with the runtime
resolved by `replace` to this checkout rather than fetched. -/
private def goMod (repoRoot : System.FilePath) : IO String := do
  let directive := (← goDirective repoRoot).elim "" (s!"{·.trim}\n\n")
  return s!"module fuguefixture\n\n{directive}require {runtimeModule} v0.0.0\n\n\
            replace {runtimeModule} => {repoRoot}\n"

/-- A fixture's Go stub companion: `<dir>/AcceptFoo.tla` → `<dir>/_stubs/AcceptFoo.go`. -/
def stubPath (fixture : System.FilePath) : System.FilePath :=
  let dir := fixture.parent.getD "."
  dir / "_stubs" / s!"{fixture.fileStem.getD "fixture"}.go"

/-- Is there a `go` on `PATH` that runs?

A separate probe rather than reading it off `go build`'s own failure, because the two are not
reliably distinguishable at the call site: a missing executable surfaces sometimes as a thrown
`IO.Error` and sometimes as a non-zero exit with the spawn failure on stderr, and mistaking the
second for a build failure would turn "no Go toolchain here" into a red suite. `go version` is the
cheapest thing that answers the question, and it runs only for a fixture that opted in. -/
def goAvailable : IO Bool := do
  match ← (IO.Process.output { cmd := "go", args := #["version"] }).toBaseIO with
  | .error _ => return false
  | .ok out => return out.exitCode == 0

/--
  Build `go` in a temporary directory and report what `go build` said.

  `GOPROXY=off` because nothing here should ever reach the network: the one dependency is
  `replace`d to a directory on disk, so a fetch would mean the `replace` did not take, and failing
  is a better answer than silently downloading something. `GOFLAGS=-mod=mod` keeps Go from
  insisting on a `go.sum`, which a directory-replaced module does not need and cannot have.
-/
private def runGoBuild (repoRoot : System.FilePath) (fixture : System.FilePath) (go : String) :
    IO (Except String Unit) :=
  IO.FS.withTempDir λ dir ↦ do
    IO.FS.writeFile (dir / "go.mod") (← goMod repoRoot)
    IO.FS.writeFile (dir / "spec.go") go
    let stub := stubPath fixture
    if ← stub.pathExists then
      IO.FS.writeFile (dir / "stub.go") (← IO.FS.readFile stub)
    let out ← IO.Process.output
      { cmd := "go", args := #["build", "./..."], cwd := dir
        env := #[("GOPROXY", some "off"), ("GOFLAGS", some "-mod=mod")] }
    if out.exitCode == 0 then
      return .ok ()
    else
      -- stderr is where `go build` puts diagnostics; stdout is included because a *tooling*
      -- failure (a bad `go.mod`, say) can land there instead, and losing it would leave the
      -- check saying only that something went wrong.
      let text := (out.stderr ++ out.stdout).trim
      return .error (if text.isEmpty then s!"go build exited {out.exitCode} and said nothing" else text)

/-- Compile the emitted Go, if this fixture asked for it.

Reports `.skip` rather than `.pass` in every case where nothing was actually built — the fixture
not opting in, the compile having failed already (the outcome check owns that), or there being no
`go` to run. A pass here means `go build` ran and was happy. -/
def checkGoBuild (e : Expectation) (repoRoot : System.FilePath) (fixture : System.FilePath)
    (r : PipelineResult) : IO CheckResult := do
  let name := "go build"
  unless e.goBuild do
    return { name, status := .skip, detail := "fixture does not ask for a go build" }
  unless r.succeeded do
    return { name, status := .skip, detail := "the compile failed — see the outcome check" }
  let some go := r.go
    | return { name, status := .fail,
               detail := "the fixture asks for a go build, but the compile produced no Go" }
  unless ← goAvailable do
    return { name, status := .skip, detail := "no `go` on PATH" }
  match ← (runGoBuild repoRoot fixture go).toBaseIO with
  | .error err =>
    return { name, status := .fail, detail := s!"could not run `go build`: {err}" }
  | .ok (.error output) =>
    return { name, status := .fail, detail := output }
  | .ok (.ok ()) =>
    return { name, status := .pass }

end GoBuild

end
