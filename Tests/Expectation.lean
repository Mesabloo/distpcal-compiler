module

public import Common.Diagnostics.Registry
public import Lean.Data.Json

public section

open Lean (Json FromJson fromJson?)

/-!
  What a fixture claims about itself.

  Two sources, in order. A fixture's **filename** (`accept_`/`reject_`/`skip_`) gives the same
  information `tests/regression/run.sh` worked from, and is enough on its own — every fixture runs
  with no authoring work. A `<fixture>.expect.json` **sidecar** next to the `.tla` then says the
  things a filename cannot: which stage a rejection must come from, which code it must carry, which
  warnings must fire.

  JSON and not TOML because `Lean.Data.Json` ships `FromJson` deriving and there is no TOML parser
  to hand. Prose stays out of it — a fixture's `\* Expect: …` header explains *why*, in the `.tla`,
  where a reader of the fixture will see it; JSON has no comments, and duplicating the prose here
  would only let the two drift.

  A sidecar is validated on load, not on use: an unknown stage name, or a code the registry does
  not list, is reported against the fixture rather than becoming a check that quietly never fires.
-/

/-- Whether a fixture is supposed to compile. -/
inductive Outcome : Type
  /-- The compiler must accept the fixture. -/
  | accept
  /-- The compiler must reject it. -/
  | reject
  deriving DecidableEq, Repr, Inhabited

/-- How an `Outcome` is written in a filename prefix, in a sidecar, and in runner output. -/
def Outcome.name : Outcome → String
  | .accept => "accept"
  | .reject => "reject"

instance : ToString Outcome := ⟨Outcome.name⟩

/-- The outcome `s` names, if it names one. -/
def Outcome.ofName? (s : String) : Option Outcome :=
  if s == "accept" then some .accept else if s == "reject" then some .reject else none

/-- How seriously a fixture's result is taken. -/
inductive FixtureStatus : Type
  /-- Normal: every check must pass. -/
  | ok
  /-- Known-broken: the fixture runs, and at least one check must fail. All checks passing is
  reported as XPASS — a failure — so a fixture that starts working can't be forgotten about. -/
  | xfail
  /-- Not run at all. A last resort: a skipped fixture rots silently, which is why `xfail` exists. -/
  | skip
  deriving DecidableEq, Repr, Inhabited

/-- The status `s` names, if it names one. -/
def FixtureStatus.ofName? (s : String) : Option FixtureStatus :=
  if s == "ok" then some .ok
  else if s == "xfail" then some .xfail
  else if s == "skip" then some .skip
  else none

/-- A warning a fixture expects, and how many times. -/
structure WarningExpectation : Type where
  /-- The warning's code. -/
  code : DiagnosticCode
  /-- How many times it must fire. -/
  count : Nat := 1
  deriving Inhabited

/-- Everything a fixture asserts about one compile of itself. -/
structure Expectation : Type where
  /-- Accept or reject. -/
  outcome : Outcome := .accept
  /-- For a rejection, the exact stage the error must come from. `none` means unasserted — the
  stage check then reports SKIP rather than passing vacuously. -/
  failsAt : Option Stage := none
  /-- For a rejection, the code the error must carry. Also unasserted when `none`.

  There is deliberately no expected *message*: the code is the identity, and wording is expected
  to change. A regex over the rendered text would pin that wording, break on every improvement to
  it, and assert nothing the code does not already assert. -/
  errorCode : Option DiagnosticCode := none
  /-- For an acceptance, the minimum stage that must have completed. `none` falls back to
  `Expectation.defaultReaches`, derived from what the compile actually produced. -/
  reaches : Option Stage := none
  /-- Every warning the compile must produce, with its count. -/
  warnings : List WarningExpectation := []
  /-- Whether warnings beyond `warnings` are tolerated. `false` — strict — is the default and the
  point: a new spurious warning anywhere in the corpus fails by default, and a fixture that wants
  one ignored has to say so in writing. -/
  allowExtraWarnings : Bool := false
  /-- `-W` names whose suppression is re-checked: the fixture is compiled again with each disabled,
  and the warning must disappear without the outcome changing. -/
  suppressible : List String := []
  /-- Normal / known-broken / not run. -/
  status : FixtureStatus := .ok
  /-- Why this fixture is `xfail` or `skip`. Shown in the runner's output. -/
  reason : String := ""
  deriving Inhabited

/-- The expectation a fixture's filename alone justifies, or `none` if the name matches no
convention — which the runner reports rather than quietly ignoring, since an unrecognised name is
usually a typo that would otherwise take the fixture out of the suite.

Fixtures are named `<Prefix><WhatItTests>.tla`, in CamelCase, because TLA⁺ requires a module's
file to be named after the module: `EXTENDS Foo` looks for `Foo.tla` and nothing else. The corpus
used snake_case until the sidecars showed what that cost — two fixtures whose `EXTENDS` could
never resolve, and which had therefore never tested what they claimed (§9.23). -/
def Expectation.ofFilename (name : String) : Option Expectation :=
  if "Accept".isPrefixOf name then
    some { outcome := .accept }
  else if "Reject".isPrefixOf name then
    some { outcome := .reject }
  else if "Skip".isPrefixOf name then
    -- For a fixture whose *own text* is the problem, not the compiler: it asserts something it
    -- does not exercise, and no amount of fixing the compiler makes it start testing that thing.
    -- A merely known-broken fixture belongs in `xfail` instead, where it keeps running and keeps
    -- having to fail. Every `Skip*` fixture carries a sidecar `reason` saying which it is.
    some { outcome := .accept, status := .skip, reason := "filename says skip" }
  else
    none

/-!
  ### The sidecar's own shape

  A separate structure from `Expectation`, with every field optional, rather than `FromJson` on
  `Expectation` directly. Two reasons: an absent field must mean "keep what the filename decided",
  which is not the same as "the field's own default" — they differ for `outcome` — and the wire
  format names stages and codes as *strings*, which have to be checked against the registry before
  they can become an `Expectation`'s typed fields.
-/

/-- A `warnings` entry, as written. -/
private structure WarningSpec : Type where
  /-- The warning's code, e.g. `"W0003"`. -/
  code : String
  /-- How many times it must fire. Defaults to 1. -/
  count : Option Nat := none
  deriving FromJson

/-- An `error` object, as written. -/
private structure ErrorSpec : Type where
  /-- The error's code, e.g. `"E0018"`. -/
  code : String
  deriving FromJson

/-- A whole sidecar, as written. -/
private structure Sidecar : Type where
  /-- `"accept"` or `"reject"`. -/
  outcome : Option String := none
  /-- The stage a rejection must come from, e.g. `"typecheck"`. -/
  failsAt : Option String := none
  /-- The error a rejection must carry. -/
  error : Option ErrorSpec := none
  /-- The minimum stage an acceptance must complete. -/
  reaches : Option String := none
  /-- Every warning the compile must produce. -/
  warnings : Option (List WarningSpec) := none
  /-- Tolerate warnings beyond those listed. -/
  allowExtraWarnings : Option Bool := none
  /-- `-W` names whose suppression is re-checked. -/
  suppressible : Option (List String) := none
  /-- `"ok"`, `"xfail"` or `"skip"`. -/
  status : Option String := none
  /-- Why, for a non-`ok` status. -/
  reason : Option String := none
  deriving FromJson

/-- Parse a code and check the registry lists it. Rejecting an unregistered code here is what stops
a sidecar naming a plausible-looking number that nothing can ever emit. -/
private def parseCode (what raw : String) : Except String DiagnosticCode := do
  let some code := DiagnosticCode.ofString? raw
    | throw s!"{what}: '{raw}' is not a diagnostic code (codes look like 'E0018' or 'W0003')"
  if (Diagnostics.find? code).isNone then
    throw s!"{what}: no diagnostic is registered under '{raw}'"
  return code

/-- Parse a stage name against `Stage.list`. -/
private def parseStage (what raw : String) : Except String Stage := do
  let some stage := Stage.ofName? raw
    | throw s!"{what}: '{raw}' is not a stage. Known stages: \
{String.intercalate ", " (Stage.list.map (·.name))}"
  return stage

/-- Apply a parsed sidecar on top of the filename's defaults. -/
private def Sidecar.applyTo (s : Sidecar) (base : Expectation) : Except String Expectation := do
  let outcome ← match s.outcome with
    | none => pure base.outcome
    | some raw => match Outcome.ofName? raw with
      | some o => pure o
      | none => throw s!"outcome: '{raw}' is neither \"accept\" nor \"reject\""
  let status ← match s.status with
    | none => pure base.status
    | some raw => match FixtureStatus.ofName? raw with
      | some st => pure st
      | none => throw s!"status: '{raw}' is none of \"ok\", \"xfail\", \"skip\""
  let failsAt ← s.failsAt.mapM (parseStage "failsAt")
  let reaches ← s.reaches.mapM (parseStage "reaches")
  let errorCode ← s.error.mapM λ e ↦ parseCode "error.code" e.code
  let warnings ← (s.warnings.getD []).mapM λ w ↦ do
    return { code := ← parseCode "warnings[].code" w.code, count := w.count.getD 1 }
  return { outcome, status, failsAt, reaches, errorCode, warnings
           allowExtraWarnings := s.allowExtraWarnings.getD base.allowExtraWarnings
           suppressible := s.suppressible.getD base.suppressible
           reason := s.reason.getD base.reason }

/-- The sidecar path for a fixture: `accept_foo.tla` → `accept_foo.expect.json`. -/
def Expectation.sidecarPath (fixture : System.FilePath) : System.FilePath :=
  fixture.withExtension "expect.json"

/-- A fixture's expectation: its filename's defaults, with its sidecar applied if one exists. An
unreadable sidecar — bad JSON, unknown stage, unregistered code — comes back as `Except.error`, and
the runner reports it against the fixture instead of running it: a sidecar nobody can read is a
broken assertion, not an absent one. -/
def Expectation.load (fixture : System.FilePath) (base : Expectation) :
    IO (Except String Expectation) := do
  let path := Expectation.sidecarPath fixture
  unless ← path.pathExists do
    return .ok base
  let text ← IO.FS.readFile path
  let json ← match Json.parse text with
    | .error e => return .error s!"{path}: {e}"
    | .ok json => pure json
  let sidecar ← match fromJson? (α := Sidecar) json with
    | .error e => return .error s!"{path}: {e}"
    | .ok sidecar => pure sidecar
  match sidecar.applyTo base with
  | .error e => return .error s!"{path}: {e}"
  | .ok expectation => return .ok expectation

end
