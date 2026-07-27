module

public import Tests.Check
import Common.Errors

public section

open Colorized (Color Style)

/-!
  What the runner prints.

  Kept apart from the checks themselves so that deciding a fixture's verdict, and deciding how to
  say it, are separate things — the same reports feed the per-fixture lines, the tally, and (later)
  the `--report` file.
-/

/-- A fixture's overall answer, once its checks are in. -/
inductive FixtureVerdict : Type
  /-- Every check that ran passed. -/
  | pass
  /-- At least one check failed. -/
  | fail
  /-- Known-broken, and still broken. Not counted as a failure. -/
  | xfail
  /-- Known-broken, but every check passed. Counted as a **failure**: either the fixture was
  fixed and nobody removed its `xfail`, or it is no longer testing what it claimed to. -/
  | xpass
  /-- Never ran. -/
  | skip
  /-- Ran past its time limit and was abandoned. A failure, and a distinct one: a fixture that has
  not finished has produced no checks at all, so reporting it as a plain FAIL would suggest
  something was asserted and came out false. -/
  | timeout
  deriving DecidableEq, Repr, Inhabited

/-- The verdict for a fixture with `status` whose checks came out as `checks`. -/
def FixtureVerdict.ofChecks (status : FixtureStatus) (checks : List CheckResult) : FixtureVerdict :=
  match status with
  | .skip => .skip
  | .xfail => if checks.any (·.failed) then .xfail else .xpass
  | .ok => if checks.any (·.failed) then .fail else .pass

/-- Does this verdict mean the run has failed? -/
def FixtureVerdict.isFailure : FixtureVerdict → Bool
  | .fail | .xpass | .timeout => true
  | .pass | .xfail | .skip => false

/-- The four-letter label, and the colour it is printed in. -/
def FixtureVerdict.label : FixtureVerdict → String × Color
  | .pass => ("PASS", .Green)
  | .fail => ("FAIL", .Red)
  | .xfail => ("XFAIL", .Yellow)
  | .xpass => ("XPASS", .Red)
  | .skip => ("SKIP", .Yellow)
  | .timeout => ("TIMEOUT", .Red)

/-- Everything one fixture's run produced. -/
structure FixtureReport : Type where
  /-- The fixture's filename. -/
  name : String
  /-- Its verdict. -/
  verdict : FixtureVerdict
  /-- Each check's answer, in check order. -/
  checks : List CheckResult := []
  /-- Wall-clock milliseconds spent compiling it. Zero for a skipped fixture. -/
  elapsedMs : Nat := 0
  /-- Why it is `xfail`/`skip`, when it is. -/
  reason : String := ""
  /-- The compile's own rendered diagnostics, shown under a failing fixture. -/
  diagnostics : List String := []
  deriving Inhabited

/-- How the runner's own output is styled. -/
structure ReportStyle : Type where
  /-- ANSI styling on? Off under `-f no-color` (and under `NO_COLOR`). -/
  colored : Bool := true
  /-- Show passing and skipped checks too, not just failing ones. -/
  verbose : Bool := false
  deriving Inhabited

/-- One check, indented under its fixture.

A detail may be several lines — `go build`'s output is, and truncating it to the first line would
throw away exactly the errors the check exists to surface — so continuations are indented under
the first rather than left to start at column zero. -/
private def CheckResult.lines (style : ReportStyle) (c : CheckResult) : List String :=
  let (mark, color) : String × Color := match c.status with
    | .pass => ("✔", .Green)
    | .fail => ("✖", .Red)
    | .skip => ("–", .Yellow)
  match c.detail.splitOn "\n" with
  | [] | [""] => [s!"      {colorizeIf style.colored color mark} {c.name}"]
  | first :: rest =>
    s!"      {colorizeIf style.colored color mark} {c.name}: {first}"
      :: rest.map (s!"        {·}")

/-- A fixture's block of output: its result line, then whichever of its checks are worth showing
(the failing ones, or all of them under `-v`), then the compiler's own diagnostics when it
failed — those are what a reader actually needs to see, and printing them for a passing fixture
would bury them. -/
def FixtureReport.lines (style : ReportStyle) (r : FixtureReport) : List String :=
  let (label, color) := r.verdict.label
  let timing := if r.verdict == .skip then "" else s!" ({r.elapsedMs}ms)"
  let reason := if r.reason.isEmpty then "" else s!" — {r.reason}"
  let head := s!"{styleIf style.colored .Bold (colorizeIf style.colored color label)}  {r.name}{timing}{reason}"
  -- Nothing below the head line for a fixture that came out as expected: an `xfail`'s failing
  -- check is *why it is an xfail*, already said by its `reason`, and printing it on every green
  -- run would be noise. `-v` shows everything, including the checks that passed.
  let interesting := r.verdict.isFailure || style.verbose
  let shown := if style.verbose then r.checks
    else if interesting then r.checks.filter (·.failed)
    else []
  head :: shown.flatMap (CheckResult.lines style)
    ++ (if interesting then r.diagnostics.flatMap (·.splitOn "\n" |>.map (s!"      {·}")) else [])

/-- How many reports carry each verdict, in `FixtureVerdict` order. -/
private def tally (reports : List FixtureReport) (v : FixtureVerdict) : Nat :=
  reports.countP (·.verdict == v)

/-- The closing tally. Mirrors the shape `run.sh` printed (`N passed, N failed, N skipped`), plus
the two verdicts it had no notion of. -/
def summaryLine (style : ReportStyle) (reports : List FixtureReport) : String :=
  let timedOut := tally reports .timeout
  let failed := tally reports .fail + tally reports .xpass + timedOut
  let parts :=
    [s!"{tally reports .pass} passed", s!"{failed} failed", s!"{tally reports .xfail} xfailed",
     s!"{tally reports .skip} skipped"]
    ++ (if timedOut == 0 then [] else [s!"{timedOut} timed out"])
  let color : Color := if failed == 0 then .Green else .Red
  styleIf style.colored .Bold (colorizeIf style.colored color (String.intercalate ", " parts))

end
