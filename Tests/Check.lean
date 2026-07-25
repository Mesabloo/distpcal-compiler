module

public import Tests.Expectation
public import Driver.Pipeline

public section

/-!
  The individual assertions made about one compile.

  Every check is a pure function of an `Expectation` and a `PipelineResult`, and they all run:
  a fixture reports *all* of its mismatches at once rather than stopping at the first, because
  "wrong stage" and "wrong code" are usually one edit apart and finding them one run at a time is
  wasted time.

  A check can report `.skip`, meaning "this fixture says nothing about that". That is a real,
  distinct answer from `.pass`: with no sidecars yet, every rejection's stage is unasserted, and
  reporting those as passes would make the suite look like it checks something it does not.
-/

/-- One check's answer. -/
inductive CheckStatus : Type
  /-- Asserted and true. -/
  | pass
  /-- Asserted and false. -/
  | fail
  /-- Not asserted by this fixture, or not applicable to it. -/
  | skip
  deriving DecidableEq, Repr, Inhabited

/-- What one check concluded. -/
structure CheckResult : Type where
  /-- The check's name, as printed. -/
  name : String
  /-- Its answer. -/
  status : CheckStatus
  /-- One line of detail: why it failed, or what it would have needed to run. -/
  detail : String := ""
  deriving Inhabited

/-- Did this check fail? -/
def CheckResult.failed (c : CheckResult) : Bool := c.status == .fail

/-- The stage an accepted fixture must reach when it does not say. Derived from what the compile
produced rather than fixed: `Guarded2Network` onward only applies to a module with a PlusCal
algorithm, so a plain TLA⁺ module is legitimately finished at `.computable`, while one with an
algorithm that stops there stopped early. -/
def Expectation.defaultReaches (r : PipelineResult) : Stage :=
  match r.typed with
  | some typedMod => if typedMod.pcalAlgorithm.isSome then .network else .computable
  | none => .computable

/-- Accepted vs. rejected — the one bit `run.sh` checked, minus the exit code. In-process there is
nothing to interpret: the compile either produced an error or it did not. -/
def checkOutcome (e : Expectation) (r : PipelineResult) : CheckResult :=
  let got : Outcome := if r.succeeded then .accept else .reject
  if got == e.outcome then
    { name := "outcome", status := .pass }
  else
    { name := "outcome", status := .fail,
      detail := s!"expected the compiler to {e.outcome} this module, it did {got}" }

/-- Where a rejection came from. The check most `reject_*` fixtures exist for and none of them
could make until now: a fixture written to exercise the type checker passes `run.sh` just as well
when a typo makes it die in the lexer. -/
def checkFailureStage (e : Expectation) (r : PipelineResult) : CheckResult :=
  let name := "failure stage"
  match e.outcome, e.failsAt, r.error with
  | .accept, _, _ =>
    { name, status := .skip, detail := "only meaningful for a rejection" }
  | .reject, none, _ =>
    { name, status := .skip, detail := "fixture does not say which stage should reject it" }
  | .reject, some want, none =>
    { name, status := .fail, detail := s!"expected a failure at {want}, the compile succeeded" }
  | .reject, some want, some err =>
    if err.stage == want then
      { name, status := .pass }
    else
      { name, status := .fail,
        detail := s!"expected a failure at {want}, got one at {err.stage} ({err.code})" }

/-- How far an accepted fixture got. Catches the failure mode `run.sh` is blind to by
construction: a module that compiles "successfully" while quietly stopping several stages short of
where it should. -/
def checkReachedStage (e : Expectation) (r : PipelineResult) : CheckResult :=
  let name := "reached stage"
  if e.outcome != .accept then
    { name, status := .skip, detail := "only meaningful for an acceptance" }
  else if !r.succeeded then
    -- The outcome check already reports this; repeating it as a second failure would just double
    -- count one problem.
    { name, status := .skip, detail := "the compile failed — see the outcome check" }
  else
    let want := e.reaches.getD (Expectation.defaultReaches r)
    if r.reached.reaches want then
      { name, status := .pass }
    else
      { name, status := .fail,
        detail := s!"expected the compile to complete through {want}, it stopped after {r.reached}" }

/-- Which error came out. Stable across rewording, unlike the message: `code` is the identity, and
the registry guarantees it names exactly one diagnostic. -/
def checkErrorCode (e : Expectation) (r : PipelineResult) : CheckResult :=
  let name := "error code"
  match e.errorCode, r.error with
  | none, _ => { name, status := .skip, detail := "fixture does not say which error it expects" }
  | some want, none =>
    { name, status := .fail, detail := s!"expected error {want}, the compile succeeded" }
  | some want, some err =>
    if err.code == want then
      { name, status := .pass }
    else
      { name, status := .fail, detail := s!"expected error {want}, got {err.code} at {err.stage}" }

/-- How many times each code was warned, as a sorted association list. Sorted so that two runs'
tallies compare and print in a fixed order regardless of `Std.HashMap` iteration. -/
private def warningTally (warnings : List PipelineWarning) : List (DiagnosticCode × Nat) :=
  let codes := warnings.map CompilerDiagnostic.code
  codes.eraseDups.map (λ c ↦ (c, codes.countP (· == c)))
    |>.mergeSort (λ a b ↦ compare a.1 b.1 != .gt)

/-- Render a tally the way a failure detail should read. -/
private def tallyString (tally : List (DiagnosticCode × Nat)) : String :=
  if tally.isEmpty then "none"
  else String.intercalate ", " (tally.map λ (c, n) ↦ if n == 1 then s!"{c}" else s!"{c}×{n}")

/-- Which warnings fired, by code and count.

Reads `warnings`, the unfiltered record of what the passes raised, rather than `reportedWarnings`.
The runner compiles a fixture with no `-W` flags, so the two agree — but the fixture is asserting
what the *compiler produces*, which is the thing that should not change silently. What `-W` then
shows is `checkSuppression`'s question.

Strict: a warning the fixture did not list is a failure unless it opted into
`allowExtraWarnings`. That is the whole value of the check — a new spurious warning anywhere in
the corpus has to be acknowledged by someone, rather than accumulating unnoticed the way it does
when nothing looks at warnings at all. -/
def checkWarnings (e : Expectation) (r : PipelineResult) : CheckResult :=
  let name := "warnings"
  let got := warningTally r.warnings
  let want := e.warnings.map (λ w ↦ (w.code, w.count)) |>.mergeSort (λ a b ↦ compare a.1 b.1 != .gt)
  let missing := want.filter λ (c, n) ↦ got.find? (·.1 == c) != some (c, n)
  let extra := got.filter λ (c, _) ↦ (want.find? (·.1 == c)).isNone
  if missing.isEmpty && (extra.isEmpty || e.allowExtraWarnings) then
    { name, status := .pass }
  else
    let parts :=
      (if missing.isEmpty then [] else [s!"expected {tallyString missing}"])
      ++ (if extra.isEmpty || e.allowExtraWarnings then [] else [s!"unexpected {tallyString extra}"])
    { name, status := .fail,
      detail := s!"{String.intercalate "; " parts} (got {tallyString got})" }

/-- Every check, against one compile. -/
def runChecks (e : Expectation) (r : PipelineResult) : List CheckResult :=
  [checkOutcome e r, checkFailureStage e r, checkErrorCode e r, checkReachedStage e r,
   checkWarnings e r]

/-- `suppressible`'s check, which needs a *second* compile and so cannot be a pure function of the
first: `r` is the fixture compiled under `flags`, which turn `warningName` off, and the warning must
be gone while the outcome stays what it was.

Asserts against `reportedWarnings`, not `warnings`. The distinction is the compiler's own design and
not an accident: a pass raises every warning it finds, and `-W` decides which of them are reported.
`warnings` is therefore never affected by `-W`, and a check reading it would pass no matter what the
flag did. -/
def checkSuppression (e : Expectation) (flags : FlagsEnv) (warningName : String)
    (r : PipelineResult) : CheckResult :=
  let name := s!"suppression of -W{warningName}"
  let stillThere := (r.reportedWarnings flags).filter (CompilerDiagnostic.name · == warningName)
  let got : Outcome := if r.succeeded then .accept else .reject
  if !stillThere.isEmpty then
    { name, status := .fail,
      detail := s!"-Wno-{warningName} did not suppress it ({stillThere.length} still reported)" }
  else if got != e.outcome then
    { name, status := .fail,
      detail := s!"-Wno-{warningName} changed the outcome to {got}; a warning toggle must not" }
  else
    { name, status := .pass }

end
