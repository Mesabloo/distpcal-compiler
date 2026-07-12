module

public import WellFormedness.Errors
public import Core.TypedPlusCal.Syntax

public section

/-!
  Pure structural/type-shape checks over a `TypedPlusCal.Algorithm`'s declarations, no
  expression-walking and no cross-module lookup needed — `PLAN.md` §5.2a's checks 2(a), 2(b),
  2(d):
  - **2(a)**: no `variables` entry (algorithm-level or process-level) may have a Channel-shaped
    type — declare a channel via `channels`/`fifos` instead.
  - **2(b)**: a process's own `localState.channels`/`.fifos` must be empty — defense-in-depth;
    the parser already guarantees this today, but nothing in `CorePlusCal`'s/`TypedPlusCal`'s
    own type enforces it structurally.
  - **2(d)**: the algorithm's own `globalState.variables` must be empty — shared mutable state
    across processes isn't allowed. `globalState.channels`/`.fifos` (the legitimate algorithm-
    level `fifos c1:τ1,...` form) and every `Process.localState.variables` (genuine per-process
    state) are untouched by this.
-/

/-- Check 2(a) over one `Declarations` value's `variables` list: reject a Channel-shaped entry.
Position is the entry's own initializer expression if one exists, `SourceSpan.placeholder`
otherwise (matches `WellFormedness/WellScoped.lean`'s `namesWithPos`, same underlying gap —
`variables` doesn't carry a position for the bare name token itself). -/
private def checkNoChannelTypedVariables {m : Type → Type} [Monad m]
    [MonadDiagnostic Empty WellFormednessError m] (d : TypedPlusCal.Declarations) : m Unit :=
  d.variables.forM λ (x, τ, _, init) ↦ do
    if τ.isChannelLike then
      throw (.channelTypedVariable (init.elim SourceSpan.placeholder (posOf ·.2)) x)

/-- Check 2(b): a process's own local `channels`/`fifos` must both be empty. Position is
`p.id`'s own — always present and always positioned (`Elaborator/PlusCal.lean` type-checks it
via `checkExprR`), unlike the channel/fifo entries themselves (which don't exist to point at
when the point is that there shouldn't be any). -/
private def checkNoLocalChannels {m : Type → Type} [Monad m] [MonadDiagnostic Empty WellFormednessError m]
    (p : TypedPlusCal.Process) : m Unit :=
  unless p.localState.channels.isEmpty ∧ p.localState.fifos.isEmpty do
    throw (.nonEmptyLocalChannels (posOf p.id) p.name)

/-- Check 2(d): the algorithm's own `globalState.variables` must be empty. Reuses
`checkNoChannelTypedVariables`'s same position convention for consistency, even though every
entry here is an error regardless of its type. -/
private def checkNoGlobalPlusCalVariables {m : Type → Type} [Monad m]
    [MonadDiagnostic Empty WellFormednessError m] (algo : TypedPlusCal.Algorithm) : m Unit :=
  algo.globalState.variables.forM λ (x, _, _, init) ↦
    throw (.globalPlusCalVariable (init.elim SourceSpan.placeholder (posOf ·.2)) x)

/-- Checks 2(a)/2(b)/2(d) together, over a whole algorithm. 2(d) runs before 2(a) on
`globalState` specifically: every algorithm-level `variables` entry is already banned outright
by 2(d) regardless of its type, so checking 2(a) first there would report the misleading
"declare it via `channels`/`fifos` instead" for a case where the real problem is "no `variables`
keyword at all is allowed here" — 2(a) still runs afterward for consistency with the plan's own
"algorithm- and process-level" wording, but is a no-op by construction once 2(d) has already
required the list to be empty. -/
def TypedPlusCal.Algorithm.checkDeclarations {m : Type → Type} [Monad m]
    [MonadDiagnostic Empty WellFormednessError m] (algo : TypedPlusCal.Algorithm) : m Unit := do
  checkNoGlobalPlusCalVariables algo
  checkNoChannelTypedVariables algo.globalState
  for p in algo.processes do
    checkNoChannelTypedVariables p.localState
    checkNoLocalChannels p

end
