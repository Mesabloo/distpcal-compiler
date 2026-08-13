module

public import WellFormedness.Errors
public import Core.TypedPlusCal.Syntax

public section

/-!
  Pure structural/type-shape checks over a `TypedPlusCal.Algorithm`'s declarations, no
  expression-walking or cross-module lookup needed:
  - No `variables` entry (algorithm- or process-level) may have a Channel-shaped type — declare
    a channel via `channels`/`fifos` instead.
  - A process's own `localState.channels`/`.fifos` must be empty — defense-in-depth; the parser
    already guarantees this, but nothing in `CorePlusCal`'s/`TypedPlusCal`'s own type enforces
    it structurally.
  - The algorithm's own `globalState.variables` must be empty — no shared mutable state across
    processes. `globalState.channels`/`.fifos` and every `Process.localState.variables` are
    untouched by this.
-/

variable {m : Type → Type} [Monad m] [MonadDiagnostic WellFormednessWarning WellFormednessError m]

/-- Rejects a Channel-shaped entry in one `Declarations` value's `variables` list. Position is
the entry's own initializer expression if one exists, `SourceSpan.placeholder` otherwise (matches
`WellFormedness/WellScoped.lean`'s `namesWithPos`, same gap — `variables` carries no position for
the bare name token). -/
private def checkNoChannelTypedVariables (d : TypedPlusCal.Declarations) : m Unit :=
  d.variables.forM λ (x, τ, _, init) ↦ do
    if τ.isChannelLike then
      throw (.channelTypedVariable (init.elim SourceSpan.placeholder (posOf ·.2)) x)

/-- A process's own local `channels`/`fifos` must both be empty. Position is `p.id`'s own —
always present and positioned (`Elaborator/PlusCal.lean` type-checks it via `checkExprR`), unlike
the channel/fifo entries themselves, which don't exist to point at when the point is there
shouldn't be any. -/
private def checkNoLocalChannels (p : TypedPlusCal.Process) : m Unit :=
  unless p.localState.channels.isEmpty ∧ p.localState.fifos.isEmpty do
    throw (.nonEmptyLocalChannels (posOf p.id) p.name)

/-- The algorithm's own `globalState.variables` must be empty. Reuses
`checkNoChannelTypedVariables`'s position convention, even though every entry here is an error
regardless of its type. -/
private def checkNoGlobalPlusCalVariables (algo : TypedPlusCal.Algorithm) : m Unit :=
  algo.globalState.variables.forM λ (x, _, _, init) ↦
    throw (.globalPlusCalVariable (init.elim SourceSpan.placeholder (posOf ·.2)) x)

/-- Runs all three checks over a whole algorithm. The empty-`globalState.variables` check runs
before the channel-shaped-entry check on `globalState`: every algorithm-level `variables` entry
is already banned regardless of its type, so checking channel-shapedness first would report the
misleading "declare it via `channels`/`fifos` instead" when the real problem is that no
`variables` keyword is allowed there at all. The channel-shapedness check still runs afterward,
but is a no-op there by construction. -/
def TypedPlusCal.Algorithm.checkDeclarations (algo : TypedPlusCal.Algorithm) : m Unit := do
  checkNoGlobalPlusCalVariables algo
  checkNoChannelTypedVariables algo.globalState
  for p in algo.processes do
    checkNoChannelTypedVariables p.localState
    checkNoLocalChannels p

end
