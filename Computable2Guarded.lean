module

public import Computable2Guarded.CFlow
public import Computable2Guarded.Par
public import Computable2Guarded.FlatReord

public section

/-!
  `Computable2Guarded`'s entry point — `𝒞_D→G := 𝒞_reord ∘ 𝒞_flat ∘ 𝒞_par ∘ 𝒞_cflow` (thesis §3.2.2),
  matching the `<InputType>.<verb>` convention `Typed2Computable`/`WellFormedness` already use.
  `𝒞_cflow`/`𝒞_par` run first, both whole-`Algorithm` rewrites *within* `ComputablePlusCal`'s own
  type (order between them doesn't matter, thesis p. 21); only then does the merged `𝒞_flat`/
  `𝒞_reord` walk (`FlatReord.walkBlock`) actually change shape, applied per `(label, Block)` pair
  across every thread of every process. `Declarations`/`Process`/`Algorithm`'s outer shape is
  otherwise a plain structural copy — `ComputablePlusCal`'s `Typ`/`Expression` and this pass's own
  pinning of `GuardedPlusCal`'s are the identical *types*, so every field's own value needs no
  conversion, only `threads` genuinely changes shape (`AtomicBlock.branches` is `FlatReord.
  walkBlock`'s own output). `Declarations` itself is still a distinct (if identically-shaped)
  *structure* between the two namespaces (`GuardedPlusCal.Declarations`'s own doc comment: "a
  fresh copy of `ElaboratedPlusCal.Declarations`'s shape", not an `abbrev` over it), so
  `Declarations.toGuarded` below is a one-line field-for-field repackaging, not a real
  translation.
-/

/-- `ElaboratedPlusCal.Declarations` and `GuardedPlusCal.Declarations` share every field's name
and type (see the module doc above) — this only exists because they're nominally distinct
`structure`s, not because anything actually needs converting. -/
def ComputablePlusCal.Declarations.toGuarded (d : ComputablePlusCal.Declarations) :
    ComputableGuardedPlusCal.Declarations :=
  { «variables» := d.variables, channels := d.channels, fifos := d.fifos }

def ComputablePlusCal.Algorithm.toGuarded {m : Type → Type} [Monad m] [MonadFresh m]
    [MonadDiagnostic Empty GuardedError m] (algo : ComputablePlusCal.Algorithm) : m ComputableGuardedPlusCal.Algorithm := do
  let algo ← algo.cflow
  let algo ← algo.par
  let processes ← algo.processes.mapM λ p ↦ do
    let threads ← p.threads.mapM (·.mapM λ (label, block) ↦ do
      pure ({ label, branches := ← FlatReord.walkBlock [] [] block } : ComputableGuardedPlusCal.AtomicBlock))
    pure ({ mailbox := p.mailbox, isFair := p.isFair, name := p.name, «=|∈» := p.«=|∈»,
            id := p.id, localState := ComputablePlusCal.Declarations.toGuarded p.localState, threads }
      : ComputableGuardedPlusCal.Process)
  pure { isFair := algo.isFair, name := algo.name,
         globalState := ComputablePlusCal.Declarations.toGuarded algo.globalState, processes }

end
