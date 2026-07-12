module

public import Elaborator.PlusCal

public section

/-!
  Ties the whole checker together: `CoreTLAPlus.Module.check`, threading `Γ` across
  `declarations₁` → the embedded PlusCal algorithm → `declarations₂`, and `Module.runChecker`,
  the one concrete monad instantiation this pass is ever run at.

  The embedded algorithm is checked but does *not* extend `Γ` any further — PlusCal-internal
  declarations (`variables`/`channels`/`fifos`) don't leak into the surrounding TLA⁺ module's own
  `Γ`. `declarations₂` is checked against the same `Γ` that `declarations₁` left behind, exactly
  as if the algorithm weren't there at all.
-/

open TypedTLAPlus (Typ MVarId)

/-- The checker's own output type — a module's cached representation once checked. -/
abbrev TypedModule := TypedTLAPlus.Module TypedPlusCal.Algorithm TypedTLAPlus.Typ

namespace CoreTLAPlus

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/-- `Γ ⊢ M typeok`: `declarations₁`, then the embedded algorithm (if any), then `declarations₂`
against the same `Γ` `declarations₁` left behind. -/
def Module.check (mod : CoreTLAPlus.Module SrcAlgorithm (Option Typ)) : m TypedModule := do
  let (decls1', bindings1) ← checkDeclarations mod.name mod.declarations₁
  extendAllBindings bindings1 do
    let pcalAlgorithm' ← mod.pcalAlgorithm.mapM checkAlgorithm
    let (decls2', _) ← checkDeclarations mod.name mod.declarations₂
    return {
      name := mod.name
      «extends» := mod.extends
      declarations₁ := decls1'
      pcalAlgorithm := pcalAlgorithm'
      declarations₂ := decls2'
    }

end CoreTLAPlus

/-- Run the checker against its one concrete monad instantiation: `Γ`'s `ReaderT`, the
metavariable/pending-bounds contexts as nested `StateT`s, and `MonadDiagnostic`'s `TCError`/
`TCWarning` reporting via `DiagT` — so a warning emitted before a later fatal error still
survives (`PLAN.md` §9.14). No checking rule emits a `TCWarning` yet, but the capability is wired
through uniformly with every other pass. `Γ₀` is the caller-supplied initial context. `DiagT`'s
own base monad is `IO`, not `Id`: fresh-name generation (`MonadFresh`, needed by `Subtyping.lean`)
now draws from `Common/Fresh.lean`'s single process-wide `IO.Ref` counter rather than a `StateT
Nat` layered in here, so this stack needs `IO` reachable to pick that instance up. -/
def CoreTLAPlus.Module.runChecker (Γ₀ : Context) (mod : CoreTLAPlus.Module SrcAlgorithm (Option Typ)) :
    DiagT TCWarning TCError IO TypedModule :=
  let check : ReaderT Context
      (StateT (MetavarContext Typ) (StateT PendingBounds (DiagT TCWarning TCError IO))) TypedModule :=
    mod.check
  ((check.run Γ₀).run' ∅).run' ∅

end
