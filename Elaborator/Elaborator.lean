import Elaborator.PlusCal

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
  let (decls1', bindings1) ← checkDeclarations mod.declarations₁
  extendAll bindings1 do
    let pcalAlgorithm' ← mod.pcalAlgorithm.mapM checkAlgorithm
    let (decls2', _) ← checkDeclarations mod.declarations₂
    return {
      name := mod.name
      «extends» := mod.extends
      declarations₁ := decls1'
      pcalAlgorithm := pcalAlgorithm'
      declarations₂ := decls2'
    }

end CoreTLAPlus

/-- Run the checker against its one concrete monad instantiation: `Γ`'s `ReaderT`, the
metavariable/pending-bounds contexts and fresh-name counter as nested `StateT`s, and `TCError`
reporting via `Except`. `Γ₀` is the caller-supplied initial context. -/
def CoreTLAPlus.Module.runChecker (Γ₀ : Context) (mod : CoreTLAPlus.Module SrcAlgorithm (Option Typ)) :
    Except TCError TypedModule :=
  let check : ReaderT Context
      (StateT (MetavarContext Typ) (StateT PendingBounds (StateT Nat (Except TCError)))) TypedModule :=
    mod.check
  (((check.run Γ₀).run' ∅).run' ∅).run' 0
