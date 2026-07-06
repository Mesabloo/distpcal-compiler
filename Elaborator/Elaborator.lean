import Elaborator.PlusCal

/-!
  Ties the whole checker together (§5.3 task 10): `CoreTLAPlus.Module.check`, threading `Γ`
  across `declarations₁` → the embedded PlusCal algorithm → `declarations₂`, and `Module.
  runChecker`, the one concrete monad instantiation this pass is ever run at — following
  `Desugarer/TLAPlus.lean`'s `SurfaceTLAPlus.Module.runDesugarer` entry-point pattern (a
  polymorphic `check` over `{m} [MonadElaborator m] [MonadPendingBounds m]`, picked apart into a
  real transformer stack only at the very end).

  **`Module.check` extends thesis Fig. 3.1.10, it doesn't literally implement it.** Fig. 3.1.10's
  own `Γ|Δ⊢M typeok` judgment is a flat `D :: M` declaration list — it has no embedded-PlusCal-
  algorithm case at all, because `CoreTLAPlus.Module`'s "`declarations₁` then an optional algorithm
  then `declarations₂`" shape is this project's own AST. So checking here is `Elaborator/
  Declarations.lean`'s `checkDeclarations` on `declarations₁`, then (if present) `Elaborator/
  PlusCal.lean`'s `checkAlgorithm`, then `checkDeclarations` again on `declarations₂` — `Γ`
  threaded from `declarations₁` into the algorithm, but not further.

  **`declarations₂` does *not* see the algorithm's own global `variables`/`channels`/`fifos`
  names** (confirmed with the project owner) — PlusCal-internal declarations don't leak into the
  surrounding TLA⁺ module's own `Γ`; `checkAlgorithm` keeps them scoped to itself. `declarations₂`
  is checked against the same `Γ` `declarations₁` left behind, exactly as if the algorithm weren't
  there at all.
-/

open TypedTLAPlus (Typ MVarId)

/-- The checker's own output type — the checker's own cached-module representation. Lives here
(not `Driver/Modules.lean`, which merely consumes it) since it's what `Module.check`/`runChecker`
below actually produce. -/
abbrev TypedModule := TypedTLAPlus.Module TypedPlusCal.Algorithm TypedTLAPlus.Typ

namespace CoreTLAPlus

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/--
  `Γ ⊢ M typeok` (thesis Fig. 3.1.10, extended per the module doc): `declarations₁`, then the
  embedded algorithm (if any, checked but *not* extending `Γ` any further — module doc), then
  `declarations₂` against the same `Γ` `declarations₁` left behind.
-/
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

/--
  Run the checker against its one concrete monad instantiation: `Γ`'s `ReaderT`, the
  metavariable/pending-bounds contexts and fresh-name counter as nested `StateT`s, and `TCError`
  reporting via `Except` — matching `SurfaceTLAPlus.Module.runDesugarer`'s own "discard whatever
  final state nothing needs again" shape. `Γ₀` is the caller-supplied initial context (`Elaborator/
  Declarations.lean`'s `builtinContext`, merged with any `EXTENDS`-resolved dependencies' own
  exported bindings — `Driver/Modules.lean`'s job, not this function's: `Module.check` itself never
  hardcodes a seed, only ever reads whatever `Γ` is already ambient).
-/
def CoreTLAPlus.Module.runChecker (Γ₀ : Context) (mod : CoreTLAPlus.Module SrcAlgorithm (Option Typ)) :
    Except TCError TypedModule :=
  let check : ReaderT Context
      (StateT (MetavarContext Typ) (StateT PendingBounds (StateT Nat (Except TCError)))) TypedModule :=
    mod.check
  (((check.run Γ₀).run' ∅).run' ∅).run' 0
