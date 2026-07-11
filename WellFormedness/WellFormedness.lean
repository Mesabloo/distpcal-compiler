import WellFormedness.Labelling
import WellFormedness.WellScoped
import WellFormedness.Declarations
import WellFormedness.Restrictions
import Elaborator.Elaborator

/-! Ties `WellFormedness/`'s four checks together, mirroring `Elaborator/Elaborator.lean`'s own
role for type checking: one entry point `Driver/Modules.lean`'s `compileModule` calls right
after `mod.runChecker` succeeds. -/

/-- `Labelling` → `WellScoped` → `Declarations` → `Restrictions`, in that order, against a
module's own embedded `pcalAlgorithm` — a no-op if it has none (an ordinary TLA⁺ module with no
PlusCal algorithm has nothing for any of these four checks to say anything about).
`Restrictions`'s checks 2(c)/3-transitive need the whole module, not just the algorithm — its
own `declarations₁ ++ declarations₂` (to resolve a same-module `Origin.module mod.name`
reference without a `lookupForeign` round-trip) and `mod.name` (to tell a same-module reference
apart from a foreign one) — hence this takes the whole `TypedModule` rather than just the
algorithm, unlike the other three checks. -/
def TypedTLAPlus.Module.checkWellFormed {m : Type → Type} [Monad m]
    [MonadExceptOf WellFormednessError m] [MonadForeignLookup m] (mod : TypedModule) : m Unit :=
  match mod.pcalAlgorithm with
  | none => pure ()
  | some algo => do
    algo.checkLabelling
    algo.checkWellScoped
    algo.checkDeclarations
    algo.checkRestrictions mod.name (mod.declarations₁ ++ mod.declarations₂)
