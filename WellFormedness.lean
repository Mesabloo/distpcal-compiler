module

public import WellFormedness.Labelling
public import WellFormedness.WellScoped
public import WellFormedness.Declarations
public import WellFormedness.Restrictions
public import Elaborator

public section

/-! Ties `WellFormedness/`'s four checks together, mirroring `Elaborator/Elaborator.lean`'s role
for type checking: one entry point, called on `Driver/Modules.lean`'s `compileModule` output right
after type checking succeeds, from outside the driver (`Fugue.lean`) — the driver's own job stops
at type checking plus caching. -/

/-- `Labelling` → `WellScoped` → `Declarations` → `Restrictions`, in that order, against a
module's own embedded `pcalAlgorithm` — a no-op if it has none (an ordinary TLA⁺ module with no
PlusCal algorithm has nothing for any of these four checks to say anything about).
`Restrictions`'s global-variable-reference and transitive-call checks need the whole module, not
just the algorithm — its own `declarations₁ ++ declarations₂` (to resolve a same-module
`Origin.module mod.name` reference without a `lookupForeign` round-trip) and `mod.name` (to tell a
same-module reference apart from a foreign one) — hence this takes the whole `TypedModule` rather
than just the algorithm, unlike the other three checks. -/
def TypedTLAPlus.Module.checkWellFormed {m : Type → Type} [Monad m]
    [MonadDiagnostic Empty WellFormednessError m] [MonadForeignLookup m] (mod : TypedModule) : m Unit :=
  match mod.pcalAlgorithm with
  | none => pure ()
  | some algo => do
    TypedPlusCal.Algorithm.checkLabelling algo
    TypedPlusCal.Algorithm.checkWellScoped algo
    TypedPlusCal.Algorithm.checkDeclarations algo
    TypedPlusCal.Algorithm.checkRestrictions mod.name (mod.declarations₁ ++ mod.declarations₂) algo

end
