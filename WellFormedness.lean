module

public import WellFormedness.Labelling
public import WellFormedness.WellScoped
public import WellFormedness.Declarations
public import WellFormedness.Restrictions
public import Elaborator

public section

/-! Ties `WellFormedness/`'s five checks together, mirroring `Elaborator/Elaborator.lean`'s role
for type checking: one entry point, called on `Driver/Modules.lean`'s `compileModule` output right
after type checking succeeds, from outside the driver (`Fugue.lean`) — the driver's own job stops
at type checking plus caching. -/

/-- `Labelling` → `WellScoped` → `Declarations` → `Restrictions` → `ReceiveChannels`, in that
order, against a module's own embedded `pcalAlgorithm` — a no-op if it has none (an ordinary TLA⁺
module with no PlusCal algorithm has nothing for any of these five checks to say anything about).
`Restrictions`'s global-variable-reference and transitive-call checks need the whole module, not
just the algorithm — its own `declarations₁ ++ declarations₂` (to resolve a same-module
`Origin.module mod.name` reference without a `lookupForeign` round-trip) and `mod.name` (to tell a
same-module reference apart from a foreign one) — hence this takes the whole `TypedModule` rather
than just the algorithm, unlike the other three checks.

Returns the module rather than `Unit`: `ReceiveChannels` is a checker everywhere except one case,
where it drops a `@mailbox` no `receive` uses (`WellFormedness/Restrictions.lean`), and downstream
stages must see the module it produced rather than the one it was given. Every other check here is
pure inspection, so the module comes back unchanged when no process declares an unused mailbox. -/
def TypedTLAPlus.Module.checkWellFormed {m : Type → Type} [Monad m]
    [MonadDiagnostic WellFormednessWarning WellFormednessError m] [MonadForeignLookup m]
    (mod : TypedModule) : m TypedModule :=
  match mod.pcalAlgorithm with
  | none => pure mod
  | some algo => do
    TypedPlusCal.Algorithm.checkLabelling algo
    TypedPlusCal.Algorithm.checkWellScoped algo
    TypedPlusCal.Algorithm.checkDeclarations algo
    TypedPlusCal.Algorithm.checkRestrictions mod.name (mod.declarations₁ ++ mod.declarations₂) algo
    return { mod with pcalAlgorithm := some (← TypedPlusCal.Algorithm.checkReceiveChannels algo) }

end
