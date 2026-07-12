module

public import Elaborator

public section


/-! The one effect the well-formedness pass needs beyond ordinary monadic error-reporting:
fetching a module's checked declarations by name, to resolve what a `.var`'s `Origin.module`
tag points at (used by `WellFormedness/Restrictions.lean`'s global-variable and transitive-call
checks). -/

/-- Fetches a module's checked representation by name — the one seam between `WellFormedness/`
and `Driver/`'s module cache. Kept as its own class (rather than `WellFormedness/` importing
`Driver/Modules.lean` directly) to avoid a cycle: `Driver/Modules.lean` calls into
`WellFormedness/` to run the check after type-checking succeeds. No provenance payload needed —
origin travels on the AST itself, so this only answers "what did module `name` declare," not
"who declared this name." -/
class MonadForeignLookup (m : Type → Type) where
  /-- The named module's checked declarations, if it exists — `none` should be unreachable in
  practice (a name with `Origin.module name` only exists because that module already
  type-checked). -/
  lookupForeign : String → m (Option TypedModule)
export MonadForeignLookup (lookupForeign)

/-- Generic lift through `StateT` — lets `WellFormedness/Restrictions.lean`'s transitive walk
add a `StateT (Std.HashSet (String × String))` layer (memoizing already-visited operator/
function bodies) on top of whatever concrete monad `Driver/Modules.lean` supplies
`MonadForeignLookup` at, without that monad needing to know about the state layer. -/
instance {m σ} [Monad m] [MonadForeignLookup m] : MonadForeignLookup (StateT σ m) where
  lookupForeign name := liftM (lookupForeign name : m _)

/-- Generic lift through `ExceptT` — lets a caller whose own ambient monad already has
`MonadForeignLookup` (e.g. `Driver/Modules.lean`'s `M`, tagged with a *different* error type)
run `TypedTLAPlus.Module.checkWellFormed` at `ExceptT WellFormednessError m`, catching its
`WellFormednessError`s locally without `m` itself needing to know about that error type. -/
instance {m ε} [Monad m] [MonadForeignLookup m] : MonadForeignLookup (ExceptT ε m) where
  lookupForeign name := liftM (lookupForeign name : m _)

/-- Generic lift through `DiagT` — same rationale as the `ExceptT` lift above, for a caller
running `TypedTLAPlus.Module.checkWellFormed`/`TypedTLAPlus.Expression.checkNode`'s own
`MonadDiagnostic`-shaped stack (`Fugue.lean`'s `runPassDiag`) rather than a bare `ExceptT`. -/
instance {m α β} [Monad m] [MonadForeignLookup m] : MonadForeignLookup (DiagT α β m) where
  lookupForeign name := liftM (lookupForeign name : m _)

end
