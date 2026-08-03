module

meta import CustomPrelude
public import Common.Errors

public section


/--
  A monotonic counter for generating hygienic fresh names, needed wherever a pass introduces a
  variable that must not collide with anything a user could have written — used by expression
  desugaring's tuple-pattern/multi-binder-collapse transformations, and by
  `Computable2Guarded`'s `𝒞_par` and `Guarded2Network`'s `inbox`/`rx` naming.

  Its own tiny effect class (like `MonadModuleCache`, not folded into `FlagsEnv`) since it's a
  mutable-store effect, not a Reader.
-/
class MonadFresh (m : Type → Type) where
  fresh : m Nat

/--
  A fresh identifier, guaranteed distinct from any name a user could have written: `$` cannot
  appear in a TLA⁺ identifier (the lexer's `identifierOrKeyword` only ever accepts letters,
  digits, and `_`), so no scope-tracking is needed to avoid collisions — a syntactic argument,
  not a runtime check.
-/
@[expose] def freshName {m} [Monad m] [MonadFresh m] (namePrefix := "fresh") : m String := do
  return s!"{namePrefix}${← MonadFresh.fresh}"

/-!
  The lifts below carry `MonadFresh` through each transformer a pass stacks on top of the monad
  that actually owns the counter — one per layer that shows up in a pass's concrete runner
  (`ReaderT` for `@`'s context and `Γ`, `StateT` for the checker's metavariable/pending-bounds
  contexts, `DiagT` for every pass's diagnostics). Written on `MonadFresh` itself rather than
  obtained by lifting an underlying `MonadStateOf Nat`: a pass says what it needs (`MonadFresh`),
  not how the counter is stored, and the owner is free to keep it as a field of a larger state
  record — which `Driver/Modules.lean`'s `DriverState` does.
-/

/-- Lift through `ReaderT` — lets a pass told only `[MonadFresh m]` add a local `ReaderT` layer and
still call something needing `MonadFresh` under it (`Desugarer/PlusCal.lean`'s `desugarMailboxArg`
wraps `Expression.desugar`'s `@`-reader this way). -/
instance {ρ m} [MonadFresh m] : MonadFresh (ReaderT ρ m) where
  fresh := liftM (MonadFresh.fresh : m Nat)

/-- Lift through `StateT` — `Elaborator.lean`'s `runChecker` runs two of them (the metavariable
context and the pending bounds) between the checker and its base monad. -/
instance {σ m} [Monad m] [MonadFresh m] : MonadFresh (StateT σ m) where
  fresh := liftM (MonadFresh.fresh : m Nat)

/-- Lift through `DiagT` — every pass reports through one, so this is the layer that stands
between essentially any pass and whatever owns its counter. -/
instance {α β m} [Monad m] [MonadFresh m] : MonadFresh (DiagT α β m) where
  fresh := liftM (MonadFresh.fresh : m Nat)

/-- Lift through `ExceptT` — needed the moment a pass's own runner is a bare `ExceptT` rather than
going through `DiagT`/`MonadDiagnostic` (`Guarded2Network`'s `G2NM`, `VerifiedCompiler/`, is the
first). -/
instance {ε m} [Monad m] [MonadFresh m] : MonadFresh (ExceptT ε m) where
  fresh := liftM (MonadFresh.fresh : m Nat)

/-- The base instance for a pass whose own runner owns a bare `Nat` counter directly, rather than
threading it through `Driver/Modules.lean`'s `DriverState` (that file's own instance, keyed on
`MonadStateOf DriverState m`). `Guarded2Network`'s `G2NM := ExceptT G2NError (StateT Nat Id)` is
the first stack that wants this — every earlier pass runs under the driver's counter instead. -/
instance {m} [Monad m] [MonadStateOf Nat m] : MonadFresh m where
  fresh := modifyGet λ n ↦ (n, n + 1)

/-!
  The counter itself lives in `Driver/Modules.lean`'s `DriverState`, one per compile, and every
  pass — the checker, the desugarer, `Computable2Guarded`, `Guarded2Network` — draws from that
  same counter for the whole compile, so compiler-introduced names cannot collide across passes.
  Deliberately not a global `IO.Ref`: a process-wide counter makes a compile's generated names
  depend on how many compiles ran before it in the same process, which is invisible in the CLI
  (one compile per process) and actively wrong for the regression runner, which compiles many
  fixtures in one process and checks its output for determinism.
-/

end
