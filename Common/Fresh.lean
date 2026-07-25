module

meta import CustomPrelude

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

instance {m} [Monad m] [MonadStateOf Nat m] : MonadFresh m where
  fresh := do
    let n ← get
    set (n + 1)
    return n

/-- Generic lift through `ReaderT` — same rationale as `WellFormedness/Monad.lean`'s lifts for
`MonadForeignLookup`. Lets a pass that is only told `[MonadFresh m]` still add a local `ReaderT`
layer and call something needing `MonadFresh` under it (`Desugarer/PlusCal.lean`'s
`desugarMailboxArg` wraps `Expression.desugar`'s `@`-reader this way). The `MonadStateOf Nat`
instance above can't cover that case: it needs the counter's *concrete* state effect, which an
abstract `[MonadFresh m]` doesn't expose. -/
instance {ρ m} [MonadFresh m] : MonadFresh (ReaderT ρ m) where
  fresh := liftM (MonadFresh.fresh : m Nat)

/-- Backing store for `MonadFresh`: one counter for the whole `fugue` process, mirroring
`Driver/Modules.lean`'s `sourceRegistryRef`/`moduleCacheRef` pattern (a global `IO.Ref`, not a
`StateT` layer threaded through each pass). Every pass — the checker, the desugarer,
`Computable2Guarded`, `Guarded2Network` — draws fresh names from this same counter for the whole
compile rather than a separate one per pass, so compiler-introduced names can never collide
across passes. No pass needs to thread a `Nat` counter itself: `MonadFresh`'s generic instance
reaches it through any standard transformer stack over `IO`, same as
`MonadModuleCache`/`MonadSourceRegistry` reach `Driver/Modules.lean`'s own refs. -/
initialize freshCounterRef : IO.Ref Nat ← IO.mkRef 0

instance : MonadStateOf Nat IO := freshCounterRef.toMonadStateOf

end
