module

meta import CustomPrelude

public section


/--
  A monotonic counter for generating hygienic fresh names, needed wherever a pass introduces a
  variable that must not collide with anything a user could have written (§2's identifier-hygiene
  discipline, cross-cutting across every pass — first needed by expression desugaring's
  tuple-pattern/multi-binder-collapse transformations, `Desugarer/TLAPlus.lean`, and recurring at
  `Computable2Guarded`'s `𝒞_par` and `Guarded2Network`'s `inbox`/`rx` naming).

  Kept as its own tiny effect class (like `MonadModuleCache`, not folded into `FlagsEnv`) since
  it's a genuine mutable-store effect, not a Reader.
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

/-- Backing store for `MonadFresh`, one single counter for the whole `fugue` process —
mirroring `Driver/Modules.lean`'s `sourceRegistryRef`/`moduleCacheRef` pattern (a global `IO.Ref`,
not a `StateT` layer threaded explicitly through every pass's own concrete monad
instantiation). Every pass that needs a fresh name — the checker's `Subtyping.lean`, the
desugarer's tuple-pattern/multi-binder collapse and `desugarMailboxArg`, `Computable2Guarded`'s
`𝒞_par`, `Guarded2Network`'s `inbox`/`rx` naming — draws from this *same* counter, for the whole
compile, not a separate one per pass restarted at `0`: strictly stronger hygiene (no risk of two
different passes' compiler-introduced names ever colliding with *each other*, only slightly more
conservative than the minimum each pass individually needs) and it means no pass's own
`toGuarded`/`toNetwork`/`runChecker`/`runDesugarer`-style entry point needs to thread a `Nat`
counter through its return type or its caller's `.run`/`.run'` chain at all — `MonadFresh`'s
existing generic instance above picks it up automatically through any standard transformer stack
built over `IO` (`ExceptT`/`ReaderT`/`StateT`/`DiagT` all lift `MonadStateOf` from their base
monad), the same way `MonadModuleCache`/`MonadSourceRegistry` already reach through `Driver/
Modules.lean`'s own `M` stack to their own backing refs. -/
initialize freshCounterRef : IO.Ref Nat ← IO.mkRef 0

instance : MonadStateOf Nat IO := freshCounterRef.toMonadStateOf

end
