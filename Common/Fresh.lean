module

meta import CustomPrelude

public section


/--
  A monotonic counter for generating hygienic fresh names, needed wherever a pass introduces a
  variable that must not collide with anything a user could have written (§2's identifier-hygiene
  discipline, cross-cutting across every pass — first needed by expression desugaring's
  tuple-pattern/multi-binder-collapse transformations, `Desugarer/TLAPlus.lean`, and expected to
  recur at `Computable2Guarded`'s `𝒞_par`, §5.4).

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

end
