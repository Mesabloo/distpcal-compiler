module

public import Guarded2Network.Errors
public import Extra.Do

@[expose] public section

/-!
  The monad a `Guarded2Network` correctness proof runs the pass at.

  `Guarded2Network.PlusCal`'s pass runs monad-polymorphically (`{m} [Monad m] [MonadDiagnostic
  Empty G2NError m] [MonadFresh m]`, plus function-scoped `StateT`s), which is right for the *pass*
  but not for *proving things about it* — `wp⟦·⟧` and the `[spec]` lemmas that drive `mvcgen` are
  stated per stack, so a proof has to pin `m` to one. Every layer (`ExceptT`, `StateT`, `Id`)
  already has `WP`/`WPMonad` in `Std.Do`, so pinning it here needs no new metatheory: only the two
  `MonadFresh` lifts (`Common/Fresh.lean`) and the `MonadWriter` instance below, neither of which
  existed before this pass needed them.

  Its own file rather than `Guarded2Network/Lemmas.lean`, where it started: the proof files import
  it, and `Lemmas.lean` imports them.
-/

/-- The concrete monad a `Guarded2Network` correctness proof runs the pass at. Every theorem about
the pass is a Hoare triple over this stack — `⦃P⦄ pass … ⦃⇓? r => Q r⦄` — never an equation about
what one `.run` happened to return. -/
abbrev G2NM := ExceptT G2NError (StateT Nat Id)

namespace Guarded2Network

/-- `G2NM` never actually warns (`MonadDiagnostic Empty G2NError m` — `Empty` says so at the type
level), so this instance's job is only to let `G2NM` satisfy the `MonadWriter` half of
`MonadDiagnostic` at all: `List Empty` has exactly one inhabitant (`[]`), so `tell`/`listen`/`pass`
are forced and lawful regardless of implementation. Scoped rather than a plain global instance —
sound only because `α = Empty` specifically; a pass with real warnings needs the general `DiagT`
machinery instead, and leaving this loose would let a monad already wired for real warnings
silently resolve here instead. -/
scoped instance : MonadWriter (List Empty) G2NM where
  tell _ := pure ()
  listen x := do let a ← x; pure (a, [])
  pass x := do let (a, _) ← x; pure a

end Guarded2Network

end
