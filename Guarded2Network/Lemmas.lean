module

public import Guarded2Network.PlusCal
public import Std.Do.WP

@[expose] public section

/-!
  Proof support for `Guarded2Network`'s refinement proof (item 7, `.claude/plans/
  item7-refinement-proof.md`). Everything about the pass itself — the AST transformation, its own
  denotational semantics, the correctness statement — lives elsewhere; this file is where the
  reasoning-specific machinery accumulates.

  `Guarded2Network.PlusCal`'s pass runs monad-polymorphically (`{m} [Monad m] [MonadDiagnostic
  Empty G2NError m] [MonadFresh m]`, plus function-scoped `StateT`s), which is right for the
  *pass* but not for *proving things about it* — `mvcgen`/`mspec` need a concrete stack Lean
  already has `Std.Do.WP`/`WPMonad` instances for, so a proof pins `m` to one: `G2NM` below. Every
  layer (`ExceptT`, `StateT`, `Id`) already has `WP`/`WPMonad` in `Std.Do`, so this needs no new
  metatheory — only the two `MonadFresh` lifts (`Common/Fresh.lean`) and the `MonadWriter`
  instance below, neither of which existed before this pass needed them.
-/

/-- The concrete monad a `Guarded2Network` correctness proof runs the pass at.
`(compile : (algo.toNetwork : G2NM _).run.run n = (.ok result, n')` is the shape a theorem states
its hypothesis against, mirroring `compileSuccess`-style hypotheses elsewhere in the codebase. -/
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

open Std.Do in
/-- Smoke test (plan §1 P4): `mvcgen` actually discharges a goal against `G2NM`, before anything
real is built on top of it. -/
example : ⦃⌜True⌝⦄ (do let _ ← MonadFresh.fresh; pure () : G2NM Unit) ⦃⇓_ => ⌜True⌝⦄ := by
  mvcgen

end
