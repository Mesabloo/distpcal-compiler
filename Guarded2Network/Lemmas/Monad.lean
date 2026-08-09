module

public import Guarded2Network.Errors
public import Extra.Do

@[expose] public section

/-!
  The monad a `Guarded2Network` correctness proof runs the pass at.

  `Guarded2Network.PlusCal`'s pass runs monad-polymorphically (`{m} [Monad m] [MonadDiagnostic
  Empty G2NError m] [MonadFresh m]`, plus function-scoped `StateT`s), which is right for the *pass*
  but not for *proving things about it* — a proof has to invert "this run returned a result", and
  that is a statement about one concrete stack. Every layer (`ExceptT`, `StateT`, `Id`) already has
  `WP`/`WPMonad` in `Std.Do`, so pinning `m` here needs no new metatheory: only the two `MonadFresh`
  lifts (`Common/Fresh.lean`) and the `MonadWriter` instance below, neither of which existed before
  this pass needed them.

  Its own file rather than `Guarded2Network/Lemmas.lean`, where it started: the proof files import
  it, and `Lemmas.lean` imports them.
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
/-- Adequacy for the stack `processPrecondition` and every other function-scoped `StateT` of the
pass runs at: what `mvcgen` proves about a program is a fact about the value that program actually
returned.

`Std.Do.WP.Basic` ships one of these per *primitive* stack (`Id`, `StateM`, `ReaderM`, `Except`,
`EStateM`) and none for a composite, so a three-layer stack needs its own. Only the `.ok` case is
stated: a compilation that threw is not one a correctness theorem has anything to say about, which
is also why the postcondition may be a `⇓?` — the error branch carries no obligation. -/
theorem G2NM.of_wp_run_eq {σ α : Type} {prog : StateT σ G2NM α} {st st' : σ} {a : α} {n n' : Nat}
    (h : ((prog.run st).run.run n) = (.ok (a, st'), n')) (P : α → σ → Prop)
    (hwp : ⊢ₛ wp⟦prog⟧ (⇓? a st'' => ⌜P a st''⌝) st n) : P a st' := by
  simp only [wp, StateT.run, ExceptT.run, PredTrans.apply_pushArg, PredTrans.apply_pushExcept,
    PredTrans.apply_Pure_pure, SPred.entails_nil, SPred.down_pure_nil, forall_const] at hwp h
  rwa [h] at hwp

/-- Inverting one `do`-block step: a run that succeeded got there through a first half that
succeeded. `mvcgen` reasons forwards and needs no such lemma, but a pass whose result is *given* —
"this compilation produced `Pₜ`" — is read backwards, and the only way through a `bind` is this. -/
theorem G2NM.run_bind_eq_ok {α β : Type} {x : G2NM α} {f : α → G2NM β} {b : β} {n n' : Nat}
    (h : ((x >>= f).run.run n) = (.ok b, n')) :
    ∃ a n₁, x.run.run n = (.ok a, n₁) ∧ (f a).run.run n₁ = (.ok b, n') := by
  change ExceptT.bindCont f (x.run.run n).1 (x.run.run n).2 = (Except.ok b, n') at h
  rcases hxn : x.run.run n with ⟨res, n₁⟩
  rw [hxn] at h
  cases res with
  | ok a => exact ⟨a, n₁, rfl, h⟩
  | error e =>
    simp only [ExceptT.bindCont] at h
    injection h with he _
    contradiction

end
