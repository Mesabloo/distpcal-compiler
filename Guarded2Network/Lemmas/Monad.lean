module

public import Guarded2Network.Errors
public import Common.Fresh
public import Extra.Do

@[expose] public section

/-!
  The monad a `Guarded2Network` correctness proof runs the pass at.

  `Guarded2Network.PlusCal`'s pass runs monad-polymorphically (`{m} [Monad m] [MonadDiagnostic
  Empty G2NError m] [MonadFresh m]`, plus function-scoped `StateT`s), which is right for the *pass*
  but not for *proving things about it* — `wp⟦·⟧` and the `[spec]` lemmas that drive `mvcgen` are
  stated per stack, so a proof has to pin `m` to one. Every layer (`ExceptT`, `StateT`, `Id`)
  already has `WP`/`WPMonad` in `Std.Do`, so pinning it here needs no new metatheory: only the two
  `MonadFresh` lifts and the `MonadWriter` instance below.

  Its own file rather than `Guarded2Network.Lemmas`: the proof files import it, and
  `Guarded2Network.Lemmas` imports them.
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

/-- A name `freshName` produced with this prefix.

This is the whole freshness argument, made syntactically: `$` cannot occur in a TLA⁺ identifier (the
lexer's `identifierOrKeyword` accepts only letters, digits and `_`), so a name of this shape is one
no source program could have written. Nothing here has to track scopes, and a proof that a generated
name avoids a source one reduces to a statement about the *shape* of the two.

The counter is existential rather than reported, because a postcondition cannot mention the state the
program started in — and nothing downstream needs the number, only that there is one.

This is also the shape the *front end's* half of the argument takes. "No source label collides with a
generated one" is `∀ l ∈ …, ¬ Generated "rx" l`, which the lexer discharges and which makes the
collision proofs here immediate rather than a computation on characters. -/
def Generated (namePrefix s : String) : Prop := ∃ n : Nat, s = s!"{namePrefix}${n}"

open Std.Do in
/-- **A family of triples for one program is one triple for the family.** The postcondition may be
quantified over an arbitrary index after the fact, which is what lets a fact owed "at every `x`" be
assembled from the specs proved at each — `Algorithm.toNetwork_refines` wants the pass's output
related at every prefix function, and `Algorithm.toNetwork_spec` supplies one prefix function per
instantiation.

Not derivable from `Std.Do`: a `PredTrans` carries *binary* conjunctivity only
(`PredTrans.conjunctive`, which `Triple.and` spends), and there is no infinitary version to appeal
to. It is true here because `G2NM` is deterministic — `wp⟦x⟧ Q n` is a match on what `x` returns at
`n`, the same match whatever `Q` is — so the proof is the one place in this development that unfolds
`wp` rather than going through the `[spec]` API. Confined to this lemma for that reason.

The precondition is `⌜True⌝` rather than general because that is what every top-level spec has, and a
general one would have to be assumed at every `i` separately. `himp` rides along because the caller
always wants to *spend* the family rather than report it, and weakening a postcondition afterwards
would need a `PostCond.entails` built by hand. -/
theorem triple_forall {α ι : Type} {x : G2NM α} {Q : ι → α → Prop} {R : α → Prop}
    (h : ∀ i, ⦃⌜True⌝⦄ x ⦃⇓? a => ⌜Q i a⌝⦄) (himp : ∀ a, (∀ i, Q i a) → R a) :
    ⦃⌜True⌝⦄ x ⦃⇓? a => ⌜R a⌝⦄ := by
  intro n _
  replace h := λ i ↦ h i n trivial
  simp only [Std.Do.WP.wp, PredTrans.apply_pushExcept, PredTrans.apply_pushArg,
    PredTrans.apply_Pure_pure, StateT.run, ExceptT.run] at h ⊢
  cases hx : (x n).run.1 <;> simp_all

open Std.Do in
/-- **`freshName` produces a `Generated` name.** Stated as a triple rather than an equation for the
same reason every other fact about this pass is: the counter is state, and a run-equation would force
reading the pass backwards from its output. -/
theorem freshName_spec (namePrefix : String) :
    ⦃⌜True⌝⦄ freshName (m := G2NM) namePrefix ⦃⇓? s => ⌜Generated namePrefix s⌝⦄ := by
  mvcgen [freshName, MonadFresh.fresh]
  exact ⟨_, rfl⟩

end Guarded2Network

end
