module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Statement

@[expose] public section

/-!
  What a receiving thread's step does to the refinement invariant.

  The `.rx` thread is the one part of the compiled algorithm with no source counterpart at all: it
  owns no label and its step consumes none, so no source process ever schedules it, and the source
  therefore *stutters* while it runs. That is only sound if the step is invisible — and "invisible"
  here is a statement about `procRelatesTo`, not about states being equal, because an rx step does
  change the target's memory and FIFOs.

  What it changes, it changes in exactly the way the invariant already accounts for.
  `procRelatesTo` says the source's queue at the process's channel is the target's queue with the
  process's `inbox` in front of it. An rx step moves one value across that boundary: off the head of
  the target's FIFO, onto the end of `inbox`. The concatenation is the same either way, which is why
  the source needs to take no step to keep up.

  The trace is `1`. Reception is not in `Behavior`'s alphabet
  (`Core/GuardedPlusCal/Semantics/Denotational.lean`), which is what makes stuttering admissible
  rather than an observable the source failed to produce.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Memory PathStep OperatorEnv Model)
open GuardedPlusCal (AlgState ChanKey EvalStep FIFOs LocalState ProcState Trace)

variable {V : Type} [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}

/-- **A receiving thread's step is invisible to the source.** The value it moves comes off the head
of the target's FIFO and goes onto the end of `inbox`, so the source's queue — which the invariant
says is `inbox ++ target's queue` — is unchanged, and the source keeps up by not moving.

Stated as the transformation of one `InboxState`: everything `procRelatesTo` and `algRelatesTo` ask
about the pair `⟨key, contents⟩` still holds of `⟨key, contents ++ [v]⟩` against the stepped target.
No label is mentioned — a `.rx` thread owns none, and its step produces `.none`.

`inbox ∉ Ref.freeVars c` is the same freshness this pass carries everywhere: without it the channel
reference could resolve to a different key under the target's memory than under the source's, and
the two sides' `ChanKey`s would not be the one the invariant names. -/
theorem rxStep_step {c : ComputableGuardedPlusCal.Ref} {inbox : String}
    {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V} {ib : InboxState V} {ε : Trace V}
    {σ' : LocalState V}
    (hfresh : inbox ∉ GuardedPlusCal.Ref.freeVars c)
    (hmem : ∀ x ≠ inbox, M₁.lookup x = M₂.lookup x)
    (hinbox : ∃ sv, M₂.lookup inbox = .some sv ∧ ExprSemantics.isSeq sv ib.contents)
    (hkey : ∃ cpath, List.Forall₂ (EvalStep Ξ Ω M₁) c.args cpath ∧ ib.key = ⟨c.name, cpath⟩)
    (hsplit : F₁.lookup ib.key = (ib.contents ++ ·) <$> F₂.lookup ib.key)
    (step : ⟨⟨M₂, F₂, .none⟩, ε, σ'⟩ ∈ NetworkPlusCal.Thread.rxStep Ξ Ω c inbox) :
    ∃ v M₂' F₂', ε = 1 ∧ σ' = ⟨M₂', F₂', .none⟩ ∧
      (∀ x ≠ inbox, M₁.lookup x = M₂'.lookup x) ∧
      (∃ sv, M₂'.lookup inbox = .some sv ∧ ExprSemantics.isSeq sv (ib.contents ++ [v])) ∧
      (∀ k ≠ ib.key, F₂'.lookup k = F₂.lookup k) ∧
      F₁.lookup ib.key = ((ib.contents ++ [v]) ++ ·) <$> F₂'.lookup ib.key ∧
      F₂'.lookup ib.key ≠ .none ∧
      GuardedPlusCal.FIFOs.size F₂' + 1 = GuardedPlusCal.FIFOs.size F₂ := by
  obtain ⟨M, F, cpath, v, vs, old, new, hpath, hfifo, hold, happ, hrun, hdone, rfl⟩ := step
  injection hrun with hM hrun'
  injection hrun' with hF _
  subst hM; subst hF
  obtain ⟨cpath₁, hpath₁, hibkey⟩ := hkey
  -- the two sides resolve the channel to the same key: the reference cannot mention `inbox`, which
  -- is the only name the memories disagree on
  obtain rfl : cpath₁ = cpath :=
    Ref.EvalArgs.inj hpath₁ ((Ref.EvalArgs.congr_of_fresh hmem hfresh).mpr hpath)
  obtain ⟨sv, hsv, hseq⟩ := hinbox
  obtain rfl : sv = old := Option.some.inj (hsv.symm.trans hold)
  refine ⟨v, _, _, rfl, hdone, ?_, ?_, ?_, ?_, ?_, GuardedPlusCal.FIFOs.size_insert_tail hfifo⟩
  · intro x hx
    rw [Finmap.lookup_insert_of_ne _ hx]
    exact hmem x hx
  · exact ⟨new, Finmap.lookup_insert _, ExprSemantics.isSeq_of_seqAppend hseq happ⟩
  · intro k hk
    exact Finmap.lookup_insert_of_ne _ (hibkey ▸ hk)
  · rw [hibkey] at hsplit ⊢
    simp [Finmap.lookup_insert, hsplit, hfifo]
  · rw [hibkey, Finmap.lookup_insert]
    exact Option.some_ne_none _

/-- **The same step, at the process level.** `rxStep_step` with `procRelatesTo`'s clauses assembled
around it, which is the form the algorithm level meets: a receiving thread's step is one whole
`Algebra.step` of the target, and the source answers it with *no* step at all.

The label set survives untouched: a `.rx` thread owns no label and its step consumes none, so
`procRelatesTo`'s `L₂ = L₁` needs nothing done to it. That is what makes the extra thread invisible
to the label bookkeeping as well as to the memory.

The FIFO clauses are returned rather than folded in: they belong to `algRelatesTo`, which quantifies
over all instances' keys at once, so only their per-instance content can be established here. -/
theorem procRelatesTo.rx_step {c : ComputableGuardedPlusCal.Ref} {inbox : String}
    {ib : InboxState V} {M₁ M₂ M₂' : Memory V} {F₁ F₂ F₂' : FIFOs V}
    {L₁ L₂ : Set String} {ε : Trace V}
    (hfresh : inbox ∉ GuardedPlusCal.Ref.freeVars c)
    (h : procRelatesTo Ξ Ω (.some (c, inbox)) (.some ib) ⟨M₁, L₁⟩ ⟨M₂, L₂⟩)
    (hsplit : F₁.lookup ib.key = (ib.contents ++ ·) <$> F₂.lookup ib.key)
    (step : (⟨⟨M₂, F₂, .none⟩, ε, ⟨M₂', F₂', .none⟩⟩ :
      LocalState V × Trace V × LocalState V) ∈
        NetworkPlusCal.Thread.rxStep Ξ Ω c inbox) :
    ∃ v, ε = 1 ∧
      procRelatesTo Ξ Ω (.some (c, inbox)) (.some ⟨ib.key, ib.contents ++ [v]⟩)
        ⟨M₁, L₁⟩ ⟨M₂', L₂⟩ ∧
      (∀ k ≠ ib.key, F₂'.lookup k = F₂.lookup k) ∧
      F₁.lookup ib.key = ((ib.contents ++ [v]) ++ ·) <$> F₂'.lookup ib.key ∧
      F₂'.lookup ib.key ≠ .none ∧
      GuardedPlusCal.FIFOs.size F₂' + 1 = GuardedPlusCal.FIFOs.size F₂ := by
  obtain ⟨hlabels, hmem, hinbox, hkey⟩ := h
  obtain ⟨v, M₂'', F₂'', rfl, hdone, hmem', hinbox', hoff, hsplit', hkeep, hsize⟩ :=
    rxStep_step hfresh hmem hinbox hkey hsplit step
  injection hdone with hM hrest
  injection hrest with hF _
  subst hM; subst hF
  exact ⟨v, rfl, ⟨hlabels, hmem', hinbox', hkey⟩, hoff, hsplit', hkeep, hsize⟩

/-- **And at the algorithm level: the source does not move at all.** One instance takes a receiving
thread's step; every other instance and every other FIFO key is untouched, so the whole
`algRelatesTo` witness survives with one instance's `InboxState` extended by the value that moved.

This is the rx half of the per-step obligation the algorithm-level refinement discharges. It is
answered with *zero* source steps — `Relation.star.refl` — which is why the source side of that
refinement has to be `Relation.star Aₛ.step` rather than `Aₛ.step`: `GuardedPlusCal.Algebra.reducing`
is defined as that star, so this is the goal's own shape rather than a weakening of it. -/
theorem algRelatesTo.rx_step {ι : Type} [DecidableEq ι] {mb : ι → Mailbox}
    {Ps Qs Qs' : GuardedPlusCal.Instances ι V} {F₁ F₂ F₂' : FIFOs V}
    {p : ι} {c : ComputableGuardedPlusCal.Ref} {inbox : String}
    {M₁ M₂ M₂' : Memory V} {L₁ L₂ : Set String} {ε : Trace V}
    (hmb : mb p = .some (c, inbox))
    (hfresh : inbox ∉ GuardedPlusCal.Ref.freeVars c)
    (h : (⟨Ps, F₁⟩ : AlgState ι V) ≋[Ξ, Ω, mb] ⟨Qs, F₂⟩)
    (hS : Ps p = .some ⟨M₁, L₁⟩)
    (hin : Qs p = .some ⟨M₂, L₂⟩)
    (hstep : (⟨⟨M₂, F₂, .none⟩, ε, ⟨M₂', F₂', .none⟩⟩ :
      LocalState V × Trace V × LocalState V) ∈
        NetworkPlusCal.Thread.rxStep Ξ Ω c inbox)
    (hQs : Qs' = Qs.update p (.some ⟨M₂', L₂⟩)) :
    ε = 1 ∧ (⟨Ps, F₁⟩ : AlgState ι V) ≋[Ξ, Ω, mb] ⟨Qs', F₂'⟩ ∧
      GuardedPlusCal.FIFOs.size F₂' + 1 = GuardedPlusCal.FIFOs.size F₂ := by
  obtain ⟨ib, pref, hmatch, habsent, hinj, hkey, hoff, hpresent, hfifo⟩ := h
  -- `Ps`/`Qs` are functions, so `hS`/`hin` already pin the one state each holds at `p`
  have hproc : procRelatesTo Ξ Ω (mb p) (ib p) ⟨M₁, L₁⟩ ⟨M₂, L₂⟩ := by
    have hm := hmatch p
    rwa [hS, hin] at hm
  -- the instance receives, so it has an inbox to account for
  obtain ⟨ibp, hibp⟩ : ∃ ibp, ib p = .some ibp := by
    match hib : ib p with
    | .some ibp => exact ⟨ibp, rfl⟩
    | .none =>
      rw [hmb, hib] at hproc
      nomatch hproc.2
  rw [hibp] at hproc
  have hsplitp : F₁.lookup ibp.key = (ibp.contents ++ ·) <$> F₂.lookup ibp.key := by
    rw [hfifo ibp.key, hkey p ibp hibp]
  obtain ⟨v, rfl, hproc', hoff', hsplit', hkeep, hsize⟩ :=
    procRelatesTo.rx_step hfresh (hmb ▸ hproc) hsplitp hstep
  subst hQs
  -- every other instance's clause survives unchanged: derived from `hmatch` directly, so it shares
  -- the same `ib` witness the goal below is stated against
  have hfwd : ∀ q σ, Ps q = .some σ →
      ∃ σ', Qs q = .some σ' ∧ procRelatesTo Ξ Ω (mb q) (ib q) σ σ' := by
    intro q σ hq
    have hm := hmatch q
    rw [hq] at hm
    rcases Option.eq_none_or_eq_some (Qs q) with hq' | ⟨σ', hq'⟩
    · rw [hq'] at hm; exact hm.elim
    · rw [hq'] at hm; exact ⟨σ', hq', hm⟩
  have hbwd : ∀ q σ', Qs q = .some σ' →
      ∃ σ, Ps q = .some σ ∧ procRelatesTo Ξ Ω (mb q) (ib q) σ σ' := by
    intro q σ' hq'
    have hm := hmatch q
    rw [hq'] at hm
    rcases Option.eq_none_or_eq_some (Ps q) with hq | ⟨σ, hq⟩
    · rw [hq] at hm; exact hm.elim
    · rw [hq] at hm; exact ⟨σ, hq, hm⟩
  -- the update changes what `p` accounts for, never *which key* it accounts for, so every clause
  -- phrased in terms of keys transfers from the old witness unchanged
  have key_of : ∀ q x, Function.update ib p (.some ⟨ibp.key, ibp.contents ++ [v]⟩) q = .some x →
      ∃ x₀, ib q = .some x₀ ∧ x₀.key = x.key := by
    intro q x hx
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self] at hx
      exact ⟨ibp, hibp, by rw [← Option.some.inj hx]⟩
    · rw [Function.update_of_ne hqp] at hx
      exact ⟨x, hx, rfl⟩
  refine ⟨rfl, ?_, hsize⟩
  refine algRelatesTo.intro (ib := Function.update ib p (.some ⟨ibp.key, ibp.contents ++ [v]⟩))
    (pref := Function.update pref ibp.key (ibp.contents ++ [v])) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro q σ hq
    dsimp only at hq ⊢
    by_cases hqp : q = p
    · subst hqp
      rw [hS] at hq
      obtain rfl := Option.some.inj hq
      refine ⟨_, GuardedPlusCal.Instances.update_self .., ?_⟩
      rw [Function.update_self, hmb]
      exact hproc'
    · obtain ⟨σ', hσ', hrel⟩ := hfwd q σ hq
      refine ⟨σ', ?_, ?_⟩
      · rwa [GuardedPlusCal.Instances.update_of_ne hqp]
      · rwa [Function.update_of_ne hqp]
  · intro q σ' hq
    dsimp only at hq ⊢
    by_cases hqp : q = p
    · subst hqp
      rw [GuardedPlusCal.Instances.update_self] at hq
      obtain rfl := Option.some.inj hq
      refine ⟨⟨M₁, L₁⟩, hS, ?_⟩
      rw [Function.update_self, hmb]
      exact hproc'
    · rw [GuardedPlusCal.Instances.update_of_ne hqp] at hq
      obtain ⟨σ, hσ, hrel⟩ := hbwd q σ' hq
      exact ⟨σ, hσ, by rwa [Function.update_of_ne hqp]⟩
  · intro q hq
    dsimp only at hq ⊢
    by_cases hqp : q = p
    · subst hqp
      rw [hS] at hq
      exact nomatch hq
    · rw [Function.update_of_ne hqp]
      exact habsent q hq
  · intro q r x y hx hy hkey
    obtain ⟨x₀, hx₀, hxk⟩ := key_of q x hx
    obtain ⟨y₀, hy₀, hyk⟩ := key_of r y hy
    exact hinj q r x₀ y₀ hx₀ hy₀ (hxk.trans (hkey.trans hyk.symm))
  · intro q x hx
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self] at hx
      obtain rfl := Option.some.inj hx
      exact Function.update_self ..
    · rw [Function.update_of_ne hqp] at hx
      have hne : x.key ≠ ibp.key := λ heq ↦ hqp (hinj q p x ibp hx hibp heq)
      rw [Function.update_of_ne hne]
      exact hkey q x hx
  · intro k hk
    have hkp : ibp.key ≠ k := hk p ⟨ibp.key, ibp.contents ++ [v]⟩ (Function.update_self ..)
    rw [Function.update_of_ne (Ne.symm hkp)]
    refine hoff k (λ q x₀ hx₀ ↦ ?_)
    by_cases hqp : q = p
    · subst hqp
      rw [hibp] at hx₀
      exact Option.some.inj hx₀ ▸ hkp
    · apply hk q x₀
      rwa [Function.update_of_ne hqp]
  · -- the relay wrote back at its own key, and left every other one alone
    intro q x hx
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self] at hx
      obtain rfl := Option.some.inj hx
      exact hkeep
    · rw [Function.update_of_ne hqp] at hx
      have hne : x.key ≠ ibp.key := λ heq ↦ hqp (hinj q p x ibp hx hibp heq)
      rw [hoff' x.key hne]
      exact hpresent q x hx
  · intro k
    by_cases hkp : k = ibp.key
    · subst hkp
      rw [Function.update_self]
      exact hsplit'
    · rw [Function.update_of_ne hkp, hoff' k hkp]
      exact hfifo k

end Guarded2Network

end
