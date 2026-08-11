module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Statement

@[expose] public section

/-!
  What a receiving thread's step does to the refinement invariant.

  The `.rx` thread is the one part of the compiled algorithm with no source counterpart at all: its
  label is fresh, so no source process ever schedules it, and the source therefore *stutters* while
  it runs. That is only sound if the step is invisible — and "invisible" here is a statement about
  `procRelatesTo`, not about states being equal, because an rx step does change the target's memory
  and FIFOs.

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

open ComputableTLAPlus (ExprSemantics Memory PathStep)
open GuardedPlusCal (ChanKey EvalStep FIFOs LocalState Trace)

variable {V : Type} [ExprSemantics V]

/-- **A receiving thread's step is invisible to the source.** The value it moves comes off the head
of the target's FIFO and goes onto the end of `inbox`, so the source's queue — which the invariant
says is `inbox ++ target's queue` — is unchanged, and the source keeps up by not moving.

Stated as the transformation of one `InboxState`: everything `procRelatesTo` and `algRelatesTo` ask
about the pair `⟨key, contents⟩` still holds of `⟨key, contents ++ [v]⟩` against the stepped target.
The label is not mentioned — the rx block's terminal `goto` targets its own label, so the target's
label set is unchanged, and that is the process level's bookkeeping rather than this lemma's.

`inbox ∉ Ref.freeVars c` is the same freshness this pass carries everywhere: without it the channel
reference could resolve to a different key under the target's memory than under the source's, and
the two sides' `ChanKey`s would not be the one the invariant names. -/
theorem rxBranch_step {c : ComputableGuardedPlusCal.Ref} {inbox label : String}
    {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V} {ib : InboxState V} {ε : Trace V}
    {σ' : LocalState V true}
    (hfresh : inbox ∉ GuardedPlusCal.Ref.freeVars c)
    (hmem : ∀ x ≠ inbox, M₁.lookup x = M₂.lookup x)
    (hinbox : ∃ sv, M₂.lookup inbox = .some sv ∧ ExprSemantics.isSeq sv ib.contents)
    (hkey : ∃ cpath, List.Forall₂ (EvalStep M₁) c.args cpath ∧ ib.key = ⟨c.name, cpath⟩)
    (hsplit : F₁.lookup ib.key = (ib.contents ++ ·) <$> F₂.lookup ib.key)
    (step : ⟨.running M₂ F₂, ε, σ'⟩ ∈ NetworkPlusCal.Thread.rxBranch c label inbox) :
    ∃ v M₂' F₂', ε = 1 ∧ σ' = .done M₂' F₂' label ∧
      (∀ x ≠ inbox, M₁.lookup x = M₂'.lookup x) ∧
      (∃ sv, M₂'.lookup inbox = .some sv ∧ ExprSemantics.isSeq sv (ib.contents ++ [v])) ∧
      (∀ k ≠ ib.key, F₂'.lookup k = F₂.lookup k) ∧
      F₁.lookup ib.key = ((ib.contents ++ [v]) ++ ·) <$> F₂'.lookup ib.key := by
  obtain ⟨M, F, cpath, v, vs, old, new, hpath, hfifo, hold, happ, hrun, hdone, rfl⟩ := step
  injection hrun with hM hF
  subst hM; subst hF
  obtain ⟨cpath₁, hpath₁, hibkey⟩ := hkey
  -- the two sides resolve the channel to the same key: the reference cannot mention `inbox`, which
  -- is the only name the memories disagree on
  obtain rfl : cpath₁ = cpath :=
    Ref.EvalArgs.inj hpath₁ ((Ref.EvalArgs.congr_of_fresh hmem hfresh).mpr hpath)
  obtain ⟨sv, hsv, hseq⟩ := hinbox
  obtain rfl : sv = old := Option.some.inj (hsv.symm.trans hold)
  refine ⟨v, _, _, rfl, hdone, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finmap.lookup_insert_of_ne _ hx]
    exact hmem x hx
  · exact ⟨new, Finmap.lookup_insert _, ExprSemantics.isSeq_of_seqAppend hseq happ⟩
  · intro k hk
    exact Finmap.lookup_insert_of_ne _ (hibkey ▸ hk)
  · rw [hibkey] at hsplit ⊢
    simp [Finmap.lookup_insert, hsplit, hfifo]

/-- **The same step, at the process level.** `rxBranch_step` with `procRelatesTo`'s clauses assembled
around it, which is the form the algorithm level meets: a receiving thread's step is one whole
`Algebra.step` of the target, and the source answers it with *no* step at all.

The label set survives untouched. A process step replaces the label it ran with the one the block's
terminal `goto` reached, and the rx block's `goto` names its own label — so `insert label (L \
{label})` is `L` again, and `procRelatesTo`'s `L₂ = L₁ ∪ rx` needs nothing done to it. That is what
makes the extra thread invisible to the label bookkeeping as well as to the memory.

The FIFO clauses are returned rather than folded in: they belong to `algRelatesTo`, which quantifies
over all instances' keys at once, so only their per-instance content can be established here. -/
theorem procRelatesTo.rx_step {c : ComputableGuardedPlusCal.Ref} {inbox label : String}
    {rx : Set String} {ib : InboxState V} {M₁ M₂ M₂' : Memory V} {F₁ F₂ F₂' : FIFOs V}
    {L₁ L₂ : Set String} {ε : Trace V}
    (hfresh : inbox ∉ GuardedPlusCal.Ref.freeVars c)
    (h : procRelatesTo (.some (c, inbox)) rx (.some ib) ⟨M₁, L₁⟩ ⟨M₂, L₂⟩)
    (hsplit : F₁.lookup ib.key = (ib.contents ++ ·) <$> F₂.lookup ib.key)
    (hlabel : label ∈ L₂)
    (step : (⟨.running M₂ F₂, ε, .done M₂' F₂' label⟩ :
      LocalState V false × Trace V × LocalState V true) ∈
        NetworkPlusCal.Thread.rxBranch c label inbox) :
    ∃ v, ε = 1 ∧
      procRelatesTo (.some (c, inbox)) rx (.some ⟨ib.key, ib.contents ++ [v]⟩)
        ⟨M₁, L₁⟩ ⟨M₂', insert label (L₂ \ {label})⟩ ∧
      (∀ k ≠ ib.key, F₂'.lookup k = F₂.lookup k) ∧
      F₁.lookup ib.key = ((ib.contents ++ [v]) ++ ·) <$> F₂'.lookup ib.key := by
  obtain ⟨hlabels, hdisj, hmem, hinbox, hkey⟩ := h
  obtain ⟨v, M₂'', F₂'', rfl, hdone, hmem', hinbox', hoff, hsplit'⟩ :=
    rxBranch_step hfresh hmem hinbox hkey hsplit step
  injection hdone with hM hF _
  subst hM; subst hF
  rw [Set.insert_sdiff_self_of_mem hlabel]
  exact ⟨v, rfl, ⟨hlabels, hdisj, hmem', hinbox', hkey⟩, hoff, hsplit'⟩

end Guarded2Network

end
