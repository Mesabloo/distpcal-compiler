module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Process
public import Guarded2Network.Lemmas.Rx
public import Core.NetworkPlusCal.Semantics.Process

@[expose] public section

/-!
  The whole algorithm, one step at a time.

  Below this file the two per-step obligations are already proved, one per kind of target thread:
  `algRelatesTo.block_step` for a compiled code thread's block, `algRelatesTo.rx_step` for a
  receiving thread's relay. What is left is the *dispatch* — deciding which of the two a target step
  is — and that is a question about the compiled algebra, not about any state.

  So this file states what a compiled algebra owes (`AlgebraRefines`), one clause per owned label,
  and then discharges the framework's `Terminating` obligation against it. The clauses are what the
  two per-step lemmas already ask for and nothing more; they are `Guarded2Network`'s side of D8's
  contract, to be established once `Thread.toNetwork` exists.

  **The source side is `Relation.star Aₛ.step`, not `Aₛ.step`.** A receiving thread's step is
  answered with *no* source step at all, so no single-step form can be stated — see
  `StrongRefinement.Terminating.starStutter`, which is the shape that admits it and which
  `terminating_reducing` below spends.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Memory)
open GuardedPlusCal (Algebra AlgState ChanKey CodeTable FIFOs Instances LocalState ProcState Trace)

variable {V : Type} [ExprSemantics V] [SeqBuiltins V] {ι : Type}

/-! # What a compiled algebra owes -/

/-- A label a compiled **code** thread owns, against the branches its block has on each side. Their
block denotes the union of those branches, and they are pairwise `BranchRefines` — at every `pref`,
since which prefix function the algorithm level hands down is not known here.

The two `⊆` clauses run in opposite directions on purpose. The target's block must be *contained* in
its branches, because a target step has to be attributed to one of them; the source's branches must
be contained in *its* block, because a source step is being built. Neither direction needs the
converse.

`not_rx` and `exits` are the label-agreement side (`algRelatesTo.block_step`): a code thread is
scheduled at a source label and leaves at another, never at a receiving thread's. -/
structure CodeLabelRefines (Aₛ Aₜ : Algebra ι V) (mb : ι → Mailbox) (rx : ι → Set String)
    (p : ι) (l : String) (brs : List ComputableGuardedPlusCal.AtomicBranch)
    (brs' : List ComputableNetworkPlusCal.AtomicBranch) : Prop where
  /-- The label is not a receiving thread's. -/
  not_rx : l ∉ rx p
  /-- And the source process owns it too. -/
  owned : l ∈ Aₛ.owned p
  /-- Nor is any label the block can leave at. -/
  exits : ∀ M F τ M' F' l', (⟨.running M F, τ, .done M' F' l'⟩ :
    LocalState V false × Trace V × LocalState V true) ∈ (Aₜ.table p).reducing l → l' ∉ rx p
  /-- The branches refine pairwise, at every prefix function. -/
  refines : ∀ pref : ChanKey V → List V,
    List.Forall₂ (BranchRefines (V := V) (mb p) pref) brs brs'
  /-- Every source branch avoids the generated `inbox`. -/
  fresh : ∀ Br ∈ brs, ∀ c inbox, mb p = .some (c, inbox) → BranchesFresh c inbox Br
  /-- A target step at this label is a step of one compiled branch. -/
  target_le : ∀ x ∈ (Aₜ.table p).reducing l,
    ∃ Br' ∈ brs', x ∈ NetworkPlusCal.AtomicBranch.reducing Br'
  /-- A step of any source branch is a step at this label. -/
  source_reducing : ∀ Br ∈ brs, GuardedPlusCal.AtomicBranch.reducing Br ⊆ (Aₛ.table p).reducing l
  /-- And likewise where it goes wrong. -/
  source_aborting : ∀ Br ∈ brs, GuardedPlusCal.AtomicBranch.aborting Br ⊆ (Aₛ.table p).aborting l

/-- A label a **receiving** thread owns. It has no source counterpart at all — that is the point of
the pass — so all this says is that the block behind it is the relay, on the instance's own channel
and into the `inbox` the pass generated for it. -/
structure RxLabelRefines (Aₜ : Algebra ι V) (mb : ι → Mailbox) (rx : ι → Set String)
    (p : ι) (l : String) (chan : ComputableGuardedPlusCal.Ref) (inbox : String) : Prop where
  /-- The label belongs to a receiving thread. -/
  mem_rx : l ∈ rx p
  /-- The channel and `inbox` are the ones the invariant is stated against. -/
  mailbox : mb p = .some (chan, inbox)
  /-- The generated name is not one the channel is indexed by. -/
  chan_fresh : inbox ∉ GuardedPlusCal.Ref.freeVars chan
  /-- And the block behind the label is the relay. -/
  target_le : (Aₜ.table p).reducing l ⊆ NetworkPlusCal.Thread.rxBranch chan l inbox

/-- **What a compiled algebra owes.** One clause per owned target label — code or receiving — plus
the two facts that hold of every instance at once.

This is the interface `algRelatesTo.terminating` consumes and `Thread.toNetwork` (D8) will produce.
Written top-down, from what the two per-step lemmas already need, so that establishing it is a
question about the pass rather than about the proof. -/
structure AlgebraRefines (Aₛ Aₜ : Algebra ι V) (mb : ι → Mailbox) (rx : ι → Set String) : Prop where
  /-- Compilation does not change an instance's identity. -/
  self_eq : ∀ p, Aₛ.self p = Aₜ.self p
  /-- The generated `inbox` is not `self` — a `freshName` fact, and what lets the source memory be
  read at `selfName` through the invariant's memory agreement. -/
  inbox_ne_self : ∀ p c inbox, mb p = .some (c, inbox) → inbox ≠ GuardedPlusCal.selfName
  /-- And every label the target owns is one kind or the other. -/
  labels : ∀ p, ∀ l ∈ Aₜ.owned p,
    (∃ brs brs', CodeLabelRefines Aₛ Aₜ mb rx p l brs brs') ∨
      ∃ chan inbox, RxLabelRefines Aₜ mb rx p l chan inbox

/-! # The per-step obligation, and the whole reducing semantics -/

omit [SeqBuiltins V] in
/-- **One target step, answered.** The algorithm-level `Terminating`, with the source allowed to
take a whole run — one step when a code thread moved, none when a receiving thread did.

The proof is dispatch and plumbing: read the target step apart into an instance and a label, ask
`AlgebraRefines` which kind of label it is, and hand the pieces to whichever per-step lemma applies.
Everything difficult already happened in those two.

Reassembling the *source's* step is the only thing here that is not dispatch. `Algebra.step` wants a
`CodeTable.procReducing`, which wants the scheduled label to be one the source process owns and has
scheduled, and the memory to bind `selfName`. The first comes from `CodeLabelRefines` together with
`procRelatesTo`'s `L₂ = L₁ ∪ rx p`; the second from memory agreement away from the generated
`inbox`, which is not `self`. -/
theorem algRelatesTo.terminating [DecidableEq ι] {Aₛ Aₜ : Algebra ι V} {mb : ι → Mailbox}
    {rx : ι → Set String} (href : AlgebraRefines Aₛ Aₜ mb rx) :
    StrongRefinement.Terminating (algRelatesTo (V := V) mb rx) (algRelatesTo (V := V) mb rx)
      (instTrace (V := V)).Rτ (Relation.star Aₛ.step) Aₛ.aborting Aₜ.step := by
  rintro ⟨Qs, F₂⟩ ⟨Qs', F₂'⟩ ε ⟨Ps, F₁⟩ hrel hstep
  obtain ⟨p, ⟨M₂, L₂⟩, hin, ⟨M₂', L₂'⟩, hproc, hQs⟩ := hstep
  obtain ⟨l, hl, l', hred, hself, rfl⟩ := hproc
  obtain ⟨ib, hbwd⟩ := hrel.backward
  obtain ⟨⟨M₁, L₁⟩, hS, hproc⟩ := hbwd p ⟨M₂, L₂⟩ hin
  -- a process only steps in a memory binding its own identity; the source's does because it agrees
  -- with the target's away from the generated `inbox`, which is not `self`
  have hself' : Finmap.lookup GuardedPlusCal.selfName M₁ = .some (Aₛ.self p) := by
    rw [href.self_eq p,
      hproc.mem_agree' _ (λ c inbox hmb ↦ (href.inbox_ne_self p c inbox hmb).symm)]
    exact hself
  rcases href.labels p l hl.2 with ⟨brs, brs', hcode⟩ | ⟨c, inbox, hrx⟩
  · -- a code thread moved, and the source block at the same label answers
    have hlabel : l ∈ L₁ := by
      rcases (hproc.1 ▸ hl.1 : l ∈ L₁ ∪ rx p) with hmem | hmem
      · exact hmem
      · exact (hcode.not_rx hmem).elim
    obtain ⟨Br', hBr', hstep'⟩ := hcode.target_le _ hred
    rcases algRelatesTo.block_step hcode.refines hcode.fresh hrel hS hin hlabel
        (hcode.exits _ _ _ _ _ _ hred) hBr' hstep' hQs with
      ⟨M₁', F₁', ε', hrel', hτ, Br, hBr, hsstep⟩ | ⟨ε', hpfx, Br, hBr, habort⟩
    · refine .inl ⟨_, ε', hrel', hτ, Relation.star.single ?_⟩
      exact ⟨p, ⟨M₁, L₁⟩, hS, ⟨M₁', insert l' (L₁ \ {l})⟩,
        ⟨l, ⟨hlabel, hcode.owned⟩, l', hcode.source_reducing Br hBr hsstep, hself', rfl⟩, rfl⟩
    · refine .inr ⟨ε', hpfx, Relation.star.le_lcomp₁ ?_⟩
      exact ⟨p, ⟨M₁, L₁⟩, hS, l, ⟨hlabel, hcode.owned⟩,
        hcode.source_aborting Br hBr habort, hself'⟩
  · -- a receiving thread moved, and the source does not move at all
    obtain rfl := NetworkPlusCal.Thread.rxBranch_label (hrx.target_le hred)
    obtain ⟨rfl, hrel'⟩ := algRelatesTo.rx_step hrx.mailbox hrx.chan_fresh hrel hS hin hl.1
      (hrx.target_le hred) hQs
    refine .inl ⟨_, 1, hrel', ?_, Relation.star.refl _⟩
    trace_rel

omit [SeqBuiltins V] in
/-- **And the whole reducing semantics.** `Algebra.reducing` is `step*` by definition and
`Algebra.aborting` is `step* ∘ᵣ₁ immediateAbort`, so this is `Terminating.starStutter` at those and
nothing else — including its absorption side condition, which is `Relation.star.star_lcomp₁_absorb`
at exactly this shape.

The `Aborting` and `Diverging` components of `StrongRefinement` are still owed; only then does
`StrongRefinement.sequentialOmega`'s conclusion become available, and it will want the same
stuttering treatment on both. -/
theorem algRelatesTo.terminating_reducing [DecidableEq ι] {Aₛ Aₜ : Algebra ι V} {mb : ι → Mailbox}
    {rx : ι → Set String} (href : AlgebraRefines Aₛ Aₜ mb rx) :
    StrongRefinement.Terminating (algRelatesTo (V := V) mb rx) (algRelatesTo (V := V) mb rx)
      (instTrace (V := V)).Rτ Aₛ.reducing Aₛ.aborting Aₜ.reducing :=
  StrongRefinement.Terminating.starStutter Relation.star.star_lcomp₁_absorb
    (algRelatesTo.terminating href)

end Guarded2Network

end
