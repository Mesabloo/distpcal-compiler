module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Process
public import Guarded2Network.Lemmas.Rx
public import Core.NetworkPlusCal.Semantics.Process
import all Guarded2Network.PlusCal

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
    BranchesRefine (V := V) (mb p) pref brs brs'
  /-- Every source branch avoids the generated `inbox`. -/
  fresh : ∀ Br ∈ brs, ∀ c inbox, mb p = .some (c, inbox) →
    BranchesFresh (.some (c, inbox)) c inbox Br
  /-- A target step at this label is a step of one compiled branch. -/
  target_le : ∀ x ∈ (Aₜ.table p).reducing l,
    ∃ Br' ∈ brs', x ∈ NetworkPlusCal.AtomicBranch.reducing Br'
  /-- And a target abort at this label is one compiled branch going wrong. -/
  target_abort_le : ∀ x ∈ (Aₜ.table p).aborting l,
    ∃ Br' ∈ brs', x ∈ NetworkPlusCal.AtomicBranch.aborting Br'
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
  /-- Including where it goes wrong — which the invariant then rules out entirely, the source having
  no receiving thread to answer with. -/
  target_abort_le : (Aₜ.table p).aborting l ⊆ NetworkPlusCal.Thread.rxBranchAborting chan inbox

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
/-- **One target step, answered — and never answered by nothing forever.** The per-step obligation
in the three-way form a stuttering simulation needs: the source takes *one* step, or it takes none
and the target's queued-message count strictly drops, or it aborts.

The middle disjunct is what a divergence argument needs and `Terminating` cannot express. A
receiving thread's step is answered with no source step at all, so an infinite target run could in
principle be answered by a source that never moves — except that a relay moves a message *out* of a
channel, and `FIFOs.size` counts exactly those. Only a `send` puts one back, and a `send` is a code
thread's step, which does move the source. So the target cannot relay forever without the source
keeping pace.

The proof is dispatch and plumbing: read the target step apart into an instance and a label, ask
`AlgebraRefines` which kind of label it is, and hand the pieces to whichever per-step lemma applies.
Everything difficult already happened in those two.

Reassembling the *source's* step is the only thing here that is not dispatch. `Algebra.step` wants a
`CodeTable.procReducing`, which wants the scheduled label to be one the source process owns and has
scheduled, and the memory to bind `selfName`. The first comes from `CodeLabelRefines` together with
`procRelatesTo`'s `L₂ = L₁ ∪ rx p`; the second from memory agreement away from the generated
`inbox`, which is not `self`. -/
theorem algRelatesTo.step_or_stutter [DecidableEq ι] {Aₛ Aₜ : Algebra ι V} {mb : ι → Mailbox}
    {rx : ι → Set String} (href : AlgebraRefines Aₛ Aₜ mb rx)
    {Sₜ Sₜ' Sₛ : AlgState ι V} {ε : Trace V} (hrel : Sₛ ≋[mb, rx] Sₜ)
    (hstep : (⟨Sₜ, ε, Sₜ'⟩ : AlgState ι V × Trace V × AlgState ι V) ∈ Aₜ.step) :
    (∃ Sₛ' ε', Sₛ' ≋[mb, rx] Sₜ' ∧ (instTrace (V := V)).Rτ ε' ε ∧
        (⟨Sₛ, ε', Sₛ'⟩ : AlgState ι V × Trace V × AlgState ι V) ∈ Aₛ.step) ∨
      (Sₛ ≋[mb, rx] Sₜ' ∧ ε = 1 ∧
        GuardedPlusCal.FIFOs.size Sₜ'.2 < GuardedPlusCal.FIFOs.size Sₜ.2) ∨
      (∃ ε', ε' ≼[(instTrace (V := V)).Rτ] ε ∧ (⟨Sₛ, ε'⟩ : AlgState ι V × Trace V) ∈
        Aₛ.aborting) := by
  obtain ⟨Qs, F₂⟩ := Sₜ
  obtain ⟨Qs', F₂'⟩ := Sₜ'
  obtain ⟨Ps, F₁⟩ := Sₛ
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
    · refine .inl ⟨_, ε', hrel', hτ, ?_⟩
      exact ⟨p, ⟨M₁, L₁⟩, hS, ⟨M₁', insert l' (L₁ \ {l})⟩,
        ⟨l, ⟨hlabel, hcode.owned⟩, l', hcode.source_reducing Br hBr hsstep, hself', rfl⟩, rfl⟩
    · refine .inr (.inr ⟨ε', hpfx, Relation.star.le_lcomp₁ ?_⟩)
      exact ⟨p, ⟨M₁, L₁⟩, hS, l, ⟨hlabel, hcode.owned⟩,
        hcode.source_aborting Br hBr habort, hself'⟩
  · -- a receiving thread moved, and the source does not move at all
    obtain rfl := NetworkPlusCal.Thread.rxBranch_label (hrx.target_le hred)
    obtain ⟨rfl, hrel', hsize⟩ := algRelatesTo.rx_step hrx.mailbox hrx.chan_fresh hrel hS hin hl.1
      (hrx.target_le hred) hQs
    refine .inr (.inl ⟨hrel', rfl, ?_⟩)
    show GuardedPlusCal.FIFOs.size F₂' < GuardedPlusCal.FIFOs.size F₂
    omega

omit [SeqBuiltins V] in
/-- **The algorithm-level `Terminating`**, read off `step_or_stutter`: a source step is a one-step
run, a stutter is the empty one, and the abort disjunct passes through unchanged. The measure is
dropped here — `Terminating` has nowhere to put it, which is exactly why the divergence half needs
`step_or_stutter` directly. -/
theorem algRelatesTo.terminating [DecidableEq ι] {Aₛ Aₜ : Algebra ι V} {mb : ι → Mailbox}
    {rx : ι → Set String} (href : AlgebraRefines Aₛ Aₜ mb rx) :
    StrongRefinement.Terminating (algRelatesTo (V := V) mb rx) (algRelatesTo (V := V) mb rx)
      (instTrace (V := V)).Rτ (Relation.star Aₛ.step) Aₛ.aborting Aₜ.step := by
  intro Sₜ Sₜ' ε Sₛ hrel hstep
  rcases algRelatesTo.step_or_stutter href hrel hstep with
    ⟨Sₛ', ε', hrel', hτ, hsstep⟩ | ⟨hrel', rfl, _⟩ | habort
  · exact .inl ⟨Sₛ', ε', hrel', hτ, Relation.star.single hsstep⟩
  · refine .inl ⟨Sₛ, 1, hrel', ?_, Relation.star.refl _⟩
    trace_rel
  · exact .inr habort

omit [SeqBuiltins V] in
/-- **A receiving thread cannot go wrong at a related state**, and it has to be so: the source has no
receiving thread, so a relay abort with no source counterpart would make the aborting refinement
false outright.

All four of `rxBranchAborting`'s cases are excluded, and by four different clauses. The channel's
path failing to resolve contradicts `procRelatesTo`'s own resolved `cpath`; the channel resolving to
no FIFO contradicts `algRelatesTo`'s presence clause — the one that exists for this; `inbox` unbound
contradicts the inbox clause; and appending to `inbox` failing contradicts `seqAppend_isSeq`, since
that clause says `inbox` really holds a sequence. -/
theorem rxBranch_not_aborting {c : ComputableGuardedPlusCal.Ref} {inbox : String}
    {rx : Set String} {ib : InboxState V} {M₁ M₂ : Memory V} {F₂ : FIFOs V}
    {L₁ L₂ : Set String} {ε : Trace V}
    (hfresh : inbox ∉ GuardedPlusCal.Ref.freeVars c)
    (h : procRelatesTo (.some (c, inbox)) rx (.some ib) ⟨M₁, L₁⟩ ⟨M₂, L₂⟩)
    (hpresent : F₂.lookup ib.key ≠ .none) :
    (⟨.running M₂ F₂, ε⟩ : LocalState V false × Trace V) ∉
      NetworkPlusCal.Thread.rxBranchAborting c inbox := by
  obtain ⟨_, _, hmem, hinbox, cpath, hpath, hibkey⟩ := h
  have hpath₂ : Ref.EvalArgs M₂ c cpath := (Ref.EvalArgs.congr_of_fresh hmem hfresh).mp hpath
  obtain ⟨sv, hsv, hseq⟩ := hinbox
  rintro (((⟨M, F, hpa, hrun, _⟩ | ⟨M, F, cpath', hpath', hlk, hrun, _⟩) |
    ⟨M, F, hnone, hrun, _⟩) | ⟨M, F, cpath', v, _, old, hpath', _, hold, happ, hrun, _⟩) <;>
    injection hrun with hM hF <;> subst hM <;> subst hF
  · exact Ref.EvalArgs.not_pathAborts hpath₂ hpa
  · obtain rfl := Ref.EvalArgs.inj hpath' hpath₂
    exact hpresent (hibkey ▸ hlk)
  · rw [hsv] at hnone
    contradiction
  · rw [hsv] at hold
    obtain rfl := Option.some.inj hold
    obtain ⟨_, happ', _⟩ := ExprSemantics.seqAppend_isSeq (v := v) hseq
    rw [happ] at happ'
    contradiction

omit [SeqBuiltins V] in
/-- **Where the target goes wrong, so does the source.** The aborting counterpart of
`algRelatesTo.terminating`, and the same dispatch — except that only one branch of it produces
anything. A code thread's abort is answered by the source block's, through `blockRefines_abort`; a
receiving thread's abort cannot happen at all (`rxBranch_not_aborting`).

Simpler than the terminating case throughout, because an abort has no post-state: no `algRelatesTo`
witness is rebuilt, so none of the key bookkeeping appears. -/
theorem algRelatesTo.immediateAbort [DecidableEq ι] {Aₛ Aₜ : Algebra ι V} {mb : ι → Mailbox}
    {rx : ι → Set String} (href : AlgebraRefines Aₛ Aₜ mb rx) :
    StrongRefinement.Aborting (algRelatesTo (V := V) mb rx) (instTrace (V := V)).Rτ
      Aₛ.immediateAbort Aₜ.immediateAbort := by
  rintro ⟨Qs, F₂⟩ ε ⟨Ps, F₁⟩ hrel ⟨p, ⟨M₂, L₂⟩, hin, l, hl, habort, hself⟩
  obtain ⟨ib, pref, _, _, _, hbwd, _, _, hkey, _, hpresent, hfifo⟩ := hrel
  obtain ⟨⟨M₁, L₁⟩, hS, hproc⟩ := hbwd p ⟨M₂, L₂⟩ hin
  have hself' : Finmap.lookup GuardedPlusCal.selfName M₁ = .some (Aₛ.self p) := by
    rw [href.self_eq p,
      hproc.mem_agree' _ (λ c inbox hmb ↦ (href.inbox_ne_self p c inbox hmb).symm)]
    exact hself
  rcases href.labels p l hl.2 with ⟨brs, brs', hcode⟩ | ⟨c, inbox, hrx⟩
  · have hlabel : l ∈ L₁ := by
      rcases (hproc.1 ▸ hl.1 : l ∈ L₁ ∪ rx p) with hmem | hmem
      · exact hmem
      · exact (hcode.not_rx hmem).elim
    obtain ⟨Br', hBr', habort'⟩ := hcode.target_abort_le _ habort
    obtain ⟨ε', hpfx, Br, hBr, hsabort⟩ :=
      blockRefines_abort_indexed (hcode.refines pref)
        (relatesTo_of_procRelatesTo hproc (hkey p) hfifo .none) hBr' habort'
    exact ⟨ε', hpfx, p, ⟨M₁, L₁⟩, hS, l, ⟨hlabel, hcode.owned⟩,
      hcode.source_aborting Br hBr hsabort, hself'⟩
  · -- the instance receives, so it has an inbox, and then the relay cannot go wrong
    obtain ⟨ibp, hibp⟩ : ∃ ibp, ib p = .some ibp := by
      refine Option.ne_none_iff_exists'.mp ?_
      intro hnn
      rw [hrx.mailbox, hnn] at hproc
      nomatch hproc.2.2
    rw [hrx.mailbox, hibp] at hproc
    absurd rxBranch_not_aborting (ε := ε) hrx.chan_fresh hproc (hpresent p ibp hibp)
    exact hrx.target_abort_le habort

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

omit [SeqBuiltins V] in
/-- **And the whole diverging semantics.** `Algebra.diverging` is `step^∞` by definition, so this is
`Diverging.omegaStutter` at `step_or_stutter` — the same three-way obligation the other two halves
are built from, here with its measure disjunct finally load-bearing.

`FIFOs.size` is the measure: a receiving thread's relay moves one message out of a channel, and only
a `send` puts one back — and a `send` is a code thread's step, which *does* move the source. So the
target cannot relay forever while the source stands still, the source's steps are cofinal in the
target's, and deleting the idle indices leaves a genuine infinite source run. -/
theorem algRelatesTo.diverging [DecidableEq ι] {Aₛ Aₜ : Algebra ι V} {mb : ι → Mailbox}
    {rx : ι → Set String} (href : AlgebraRefines Aₛ Aₜ mb rx) :
    StrongRefinement.Diverging (algRelatesTo (V := V) mb rx) (instTrace (V := V)).Rτ
      Aₛ.diverging Aₛ.aborting Aₜ.diverging :=
  StrongRefinement.Diverging.omegaStutter (μ := λ S ↦ GuardedPlusCal.FIFOs.size S.2)
    rτ_omega ωProd_comp Stream'.Seq.hasPartialProdDvd Relation.star.lcomp₁_absorb
    (λ _ _ _ _ hrel hstep ↦ algRelatesTo.step_or_stutter href hrel hstep)

omit [SeqBuiltins V] in
/-- **And the whole aborting semantics.** `Algebra.aborting` is `step* ∘ᵣ₁ immediateAbort` by
definition, so this is `Aborting.starStutter` at that — the immediate half above, lifted over the run
that precedes it by the same per-step `Terminating` the reducing half uses.

Two of `StrongRefinement`'s three components are now in hand; `Diverging` is the one left. -/
theorem algRelatesTo.aborting [DecidableEq ι] {Aₛ Aₜ : Algebra ι V} {mb : ι → Mailbox}
    {rx : ι → Set String} (href : AlgebraRefines Aₛ Aₜ mb rx) :
    StrongRefinement.Aborting (algRelatesTo (V := V) mb rx) (instTrace (V := V)).Rτ
      Aₛ.aborting Aₜ.aborting :=
  StrongRefinement.Aborting.starStutter (algRelatesTo.terminating href)
    (algRelatesTo.immediateAbort href)

omit [SeqBuiltins V] in
/-- **The algorithm-level refinement, whole.** All three components at the closed forms
`Algebra.reducing`/`.aborting`/`.diverging`, against one state relation.

What remains for item 7 is on the other side of this statement: `AlgebraRefines` has to be
*established* from a compiled algorithm (D8, `Thread.toNetwork`), and `Algorithm.init` has to
establish `algRelatesTo` at the initial states. Nothing further is owed by the refinement argument
itself. -/
theorem algRelatesTo.refines [DecidableEq ι] {Aₛ Aₜ : Algebra ι V} {mb : ι → Mailbox}
    {rx : ι → Set String} (href : AlgebraRefines Aₛ Aₜ mb rx) :
    StrongRefinement (algRelatesTo (V := V) mb rx) (instTrace (V := V)).Rτ
      Aₛ.reducing Aₛ.aborting Aₛ.diverging Aₜ.reducing Aₜ.aborting Aₜ.diverging where
  terminating := algRelatesTo.terminating_reducing href
  aborting := algRelatesTo.aborting href
  diverging := algRelatesTo.diverging href

/-! # The pass at this level: the whole algorithm, compiled

  D8's last rung. `Algorithm.toNetwork` maps `Process.toNetwork` over the algorithm's processes and
  keeps the global state, so the syntactic half is `Spec.mapM_list` a fourth time and nothing more.

  The semantic half — turning the resulting `ProcessRefines` into the `AlgebraRefines` above — is a
  different kind of step and is not here. It has to go through `Algorithm.algebra`'s by-name lookup
  on both sides, and it is the first place the two languages' `Process.codeTable`s are compared
  rather than their syntax.
-/

/-! ## `mb` and `rx`, read off the compiled processes

  `AlgebraRefines` is indexed by instances (`ι = String × V`) while the pass's data is positional in
  a list, and `Algorithm.algebra` bridges the two by looking a process up under its *name*. So both
  functions are that lookup composed with something local to the compiled process — no existential,
  no choice, and `.none` for a process that has no receiving thread, which is exactly the mailbox a
  receive-free process must have.

  `List.Forall₂.find?_right` is what makes the lookup usable: the two `find?`s walk their lists in
  step, so a target process found under a name is the compilation of the source process found under
  the same one. `ProcessRefines.name_eq` is what makes the two predicates agree on related pairs.
-/

/-- **The mailbox of the process an instance belongs to.** An algorithm has no mailbox; its processes
do, and an instance's is its process's. Found by name, then read off the process's receiving thread —
`.none` when it has none.

Reading it off the *thread* is provisional: the source process carries a declared `@mailbox` field
which `Process.toNetwork` copies across, and that is where this should come from. The front end now
makes that field trustworthy — `checkReceiveChannels` rejects a `receive` with no declaration and
drops a declaration no `receive` uses (`PLAN.md` §5.2a) — so this becomes `p'.mailbox` when D8 is
assembled. -/
def procMailbox (algo' : ComputableNetworkPlusCal.Algorithm) : String × V → Mailbox :=
  λ ⟨name, _⟩ ↦ (algo'.processes.find? (·.name == name)).bind λ p' ↦
    p'.threads.findSome? λ T ↦ match T with
      | .rx chan _ _ ib => some (chan, ib)
      | .code _ => none

/-- And the receiving labels of the process an instance belongs to, found the same way. -/
def procRxLabels (algo' : ComputableNetworkPlusCal.Algorithm) : String × V → Set String :=
  λ ⟨name, _⟩ ↦ (algo'.processes.find? (·.name == name)).elim ∅ rxLabels

/-- **The source-side half of D8's contract, at the top.** Every process of the algorithm is
`ProcessFresh` at the channel the mailbox assignment gives its name.

`c₀` and `mbox` are keyed by process *name* rather than carried per process, because that is how the
algorithm layer indexes: `Algorithm.algebra` resolves a process instance `⟨name, self⟩` by looking
`name` up. `mbox`'s second argument is the name the pass will generate, which is why it is a function
and not a `Mailbox` — see `ProcessFresh`. -/
def AlgorithmFresh (mbox : String → String → Mailbox)
  (c₀ : String → ComputableGuardedPlusCal.Ref)
  (algo : ComputableGuardedPlusCal.Algorithm) : Prop :=
    ∀ p ∈ algo.processes, ProcessFresh (mbox p.name) (c₀ p.name) p

open Std.Do in
/-- **The walk over an algorithm's processes.** `Process.toNetwork_spec` iterated by
`Spec.mapM_list`.

The per-process `inbox` stays existential inside the `Forall₂` rather than being collected into a
function. Turning it into the `mb : ι → Mailbox` that `AlgebraRefines` wants is the semantic half's
business, and it needs the by-name lookup anyway. -/
private theorem mapM_processToNetwork_spec {globalChans : Guarded2NetworkChans}
  {mbox : String → String → Mailbox} {c₀ : String → ComputableGuardedPlusCal.Ref}
  {pref : ChanKey V → List V} {ps : List ComputableGuardedPlusCal.Process}
  (fresh : ∀ p ∈ ps, ProcessFresh (mbox p.name) (c₀ p.name) p) :
    ⦃⌜True⌝⦄
    ps.mapM (ComputableGuardedPlusCal.Process.toNetwork (m := G2NM) globalChans)
    ⦃⇓? ps' _ => ⌜List.Forall₂
      (λ p p' ↦ ∃ inbox, ProcessRefines (V := V) (mbox p.name inbox) (c₀ p.name) inbox pref p p')
      ps ps'⌝⦄ := by
  mvcgen [Process.toNetwork_spec]
  invariants
  | inv1 => ⇓? ⟨cur, res⟩ _ =>
    ⌜List.Forall₂
      (λ p p' ↦ ∃ inbox, ProcessRefines (V := V) (mbox p.name inbox) (c₀ p.name) inbox pref p p')
      cur.prefix res⌝
  with
  -- `Process.toNetwork_spec`'s seven implicits, answered by shape rather than by tag. Three the
  -- context already holds; the mailbox and the channel are functions of *which* process, so they are
  -- read off the walk's position; the last is the freshness hypothesis at that same process. One
  -- alternative rather than seven, because the tags carry no information — they renumber whenever a
  -- rung below gains a hypothesis, and `cur✝` is the only bare `Process` in scope either way.
  | vc5 | vc6 | vc7 | vc8 | vc9 | vc10 | vc11 =>
    intro _ _
    first
      | assumption
      | exact mbox ‹ComputableGuardedPlusCal.Process›.name
      | exact c₀ ‹ComputableGuardedPlusCal.Process›.name
      | (rw [‹ps = _ ++ _ :: _›] at fresh
         exact fresh _ (List.mem_append_right _ List.mem_cons_self))

  case vc1.pre => exact .nil
  case vc2.post.success => exact id

  case vc3.post.success _ _ _ _ _ _ _ hinv _ =>
    intro _ hcur
    exact List.rel_append hinv (List.forall₂_singleton.mpr hcur)

open Std.Do in
/-- **The whole algorithm, compiled — D8's syntactic half.** The walk over the processes, plus the
global state carried across unchanged.

`globalState` is reported because `Algorithm.init` is stated against it: the clause fixing every
declared channel's initial queue quantifies over `algo.globalState.channels ++ .fifos`, and the
initial-state obligation needs those to be the same two lists on both sides. Nothing in
`AlgebraRefines` wants it. -/
theorem Algorithm.toNetwork_spec {mbox : String → String → Mailbox}
  {c₀ : String → ComputableGuardedPlusCal.Ref} {pref : ChanKey V → List V}
  {algo : ComputableGuardedPlusCal.Algorithm} (fresh : AlgorithmFresh mbox c₀ algo) :
    ⦃⌜True⌝⦄
    ComputableGuardedPlusCal.Algorithm.toNetwork (m := G2NM) algo
    ⦃⇓? algo' _ => ⌜algo'.globalState = algo.globalState ∧
      List.Forall₂
        (λ p p' ↦ ∃ inbox, ProcessRefines (V := V) (mbox p.name inbox) (c₀ p.name) inbox pref p p')
        algo.processes algo'.processes⌝⦄ := by
  -- `-Spec.mapM_list` for the reason it is needed at every rung: the generic loop spec would match
  -- the walk before `mapM_processToNetwork_spec` does
  mvcgen [ComputableGuardedPlusCal.Algorithm.toNetwork, mapM_processToNetwork_spec,
    -Std.Do.Spec.mapM_list]

end Guarded2Network

end
