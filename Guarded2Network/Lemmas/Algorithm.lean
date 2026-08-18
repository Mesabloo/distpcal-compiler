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
  two per-step lemmas already ask for and nothing more; they are what a compiled algebra has to
  supply.

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

This is the interface `algRelatesTo.terminating` consumes and `Thread.toNetwork` produces. Written
top-down, from what the two per-step lemmas need, so that establishing it is a question about the
pass rather than about the proof. -/
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
at exactly this shape. -/
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
that precedes it by the same per-step `Terminating` the reducing half uses. -/
theorem algRelatesTo.aborting [DecidableEq ι] {Aₛ Aₜ : Algebra ι V} {mb : ι → Mailbox}
    {rx : ι → Set String} (href : AlgebraRefines Aₛ Aₜ mb rx) :
    StrongRefinement.Aborting (algRelatesTo (V := V) mb rx) (instTrace (V := V)).Rτ
      Aₛ.aborting Aₜ.aborting :=
  StrongRefinement.Aborting.starStutter (algRelatesTo.terminating href)
    (algRelatesTo.immediateAbort href)

omit [SeqBuiltins V] in
/-- **The algorithm-level refinement, whole.** All three components at the closed forms
`Algebra.reducing`/`.aborting`/`.diverging`, against one state relation.

`AlgebraRefines` itself is established from a compiled algorithm by `Thread.toNetwork`, and
`algRelatesTo` at the initial states by `Algorithm.init`; the refinement argument asks for nothing
beyond those two. -/
theorem algRelatesTo.refines [DecidableEq ι] {Aₛ Aₜ : Algebra ι V} {mb : ι → Mailbox}
    {rx : ι → Set String} (href : AlgebraRefines Aₛ Aₜ mb rx) :
    StrongRefinement (algRelatesTo (V := V) mb rx) (instTrace (V := V)).Rτ
      Aₛ.reducing Aₛ.aborting Aₛ.diverging Aₜ.reducing Aₜ.aborting Aₜ.diverging where
  terminating := algRelatesTo.terminating_reducing href
  aborting := algRelatesTo.aborting href
  diverging := algRelatesTo.diverging href

/-! # The pass at this level: the whole algorithm, compiled

  `Algorithm.toNetwork` maps `Process.toNetwork` over the algorithm's processes and keeps the
  global state, so the syntactic half is `Spec.mapM_list` a fourth time and nothing more.

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

The declared `@mailbox` field cannot serve: it is `Option (String × List Expr)`, which carries
neither the generated `inbox` nor a `Ref` — `rxMailbox`'s own doc says what is missing. What the
field is good for is the *decision*, and that enters `procMailbox_eq` below as a hypothesis. -/
def procMailbox (algo' : ComputableNetworkPlusCal.Algorithm) : String × V → Mailbox :=
  λ ⟨name, _⟩ ↦ (algo'.processes.find? (·.name == name)).bind rxMailbox

/-- And the receiving labels of the process an instance belongs to, found the same way. -/
def procRxLabels (algo' : ComputableNetworkPlusCal.Algorithm) : String × V → Set String :=
  λ ⟨name, _⟩ ↦ (algo'.processes.find? (·.name == name)).elim ∅ rxLabels

/-- **What a process declares its mailbox to be, as the pass gets to assume it.** After
`checkReceiveChannels` a `@mailbox` field is present exactly when the process has a `receive` to use
it, so a mailbox assignment that says `.some` is one whose process receives.

Only that direction is needed, and only that direction is a front-end fact. The converse — a process
that receives has a mailbox — is what `BranchesFresh.mbox_some` already carries down the ladder. -/
def MailboxUsed (mbox : String → String → Mailbox)
  (algo : ComputableGuardedPlusCal.Algorithm) : Prop :=
    ∀ p ∈ algo.processes, ∀ inbox, mbox p.name inbox ≠ .none → ProcessReceives p

variable {mbox : String → String → Mailbox} {c₀ : String → ComputableGuardedPlusCal.Ref}
  {pref : ChanKey V → List V} {algo : ComputableGuardedPlusCal.Algorithm}
  {algo' : ComputableNetworkPlusCal.Algorithm} {name : String} {v : V}
  {p' : ComputableNetworkPlusCal.Process}

/-- **The pass's output, as the algorithm level receives it.** `Algorithm.toNetwork_spec`'s
postcondition, named because everything below quantifies over it. -/
abbrev ProcessesRefine (mbox : String → String → Mailbox)
  (c₀ : String → ComputableGuardedPlusCal.Ref) (pref : ChanKey V → List V)
  (algo : ComputableGuardedPlusCal.Algorithm) (algo' : ComputableNetworkPlusCal.Algorithm) : Prop :=
    List.Forall₂
      (λ p p' ↦ ∃ inbox, ProcessRefines (V := V) (mbox p.name inbox) (c₀ p.name) inbox pref p p')
      algo.processes algo'.processes

omit [SeqBuiltins V] in
/-- **Instance resolution.** A compiled process found under a name is the compilation of the source
process found under that same name — the step every clause below opens with, since both algebras
resolve an instance `⟨name, self⟩` by exactly this lookup.

`List.Forall₂.find?_right` is what makes it work: the two `find?`s walk their lists in step, so
agreement on the *predicate* at related pairs is enough, and `ProcessRefines.name_eq` is that
agreement. The target side is the hypothesis rather than the source's because that is the direction
the clauses need — `AlgebraRefines` quantifies over labels the *target* owns. -/
theorem find?_refines (href : ProcessesRefine (V := V) mbox c₀ pref algo algo')
    (hfind : algo'.processes.find? (·.name == name) = some p') :
    ∃ p inbox, algo.processes.find? (·.name == name) = some p ∧ p.name = name ∧
      ProcessRefines (V := V) (mbox p.name inbox) (c₀ p.name) inbox pref p p' := by
  have hname_eq (p : ComputableGuardedPlusCal.Process) (p'' : ComputableNetworkPlusCal.Process)
      (h : ∃ inbox, ProcessRefines (V := V) (mbox p.name inbox) (c₀ p.name) inbox pref p p'') :
      (p.name == name) = (p''.name == name) := by
    obtain ⟨_, hpr⟩ := h
    rw [hpr.name_eq]
  obtain ⟨p, hfinds, inbox, hpr⟩ := href.find?_right hname_eq hfind
  refine ⟨p, inbox, hfinds, ?_, hpr⟩
  simpa using List.find?_some hfinds

variable {p : ComputableGuardedPlusCal.Process} {inbox : String}

omit [SeqBuiltins V] in
/-- **`procMailbox` computes the mailbox the refinement was proved at.** The per-process
`ProcessRefines.rxMailbox_eq` at the resolved instance.

Stated against the resolution's own `p`/`inbox` rather than existentially, because every consumer has
already run `find?_refines` and needs the two sides of the equation to be the *same* mailbox as the
`ProcessRefines` it is holding. -/
theorem procMailbox_eq (hfind : algo'.processes.find? (·.name == name) = some p')
    (hpr : ProcessRefines (V := V) (mbox p.name inbox) (c₀ p.name) inbox pref p p')
    (hused : mbox p.name inbox ≠ .none → ProcessReceives p) :
    procMailbox algo' (name, v) = mbox p.name inbox := by
  simp only [procMailbox, hfind, Option.bind_some]
  exact hpr.rxMailbox_eq hused

omit [SeqBuiltins V] in
/-- **Both algebras answer a resolved instance from the process itself.** `Algorithm.algebra`'s
`table`/`owned` are the by-name lookup composed with the process's own `codeTable`/`ownedLabels`, and
every `ProcessRefines` field lemma is stated against those bare forms — so each of the four is one
`Option.elim` in the way. -/
theorem tgt_algebra_table (hfind : algo'.processes.find? (·.name == name) = some p') :
    (NetworkPlusCal.Algorithm.algebra algo').table (name, v) =
      NetworkPlusCal.Process.codeTable p' := by
  simp only [NetworkPlusCal.Algorithm.algebra, hfind, Option.elim_some]

omit [SeqBuiltins V] in
@[inherit_doc tgt_algebra_table]
theorem tgt_algebra_owned (hfind : algo'.processes.find? (·.name == name) = some p') :
    (NetworkPlusCal.Algorithm.algebra algo').owned (name, v) =
      NetworkPlusCal.Process.ownedLabels p' := by
  simp only [NetworkPlusCal.Algorithm.algebra, hfind, Option.elim_some]

omit [SeqBuiltins V] in
@[inherit_doc tgt_algebra_table]
theorem src_algebra_table (hfind : algo.processes.find? (·.name == name) = some p) :
    (GuardedPlusCal.Algorithm.algebra algo).table (name, v) =
      GuardedPlusCal.Process.codeTable p := by
  simp only [GuardedPlusCal.Algorithm.algebra, hfind, Option.elim_some]

omit [SeqBuiltins V] in
@[inherit_doc tgt_algebra_table]
theorem src_algebra_owned (hfind : algo.processes.find? (·.name == name) = some p) :
    (GuardedPlusCal.Algorithm.algebra algo).owned (name, v) =
      GuardedPlusCal.Process.ownedLabels p := by
  simp only [GuardedPlusCal.Algorithm.algebra, hfind, Option.elim_some]

omit [SeqBuiltins V] [ExprSemantics V] in
/-- **`procRxLabels` is the resolved process's own receiving labels.** The lookup and nothing else —
no refinement is involved, `rxLabels` being a fact about the compiled process alone. Stated anyway
because every `AlgebraRefines` clause mentioning `rx p` has to get past the `Option.elim` first, and
`ProcessRefines`' six `rxLabels` lemmas are all phrased against the bare process. -/
theorem procRxLabels_eq (hfind : algo'.processes.find? (·.name == name) = some p') :
    procRxLabels algo' (name, v) = rxLabels p' := by
  simp only [procRxLabels, hfind, Option.elim_some]

omit [SeqBuiltins V] in
/-- **`AlgebraRefines.inbox_ne_self`, discharged.** A mailbox `procMailbox` reports is one a process
registered a thread for, so its `inbox` is a name `freshName` generated, and no generated name is
`self` (`Generated.ne_selfName`).

Load-bearing rather than hygiene: `CodeTable.procReducing` requires the memory to bind `selfName`,
and the source memory agrees with the target's only *away* from the generated name. -/
theorem procMailbox_inbox_ne_selfName (href : ProcessesRefine (V := V) mbox c₀ pref algo algo')
    (used : MailboxUsed mbox algo) {c : ComputableGuardedPlusCal.Ref} {ib : String}
    (hm : procMailbox algo' (name, v) = .some (c, ib)) : ib ≠ GuardedPlusCal.selfName := by
  -- a `.some` answer means the lookup found a process, `Option.bind` being `.none` otherwise
  cases hfind : algo'.processes.find? (·.name == name) with
  | none => simp only [procMailbox, hfind, Option.bind_none, reduceCtorEq] at hm
  | some _ =>
    obtain ⟨p, inbox, hfinds, -, hpr⟩ := find?_refines href hfind
    have hused := used p (List.mem_of_find?_eq_some hfinds) inbox
    rw [procMailbox_eq hfind hpr hused] at hm
    -- a `.some` mailbox is the pair the ladder is stated against, whose name `freshName` generated
    have hne : mbox p.name inbox ≠ .none := by rw [hm]; nofun
    have heq := hpr.mailbox_eq hused hne
    rewrite [hm] at heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    exact hpr.inbox_generated.ne_selfName

/-- **The source-side freshness obligation, at the top.** Every process of the algorithm is
`ProcessFresh` at the channel the mailbox assignment gives its name.

`c₀` and `mbox` are keyed by process *name* rather than carried per process, because that is how the
algorithm layer indexes: `Algorithm.algebra` resolves a process instance `⟨name, self⟩` by looking
`name` up. `mbox`'s second argument is the name the pass will generate, which is why it is a function
and not a `Mailbox` — see `ProcessFresh`. -/
def AlgorithmFresh (mbox : String → String → Mailbox)
  (c₀ : String → ComputableGuardedPlusCal.Ref)
  (algo : ComputableGuardedPlusCal.Algorithm) : Prop :=
    ∀ p ∈ algo.processes, ProcessFresh (mbox p.name) (c₀ p.name) p

omit [SeqBuiltins V] in
/-- **The compiled algebra refines** the source's, at the mailbox and receiving labels
read off the compiled algorithm. Every clause is one lemma at the resolved instance and nothing else;
`find?_refines` is what turns an instance into a related process pair, and the four
`*_algebra_table`/`*_algebra_owned` lemmas are what get past the `Option.elim` to the field lemmas.

`href` quantifies over `pref` because `CodeLabelRefines.refines` does. Which prefix function the
algorithm level hands down is not known per process, and `Algorithm.toNetwork_spec` holds at every
one — the `inbox` each instantiation witnesses may differ, but `procMailbox_eq` pins all of them to
the same `procMailbox algo'`, so the mailbox the clause is stated at does not.

The two hypotheses that are not the pass's are the front end's: `used` says a declared mailbox is one
its process receives on (`checkReceiveChannels`), and `hyg` that no source label is one the pass could
generate (the `$` argument, discharged for every counter value at once). -/
theorem algebraRefines
    (href : ∀ pref : ChanKey V → List V, ProcessesRefine (V := V) mbox c₀ pref algo algo')
    (used : MailboxUsed mbox algo) (fresh : AlgorithmFresh mbox c₀ algo)
    (hyg : ∀ p ∈ algo.processes, LabelsHygienic p) :
    AlgebraRefines (V := V) (GuardedPlusCal.Algorithm.algebra algo)
      (NetworkPlusCal.Algorithm.algebra algo') (procMailbox algo') (procRxLabels algo') where
  self_eq _ := rfl
  inbox_ne_self := λ ⟨_, _⟩ _ _ hm ↦ procMailbox_inbox_ne_selfName (href λ _ ↦ []) used hm
  labels := by
    rintro ⟨name, v⟩ l hl
    -- an instance whose name resolves to no process owns no label at all
    cases hfind : algo'.processes.find? (·.name == name) with
    | none =>
      simp only [NetworkPlusCal.Algorithm.algebra, hfind, Option.elim_none,
        Set.mem_empty_iff_false] at hl
    | some p' =>
      obtain ⟨p, inbox, hfinds, -, hpr⟩ := find?_refines (href λ _ ↦ []) hfind
      have hmem : p ∈ algo.processes := List.mem_of_find?_eq_some hfinds
      have hused := used p hmem inbox
      have hmb := procMailbox_eq (v := v) hfind hpr hused
      rw [tgt_algebra_owned hfind] at hl
      rcases hpr.label_cases (hyg p hmem) hl with ⟨hsrc, hnrx⟩ | ⟨hrx, hnsrc⟩
      -- a code label: the branches its block has on each side
      · refine .inl ⟨srcBranchesAt p l, tgtBranchesAt p' l, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [procRxLabels_eq hfind]
          exact hnrx
        · rw [src_algebra_owned hfinds]
          exact hsrc
        · intro _ _ _ _ _ _ hstep
          rw [tgt_algebra_table hfind] at hstep
          rw [procRxLabels_eq hfind]
          exact hpr.exits (hyg p hmem) hnrx hstep
        -- the refinement is owed at every prefix function, so the walk is re-resolved at each; the
        -- `inbox` it witnesses need not be the one above, but the mailbox it names is
        · intro pref'
          obtain ⟨p₂, inbox₂, hfinds₂, -, hpr₂⟩ := find?_refines (href pref') hfind
          rw [hfinds] at hfinds₂
          obtain rfl := Option.some.inj hfinds₂
          rw [procMailbox_eq (v := v) hfind hpr₂ (used _ hmem inbox₂)]
          exact hpr₂.branchesRefine l
        · intro Br hBr c ib hmbeq
          rw [hmb] at hmbeq
          have hne : mbox p.name inbox ≠ .none := by rw [hmbeq]; nofun
          have heq := hpr.mailbox_eq hused hne
          -- so the pair the clause was handed is the one the ladder is stated against
          rewrite [heq] at hmbeq
          simp only [Option.some.injEq, Prod.mk.injEq] at hmbeq
          obtain ⟨rfl, rfl⟩ := hmbeq
          rw [← heq]
          obtain ⟨T, hT, blk, hblk, -, hBrmem⟩ := mem_srcBranchesAt.mp hBr
          exact fresh p hmem inbox hpr.inbox_generated T hT blk hblk Br hBrmem
        · rw [tgt_algebra_table hfind]
          exact tgt_reducing_le hnrx
        · rw [tgt_algebra_table hfind]
          exact tgt_aborting_le hnrx
        · intro _ hBr
          rw [src_algebra_table hfinds]
          exact src_reducing_le hBr
        · intro _ hBr
          rw [src_algebra_table hfinds]
          exact src_aborting_le hBr
      -- a receiving label: no source counterpart at all, only the relay
      · obtain ⟨_, _, _, hT⟩ := hrx
        refine .inr ⟨c₀ p.name, inbox, ?_, ?_, ?_, ?_, ?_⟩
        · rw [procRxLabels_eq hfind]
          exact ⟨_, _, _, hT⟩
        · rw [hmb]
          exact (hpr.rxThread hT).1
        · exact (hpr.rxThread hT).2.1
        -- the relay bound is stated at "the source owns no such label", `label_cases`' negative half
        · rw [tgt_algebra_table hfind]
          exact hpr.rx_target_le hnsrc
        · rw [tgt_algebra_table hfind]
          exact hpr.rx_target_abort_le hnsrc

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
  -- `Process.toNetwork_spec`'s seven implicits, answered by shape rather than by tag: three the
  -- context already holds, the mailbox and the channel read off the walk's position, and the
  -- freshness hypothesis at that same process.
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
/-- **The whole algorithm, compiled — the syntactic half.** The walk over the processes, plus the
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
  -- `-Spec.mapM_list`, or the generic loop spec matches the walk before `mapM_processToNetwork_spec`
  mvcgen [ComputableGuardedPlusCal.Algorithm.toNetwork, mapM_processToNetwork_spec,
    -Std.Do.Spec.mapM_list]

open Std.Do in
/-- **The pass is correct.** Compiling an algorithm yields one whose algebra refines the source's,
under `algRelatesTo` at the mailbox and receiving labels the compiled algorithm itself determines.

Everything in this development meets here. `Algorithm.toNetwork_spec` is the syntactic half, the
four walks; `algebraRefines` is its semantic half, turning the per-process refinement into the
algebra-level dispatch; `algRelatesTo.refines` is the refinement argument, `Terminating`/`Aborting`/
`Diverging` at the three closed forms. `triple_forall` is the joint: `CodeLabelRefines.refines` is
needed at every prefix function and the spec supplies one per instantiation.

The three hypotheses are the front end's, not the pass's. `AlgorithmFresh` is the syntactic
conditions on the source program and the generated `inbox`; `MailboxUsed` says a declared mailbox is
one its process receives on (`checkReceiveChannels`); `LabelsHygienic` that no source label is one
the pass could generate (the `$` argument).

Relating `Algorithm.init`'s initial states under `algRelatesTo` is a separate statement, and
`Algorithm.toNetwork_spec` reports `globalState` because that is what it is stated against. -/
theorem Algorithm.toNetwork_refines [DecidableEq V] {mbox : String → String → Mailbox}
  {c₀ : String → ComputableGuardedPlusCal.Ref} {algo : ComputableGuardedPlusCal.Algorithm}
  (fresh : AlgorithmFresh mbox c₀ algo) (used : MailboxUsed mbox algo)
  (hyg : ∀ p ∈ algo.processes, LabelsHygienic p) :
    ⦃⌜True⌝⦄
    ComputableGuardedPlusCal.Algorithm.toNetwork (m := G2NM) algo
    ⦃⇓? algo' _ => ⌜algo'.globalState = algo.globalState ∧
      StrongRefinement (algRelatesTo (V := V) (procMailbox algo') (procRxLabels algo'))
        (instTrace (V := V)).Rτ
        (GuardedPlusCal.Algorithm.algebra algo).reducing
        (GuardedPlusCal.Algorithm.algebra algo).aborting
        (GuardedPlusCal.Algorithm.algebra algo).diverging
        (NetworkPlusCal.Algorithm.algebra algo').reducing
        (NetworkPlusCal.Algorithm.algebra algo').aborting
        (NetworkPlusCal.Algorithm.algebra algo').diverging⌝⦄ := by
  refine triple_forall (ι := ChanKey V → List V)
    (λ pref ↦ Algorithm.toNetwork_spec (V := V) (pref := pref) fresh) ?_
  intro algo' h
  refine ⟨(h λ _ ↦ []).1, algRelatesTo.refines ?_⟩
  exact algebraRefines (λ pref ↦ (h pref).2) used fresh hyg

/-! # The initial state

  A `StrongRefinement` says nothing at all unless the two algorithms' *initial* states are related:
  with `algRelatesTo` never holding, it is vacuously true. What gives `Algorithm.toNetwork_refines`
  content is that every initial state of the compiled algorithm has one of the source's related to
  it, and that is what this section proves.

  Both `init`s have the same shape and their FIFO clause is *identical* on the two sides —
  `Algorithm.toNetwork_spec` reports `algo'.globalState = algo.globalState` for exactly this reason —
  so the source state is built on the target's own FIFO map, and the whole obligation is about the
  instances. There the pass makes three differences to a process, and each is one clause of
  `procRelatesTo`: the entry labels gain the receiving threads' (`ProcessRefines.entryLabels_eq`),
  the locals gain the `inbox` (`ProcessRefines.inits_eq`), and the instance starts receiving on a key.

  Only the last is beyond the pass. Nothing it compiles decides whether a channel's index expressions
  evaluate, whether what they resolve to is a FIFO the module declared, or whether two instances
  resolve to the same one. Those are the front end's, and `InitKeys` is where they enter.
-/

/-- **The key each receiving instance starts on, and what the front end owes about it.** A witness
function rather than an existential per instance, for the reason `algRelatesTo`'s own `ib` is one:
the FIFO clauses speak about every key at once, and a per-instance existential would leave nothing
relating them. -/
structure InitKeys (c₀ : String → ComputableGuardedPlusCal.Ref)
  (algo : ComputableGuardedPlusCal.Algorithm) (F : FIFOs V) (key : String × V → ChanKey V) :
    Prop where
  /-- The mailbox channel resolves, in each instance's own initial memory, to that instance's key. -/
  resolves : ∀ p ∈ algo.processes, ∀ self : V, ∀ σ : ProcState V,
    GuardedPlusCal.InitProc self p.inits (GuardedPlusCal.Process.entryLabels p) σ →
    ProcessReceives p →
      (key (p.name, self)).1 = (c₀ p.name).name ∧
        List.Forall₂ (GuardedPlusCal.EvalStep σ.1) (c₀ p.name).args (key (p.name, self)).2
  /-- And the key names a channel that exists. `algRelatesTo` carries this as an invariant because a
  compiled relay *aborts* where the FIFO is absent and the source has no relay to abort with;
  establishing it at the initial state is this clause. -/
  declared : ∀ p ∈ algo.processes, ∀ self : V, ProcessReceives p →
    F.lookup (key (p.name, self)) ≠ .none
  /-- And no two receiving instances share one — the well-formedness condition that a process set's
  mailbox is indexed by `self` (`WellFormednessError.mailboxNotIndexedBySelf`). Without it one FIFO
  would be accounted against two inboxes, and no relation of `algRelatesTo`'s shape could hold. -/
  inj : ∀ p ∈ algo.processes, ∀ q ∈ algo.processes, ∀ self self' : V,
    ProcessReceives p → ProcessReceives q →
    key (p.name, self) = key (q.name, self') → (p.name, self) = (q.name, self')

omit [SeqBuiltins V] in
/-- **Every initializer the pass invents evaluates.** `<<>>` has a value under any memory
(`ExprSemantics.eval_seq_nil`, stated as existence for this), and those are the only initializers the
pass writes — which is what makes a compiled instance have an initial state wherever its source has
one. -/
private theorem exists_inboxInit_values {ninits : List (String × ComputablePlusCal.Expression)}
  (hin : ∀ e ∈ ninits, InboxInit inbox e) (M : Memory V) :
    ∃ ws : List V, List.Forall₂ (λ ie v ↦ ExprSemantics.Eval M (Prod.snd ie) v) ninits ws := by
  induction ninits with
  | nil => exact ⟨[], .nil⟩
  | cons e _ ih =>
    obtain ⟨ws, hws⟩ := ih λ x hx ↦ hin x (List.mem_cons_of_mem _ hx)
    obtain ⟨τ, rfl⟩ := hin e List.mem_cons_self
    obtain ⟨sv, hsv, -⟩ := ExprSemantics.eval_seq_nil (V := V) (M := M) (τ := τ)
    exact ⟨sv :: ws, .cons hsv hws⟩

omit [SeqBuiltins V] in
/-- **The two initial memories, related.** The compiled instance's is the source's with the pass's
own initializers folded on top, and every one of those declares `inbox` and initializes it to `<<>>`:
so nothing else moves, and where there is one at all, `inbox` ends up holding a value the semantics
says is the empty sequence.

Both directions of `Algorithm.init_refines` spend this — the memory relation is the same statement
whichever of the two states was built from the other. -/
private theorem initMem_relates {ninits : List (String × ComputablePlusCal.Expression)}
  {ws : List V} {M M₀ : Memory V} (hin : ∀ e ∈ ninits, InboxInit inbox e)
  (hws : List.Forall₂ (λ ie v ↦ ExprSemantics.Eval M₀ (Prod.snd ie) v) ninits ws) :
    (∀ x ≠ inbox, (GuardedPlusCal.InitMem ninits ws M).lookup x = M.lookup x) ∧
      (ninits = [] → GuardedPlusCal.InitMem ninits ws M = M) ∧
      (ninits ≠ [] → ∃ sv, (GuardedPlusCal.InitMem ninits ws M).lookup inbox = .some sv ∧
        ExprSemantics.isSeq sv []) := by
  have hname (e : String × ComputablePlusCal.Expression) (he : e ∈ ninits) : e.1 = inbox := by
    obtain ⟨_, rfl⟩ := hin e he
    rfl
  refine ⟨λ _ hx ↦ GuardedPlusCal.InitMem.lookup_ne hname hx, ?_, ?_⟩
  · rintro rfl
    rfl
  · intro hne
    obtain ⟨sv, hsv, hlk⟩ := GuardedPlusCal.InitMem.lookup_mem hname hne hws.length_eq
    obtain ⟨e, he, heval⟩ := hws.exists_left hsv
    obtain ⟨_, rfl⟩ := hin e he
    exact ⟨sv, hlk, ExprSemantics.isSeq_of_eval_seq_nil heval⟩

omit [SeqBuiltins V] in
open Classical in
/-- **The initial states are related — the pass's correctness is not vacuous.** Every initial state
of the compiled algorithm has one of the source's related to it under `algRelatesTo`, at the same
mailbox and receiving labels `Algorithm.toNetwork_refines` is stated against.

The source state is built on the *target's* FIFO map, which is what `hglobal` buys: the two `init`s'
channel clauses are then the same statement, so the map that satisfies one satisfies the other. What
is left is the instances, and each is the target's own with the pass's three differences undone —
`ProcessRefines.inits_eq` to strip the `inbox` back off the initial memory, `.entryLabels_eq` to
strip the receiving threads off the label set, and `InitKeys` to say what the inbox is accounting
for.

`hnames` is the front end's, and is not bookkeeping: `Algorithm.algebra` resolves an instance by
`find?` on its process name, so two processes sharing one would have every instance of the second
running the first's code. It is what pins `find?` to the process an instance actually came from, on
both sides — the target's names are the source's, pointwise, by `ProcessRefines.name_eq`. -/
theorem Algorithm.init_refines {key : String × V → ChanKey V}
  {Ps' : Instances (String × V) V} {F : FIFOs V}
  (href : ProcessesRefine (V := V) mbox c₀ pref algo algo')
  (hglobal : algo'.globalState = algo.globalState) (used : MailboxUsed mbox algo)
  (hyg : ∀ p ∈ algo.processes, LabelsHygienic p)
  (hnames : (algo.processes.map (·.name)).Nodup) (hkeys : InitKeys (V := V) c₀ algo F key)
  (hinit : NetworkPlusCal.Algorithm.init algo' ⟨Ps', F⟩) :
    ∃ Ps : Instances (String × V) V, GuardedPlusCal.Algorithm.init algo ⟨Ps, F⟩ ∧
      (⟨Ps, F⟩ : AlgState (String × V) V) ≋[procMailbox algo', procRxLabels algo'] ⟨Ps', F⟩ := by
  -- the source instances: exactly the ones `init` asks for, so its first clause is definitional
  let Ps : Instances (String × V) V :=
    {x | ∃ p ∈ algo.processes, ∃ self ∈ GuardedPlusCal.Process.identities (V := V) p,
      x.1 = (p.name, self) ∧
        GuardedPlusCal.InitProc self p.inits (GuardedPlusCal.Process.entryLabels p) x.2}
  have hPs (i : String × V) (σ : ProcState V) :
      (⟨i, σ⟩ : (String × V) × ProcState V) ∈ Ps ↔
      ∃ p ∈ algo.processes, ∃ self ∈ GuardedPlusCal.Process.identities (V := V) p,
        i = (p.name, self) ∧
          GuardedPlusCal.InitProc self p.inits (GuardedPlusCal.Process.entryLabels p) σ := Iff.rfl
  have hsrcInit : GuardedPlusCal.Algorithm.init algo ⟨Ps, F⟩ := ⟨hPs, hglobal ▸ hinit.2⟩
  -- both sides resolve an instance to the process it came from, the target's names being the
  -- source's pointwise
  have hnameEq (q : ComputableGuardedPlusCal.Process) (q' : ComputableNetworkPlusCal.Process)
      (h : ∃ ib, ProcessRefines (V := V) (mbox q.name ib) (c₀ q.name) ib pref q q') :
      q.name = q'.name := by
    obtain ⟨_, hpr⟩ := h
    exact hpr.name_eq.symm
  have hnames' : (algo'.processes.map (·.name)).Nodup := href.map_eq_map hnameEq ▸ hnames
  have huniq (q : ComputableGuardedPlusCal.Process) (hq : q ∈ algo.processes)
      (r : ComputableGuardedPlusCal.Process) (hr : r ∈ algo.processes) (h : q.name = r.name) :
      q = r := List.inj_on_of_nodup_map hnames hq hr h
  have huniq' (q : ComputableNetworkPlusCal.Process) (hq : q ∈ algo'.processes)
      (r : ComputableNetworkPlusCal.Process) (hr : r ∈ algo'.processes) (h : q.name = r.name) :
      q = r := List.inj_on_of_nodup_map hnames' hq hr h
  have hres (q : ComputableGuardedPlusCal.Process) (hq : q ∈ algo.processes) :
      ∃ q' ib, algo'.processes.find? (·.name == q.name) = .some q' ∧
        ProcessRefines (V := V) (mbox q.name ib) (c₀ q.name) ib pref q q' := by
    have hbeq (r : ComputableGuardedPlusCal.Process) (r' : ComputableNetworkPlusCal.Process)
        (h : ∃ ib, ProcessRefines (V := V) (mbox r.name ib) (c₀ r.name) ib pref r r') :
        (r.name == q.name) = (r'.name == q.name) := by rw [hnameEq r r' h]
    have hsrc : algo.processes.find? (·.name == q.name) = .some q := by
      refine List.find?_eq_some_of_unique hq (beq_self_eq_true _) λ r hr hrn ↦ ?_
      exact huniq r hr q hq (eq_of_beq hrn)
    obtain ⟨q', hfind, ib, hpr⟩ := href.find?_left hbeq hsrc
    exact ⟨q', ib, hfind, hpr⟩
  -- an instance receives on its own key, when it receives at all
  let ib : String × V → Option (InboxState V) := λ i ↦
    if (∃ σ, (⟨i, σ⟩ : (String × V) × ProcState V) ∈ Ps) ∧ (procMailbox algo' i).isSome then
      .some ⟨key i, []⟩
    else .none
  have hibPos (i : String × V) (h₁ : ∃ σ, (⟨i, σ⟩ : (String × V) × ProcState V) ∈ Ps)
      (h₂ : (procMailbox algo' i).isSome) : ib i = .some ⟨key i, []⟩ := if_pos ⟨h₁, h₂⟩
  have hibNeg (i : String × V)
      (h : ¬ ((∃ σ, (⟨i, σ⟩ : (String × V) × ProcState V) ∈ Ps) ∧ (procMailbox algo' i).isSome)) :
      ib i = .none := if_neg h
  -- and an instance that has a key is a receiving process's, which is what `InitKeys`' clauses are
  -- conditioned on
  have hibRecv (i : String × V) (x : InboxState V) (h : ib i = .some x) :
      x = ⟨key i, []⟩ ∧
        ∃ q ∈ algo.processes, ∃ self : V, i = (q.name, self) ∧ ProcessReceives q := by
    by_cases hcond :
        (∃ σ, (⟨i, σ⟩ : (String × V) × ProcState V) ∈ Ps) ∧ (procMailbox algo' i).isSome
    · rw [hibPos i hcond.1 hcond.2] at h
      refine ⟨(Option.some.inj h).symm, ?_⟩
      obtain ⟨σ, hσ⟩ := hcond.1
      obtain ⟨q, hq, self, -, rfl, -⟩ := (hPs i σ).mp hσ
      obtain ⟨q', ibx, hfind, hpr⟩ := hres q hq
      refine ⟨q, hq, self, rfl, used q hq ibx ?_⟩
      have hisSome := hcond.2
      rw [procMailbox_eq hfind hpr (used q hq ibx)] at hisSome
      exact Option.isSome_iff_ne_none.mp hisSome
    · rw [hibNeg i hcond] at h
      exact nomatch h
  -- one instance, related. Both directions below spend this; they differ only in which of the two
  -- states was built from the other
  have hrel (q : ComputableGuardedPlusCal.Process) (hq : q ∈ algo.processes)
      (q' : ComputableNetworkPlusCal.Process) (ibx : String)
      (hfind : algo'.processes.find? (·.name == q.name) = .some q')
      (hpr : ProcessRefines (V := V) (mbox q.name ibx) (c₀ q.name) ibx pref q q') (self : V)
      (hself : self ∈ GuardedPlusCal.Process.identities (V := V) q) (σ σ' : ProcState V)
      (hσ : GuardedPlusCal.InitProc self q.inits (GuardedPlusCal.Process.entryLabels q) σ)
      (hσ' : GuardedPlusCal.InitProc self (NetworkPlusCal.Process.inits q')
        (NetworkPlusCal.Process.entryLabels q') σ') :
      procRelatesTo (procMailbox algo' (q.name, self)) (procRxLabels algo' (q.name, self))
        (ib (q.name, self)) σ σ' := by
    obtain ⟨M₂, L₂⟩ := σ'
    obtain ⟨ninits, hsplit, hin, hnilIff⟩ := hpr.inits_eq (used q hq ibx)
    rw [hsplit] at hσ'
    have hlab := hσ'.labels
    change L₂ = NetworkPlusCal.Process.entryLabels q' at hlab
    obtain ⟨M, ws, hM, hws, hmem⟩ :=
      GuardedPlusCal.InitProc.append (e₁ := GuardedPlusCal.Process.entryLabels q) hσ'
    change M₂ = GuardedPlusCal.InitMem ninits ws M at hmem
    obtain rfl := hσ.inj hM
    subst hmem
    obtain ⟨hoff, hnil, hsome⟩ := initMem_relates (M := M) hin hws
    rw [procRxLabels_eq hfind, procMailbox_eq hfind hpr (used q hq ibx)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hlab, hpr.entryLabels_eq, Set.union_comm]
    · exact Set.disjoint_of_subset_left GuardedPlusCal.Process.entryLabels_subset_ownedLabels
        (hpr.rx_disjoint (hyg q hq))
    · by_cases hmbox : mbox q.name ibx = .none
      · have hibnone : ib (q.name, self) = .none := by
          refine hibNeg _ ?_
          rintro ⟨-, hisSome⟩
          rw [procMailbox_eq hfind hpr (used q hq ibx), hmbox] at hisSome
          contradiction
        rw [hibnone, hmbox]
        exact (hnil (hnilIff.mpr hmbox)).symm
      · have hrecv := used q hq ibx hmbox
        have hmb := hpr.mailbox_eq (used q hq ibx) hmbox
        have hibsome : ib (q.name, self) = .some ⟨key (q.name, self), []⟩ := by
          refine hibPos _ ⟨_, (hPs _ _).mpr ⟨q, hq, self, hself, rfl, hσ⟩⟩ ?_
          rw [procMailbox_eq hfind hpr (used q hq ibx), hmb]
          rfl
        obtain ⟨hfst, hpath⟩ := hkeys.resolves q hq self _ hσ hrecv
        rw [hibsome, hmb]
        refine ⟨λ x hx ↦ (hoff x hx).symm, ?_, (key (q.name, self)).2, hpath, Prod.ext hfst rfl⟩
        exact hsome λ hnil' ↦ hmbox (hnilIff.mp hnil')
  refine ⟨Ps, hsrcInit, ib, λ _ ↦ [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact GuardedPlusCal.Algorithm.init.functional huniq hsrcInit
  · exact NetworkPlusCal.Algorithm.init.functional huniq' hinit
  -- every source instance has a compiled one: the pass's own initializers all evaluate, so the
  -- longer state exists wherever the shorter does
  · rintro i σ hσ
    obtain ⟨q, hq, self, hself, rfl, hσinit⟩ := (hPs i σ).mp hσ
    obtain ⟨q', ibx, hfind, hpr⟩ := hres q hq
    obtain ⟨ninits, hsplit, hin, -⟩ := hpr.inits_eq (used q hq ibx)
    obtain ⟨ws, hws⟩ :=
      exists_inboxInit_values hin (Finmap.singleton GuardedPlusCal.selfName self)
    have htgt : GuardedPlusCal.InitProc self (NetworkPlusCal.Process.inits q')
        (NetworkPlusCal.Process.entryLabels q')
        (GuardedPlusCal.InitMem ninits ws σ.1, NetworkPlusCal.Process.entryLabels q') := by
      rw [hsplit]
      exact GuardedPlusCal.InitProc.append_of hσinit hws
    refine ⟨_, (hinit.1 _ _).mpr ⟨q', List.mem_of_find?_eq_some hfind, self, ?_, ?_, htgt⟩,
      hrel q hq q' ibx hfind hpr self hself _ _ hσinit htgt⟩
    · rw [hpr.identities_eq]
      exact hself
    · rw [hpr.name_eq]
  -- and every compiled instance has a source one: strip the pass's initializers back off
  · rintro i σ' hσ'
    obtain ⟨q', hq', self, hself', rfl, hσ'init⟩ := (hinit.1 i σ').mp hσ'
    have hfind : algo'.processes.find? (·.name == q'.name) = .some q' := by
      refine List.find?_eq_some_of_unique hq' (beq_self_eq_true _) λ r hr hrn ↦ ?_
      exact huniq' r hr q' hq' (eq_of_beq hrn)
    obtain ⟨q, ibx, hsrcfind, hqname, hpr⟩ := find?_refines href hfind
    have hq : q ∈ algo.processes := List.mem_of_find?_eq_some hsrcfind
    rw [← hqname] at hfind ⊢
    have hself : self ∈ GuardedPlusCal.Process.identities (V := V) q := by
      rw [← hpr.identities_eq]
      exact hself'
    obtain ⟨ninits, hsplit, -, -⟩ := hpr.inits_eq (used q hq ibx)
    rw [hsplit] at hσ'init
    obtain ⟨M, -, hM, -, -⟩ :=
      GuardedPlusCal.InitProc.append (e₁ := GuardedPlusCal.Process.entryLabels q) hσ'init
    rw [← hsplit] at hσ'init
    exact ⟨_, (hPs _ _).mpr ⟨q, hq, self, hself, rfl, hM⟩,
      hrel q hq q' ibx hfind hpr self hself _ _ hM hσ'init⟩
  -- an index naming no instance accounts for nothing
  · intro i hi
    refine hibNeg i λ hcond ↦ ?_
    obtain ⟨σ, hσ⟩ := hcond.1
    exact hi σ hσ
  -- distinct instances get distinct keys, which is `InitKeys.inj` at the two processes they came
  -- from — and both receive, `MailboxUsed` turning each `.some` mailbox into a `ProcessReceives`
  · rintro i j x y hx hy hkey
    obtain ⟨rfl, q, hq, self, rfl, hrecv⟩ := hibRecv i x hx
    obtain ⟨rfl, r, hr, self', rfl, hrecv'⟩ := hibRecv j y hy
    exact hkeys.inj q hq r hr self self' hrecv hrecv' hkey
  · intro i x hx
    rw [(hibRecv i x hx).1]
  · exact λ _ _ ↦ rfl
  · rintro i x hx
    obtain ⟨rfl, q, hq, self, rfl, hrecv⟩ := hibRecv i x hx
    exact hkeys.declared q hq self hrecv
  · intro k
    cases F.lookup k <;> rfl

end Guarded2Network

end
