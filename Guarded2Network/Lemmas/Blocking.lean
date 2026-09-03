module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Algorithm

@[expose] public section

/-!
  The blocking half of the algorithm-level refinement.

  A blocking configuration of the compiled algorithm is one where every process is wedged: every
  scheduled code block blocks on a guard, and every `.rx` thread's channel is empty. The last
  conjunct is what makes the transfer to the source exact. A compiled `await Len(inbox) > k` blocks
  when `inbox` is short, which on its own says nothing about the source's channel — a message could
  still be sitting in `mailbox` waiting to be relayed. But a *blocking* configuration has that
  channel empty too (`relayBlocking`), so the invariant `F_s(c) = inbox ++ F_t(c)` collapses to
  `F_s(c) = ⟨⟩`, and the source `receive` blocks for the same reason.

  This is why `T_rx` is essential: a compiler that drops it has `relayBlocking` vacuously true, so it
  can produce a wedged configuration with `F_t(mailbox) ≠ ⟨⟩` — code deadlocked on
  `await Len(inbox) > 0` while a message rots in `mailbox` — which the source, reading the channel
  directly, would have consumed. No matched source blocking run, so `blocking` is unprovable.
-/

namespace Guarded2Network

universe u

open ComputableTLAPlus (ExprSemantics Memory OperatorEnv Model)
open GuardedPlusCal (Algebra AlgState ChanKey EvalStep FIFOs Instances LocalState ProcConfig
  ProcState Trace)

variable {V : Type u} [ExprSemantics V] [SeqBuiltins V] {ι : Type u} {Ξ : OperatorEnv} {Ω : Model V}

variable {mbox : String → String → Mailbox} {c₀ : String → ComputableGuardedPlusCal.Ref}
  {pref : ChanKey V → List V} {algo : ComputableGuardedPlusCal.Algorithm}
  {algo' : ComputableNetworkPlusCal.Algorithm} {name : String} {v : V}

omit [SeqBuiltins V] in
/-- **One process's blocking, transferred.** A compiled process wedged at a related state — every
scheduled block blocked and its receiving channel drained — is matched by the source process wedged,
or by the source aborting.

The channel-drained conjunct (`hdrain`) is what `procBlocking`'s `relayBlocking` supplies and what
makes the receive-guard case exact: with `F_t(c) = ⟨⟩` the invariant gives `F_s(c) = inbox`, and a
compiled `await Len(inbox) > k` that blocks means the source's queue is emptied after its `k`
receives. -/
theorem procBlockTransfer (hΞ : Ξ.WellScoped)
    (href : ∀ pref : ChanKey V → List V, ProcessesRefine (V := V) Ξ Ω mbox c₀ pref algo algo')
    (used : MailboxUsed mbox algo)
    {Ps Qs : Instances (String × V) V} {F₁ F₂ : FIFOs V}
    (hrel : (⟨Ps, F₁⟩ : AlgState (String × V) V) ≋[Ξ, Ω, procMailbox algo'] ⟨Qs, F₂⟩)
    {p : String × V} {σₛ σₜ : ProcState V} {ε : Trace V}
    (hS : Ps p = .some σₛ) (hin : Qs p = .some σₜ)
    (hblk : (⟨⟨σₜ, F₂⟩, ε⟩ : ProcConfig V × Trace V) ∈
      (NetworkPlusCal.Algorithm.algebra Ξ Ω algo' p).procBlocking p.2) :
    (⟨⟨σₛ, F₁⟩, ε⟩ : ProcConfig V × Trace V) ∈
      (GuardedPlusCal.Algorithm.algebra Ξ Ω algo p).procBlocking p.2 ∨
    (⟨⟨σₛ, F₁⟩, ε⟩ : ProcConfig V × Trace V) ∈
      (GuardedPlusCal.Algorithm.algebra Ξ Ω algo p).procAborting p.2 := by
  obtain ⟨name, v⟩ := p
  obtain ⟨M₁, L₁⟩ := σₛ
  obtain ⟨M₂, L₂⟩ := σₜ
  obtain ⟨ib, pref, hmatch, -, -, hkey, -, -, hfifo⟩ := hrel
  have hproc : procRelatesTo Ξ Ω (procMailbox algo' (name, v)) (ib (name, v))
      (⟨M₁, L₁⟩ : ProcState V) ⟨M₂, L₂⟩ := by
    have hm := hmatch (name, v); rwa [hS, hin] at hm
  cases hfind : algo'.processes.find? (·.name == name) with
  | none =>
    exfalso
    simp only [NetworkPlusCal.Algorithm.algebra, hfind, Option.elim_none,
      GuardedPlusCal.CodeTable.procBlocking, Set.mem_setOf_eq] at hblk
    obtain ⟨hne, -⟩ := hblk
    simp only [Set.inter_empty, Set.not_nonempty_empty] at hne
  | some p' =>
    rw [tgt_algebra_table hfind] at hblk
    obtain ⟨hne, hbl, hrelay, hself0⟩ := hblk
    obtain ⟨psrc, inbox, hfinds, -, hpr⟩ := find?_refines (href pref) hfind
    have hmem : psrc ∈ algo.processes := List.mem_of_find?_eq_some hfinds
    have hused' := used psrc hmem inbox
    have hmbeq : procMailbox algo' (name, v) = mbox psrc.name inbox :=
      procMailbox_eq hfind hpr hused'
    have hself' : Finmap.lookup GuardedPlusCal.selfName M₁ = .some v := by
      rwa [hproc.mem_agree' _ (λ c ib_ hmb ↦
        (procMailbox_inbox_ne_selfName (href λ _ ↦ []) used hmb).symm)]
    have howned : (NetworkPlusCal.Process.codeTable Ξ Ω p').owned =
      (GuardedPlusCal.Process.codeTable Ξ Ω psrc).owned := hpr.ownedLabels_eq
    have sim : (⟨M₁, F₁, .none⟩ : LocalState V) ∼[Ξ, Ω, mbox psrc.name inbox, pref] ⟨M₂, F₂, .none⟩ := by
      rw [← hmbeq]; exact relatesTo_of_procRelatesTo hproc (hkey (name, v)) hfifo .none
    have hib : ∀ (c : ComputableGuardedPlusCal.Ref) (i : String),
        mbox psrc.name inbox = .some (c, i) → i ∉ GuardedPlusCal.Ref.freeVars c := by
      intro c i hmb
      have hrxmb : rxMailbox p' = .some (c, i) := by rwa [hpr.rxMailbox_eq hused']
      obtain ⟨lbl, tτ, hT⟩ := rxMailbox_mem hrxmb
      obtain ⟨-, hnf, hcc', hii'⟩ := hpr.rxThread hT
      rwa [hii', hcc']
    have hdrain : ∀ (c : ComputableGuardedPlusCal.Ref) (i : String)
        (cp : List (ComputableTLAPlus.PathStep V)), mbox psrc.name inbox = .some (c, i) →
        List.Forall₂ (GuardedPlusCal.EvalStep Ξ Ω M₁) c.args cp →
        F₂.lookup (⟨c.name, cp⟩ : ChanKey V) = .some [] := by
      intro c i cp hmb hcp
      have hrxmb : rxMailbox p' = .some (c, i) := by rwa [hpr.rxMailbox_eq hused']
      obtain ⟨lbl, tτ, hT⟩ := rxMailbox_mem hrxmb
      have hinf : i ∉ GuardedPlusCal.Ref.freeVars c := hib c i hmb
      obtain ⟨cp', hcp', hlk'⟩ := hrelay _ hT c lbl tτ i rfl
      have hagree : ∀ y ∈ GuardedPlusCal.Ref.freeVars c,
          Finmap.lookup y M₁ = Finmap.lookup y M₂ := by
        intro y hy
        refine hproc.mem_agree' y (λ c' i' hmb' hyi' ↦ hinf ?_)
        rw [hmbeq, hmb] at hmb'
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hmb'
        exact hyi' ▸ hy
      obtain rfl : cp = cp' :=
        GuardedPlusCal.EvalStep.path_inj ((Ref.EvalArgs.congr_of_agree hΞ hagree).mp hcp) hcp'
      exact hlk'
    have hsbr := hpr.srcBranchesRefine (mbox := mbox psrc.name inbox)
    -- either some scheduled owned label has a source branch that aborts, or all block
    by_cases habt : ∃ l ∈ L₁, ∃ Br ∈ srcBranchesAt psrc l,
        (⟨(⟨M₁, F₁, .none⟩ : LocalState V), ε⟩ : LocalState V × Trace V) ∈
          GuardedPlusCal.AtomicBranch.aborting Ξ Ω Br
    · right
      obtain ⟨l, hl, Br, hBr, hab⟩ := habt
      rw [src_algebra_table hfinds]
      exact ⟨l, hl, src_aborting_le hBr hab, hself'⟩
    · left
      rw [src_algebra_table hfinds]
      refine ⟨?_, ?_, Set.mem_univ _, hself'⟩
      · obtain ⟨l₀, hl₀⟩ := hne
        exact ⟨l₀, hproc.1 ▸ hl₀.1, howned ▸ hl₀.2⟩
      · intro l hlL hlO
        refine src_blocking_le (λ Br hBr ↦ ?_)
        obtain ⟨Br', hBr', href'⟩ := hsbr l Br hBr
        have htgt : (⟨(⟨M₂, F₂, .none⟩ : LocalState V), ε⟩ : LocalState V × Trace V) ∈
            NetworkPlusCal.AtomicBranch.blocking Ξ Ω Br' :=
          tgt_blocking_le (hbl l (hproc.1 ▸ hlL) (howned ▸ hlO)) hBr'
        rcases href'.blockTransfer hib sim hdrain htgt with hb | ha
        · exact hb
        · exact (habt ⟨l, hlL, Br, hBr, ha⟩).elim

omit [SeqBuiltins V] in
/-- **One process's doneness, transferred.** A compiled process that has reached a sentinel on
every thread is matched by its source, which has the same scheduled label set (`L_s = L_t`) over the
same owned labels (`ProcessRefines.ownedLabels_eq`). A name resolving to no process owns nothing on
either side, so the doneness is vacuous there. -/
theorem procDoneTransfer
    (href : ∀ pref : ChanKey V → List V, ProcessesRefine (V := V) Ξ Ω mbox c₀ pref algo algo')
    {Ps Qs : Instances (String × V) V} {F₁ F₂ : FIFOs V}
    (hrel : (⟨Ps, F₁⟩ : AlgState (String × V) V) ≋[Ξ, Ω, procMailbox algo'] ⟨Qs, F₂⟩)
    {p : String × V} {σₛ σₜ : ProcState V}
    (hS : Ps p = .some σₛ) (hin : Qs p = .some σₜ)
    (hdone : σₜ ∈ (NetworkPlusCal.Algorithm.algebra Ξ Ω algo' p).procDone) :
    σₛ ∈ (GuardedPlusCal.Algorithm.algebra Ξ Ω algo p).procDone := by
  obtain ⟨name, v⟩ := p
  obtain ⟨ib, hfwd⟩ := hrel.forward
  obtain ⟨σₜ', hin', hproc⟩ := hfwd (name, v) σₛ hS
  obtain rfl : σₜ = σₜ' := Option.some.inj (hin.symm.trans hin')
  obtain ⟨M₁, L₁⟩ := σₛ
  obtain ⟨M₂, L₂⟩ := σₜ
  obtain ⟨hL, -⟩ := hproc
  simp only [GuardedPlusCal.CodeTable.procDone, Set.mem_setOf_eq] at hdone ⊢
  rw [hL] at hdone
  have hpred : ∀ (a : ComputableGuardedPlusCal.Process) (b : ComputableNetworkPlusCal.Process),
      (∃ inbox, ProcessRefines (V := V) Ξ Ω (mbox a.name inbox) (c₀ a.name) inbox (λ _ ↦ []) a b) →
      (a.name == name) = (b.name == name) := by
    rintro a b ⟨_, hpr⟩
    rw [hpr.name_eq]
  cases hfind : algo'.processes.find? (·.name == name) with
  | none =>
    cases hfinds : algo.processes.find? (·.name == name) with
    | none =>
      simp only [GuardedPlusCal.Algorithm.algebra, hfinds, Option.elim_none, Set.inter_empty]
    | some psrc =>
      obtain ⟨b, hb, -⟩ := (href λ _ ↦ []).find?_left hpred hfinds
      rw [hfind] at hb
      exact nomatch hb
  | some p' =>
    obtain ⟨psrc, inbox, hfinds, -, hpr⟩ := find?_refines (href λ _ ↦ []) hfind
    rw [tgt_algebra_table hfind] at hdone
    rw [src_algebra_table hfinds]
    change L₁ ∩ (NetworkPlusCal.Process.codeTable Ξ Ω p').owned = ∅ at hdone
    simp only [GuardedPlusCal.Process.codeTable, NetworkPlusCal.Process.codeTable] at hdone ⊢
    rwa [hpr.ownedLabels_eq] at hdone

omit [SeqBuiltins V] in
/-- **Whole-configuration doneness, transferred.** Every process instance of the compiled algorithm
done implies every instance of the source done — `procDoneTransfer` per instance, since
`procRelatesTo` keeps `L` equal over the same owned labels. This is what restricts the reducing
refinement to `Algebra.terminating` (runs that end done) on both sides. -/
theorem algRelatesTo.isDone_of
    (href : ∀ pref : ChanKey V → List V, ProcessesRefine (V := V) Ξ Ω mbox c₀ pref algo algo')
    {Sₛ Sₜ : AlgState (String × V) V}
    (hrel : Sₛ ≋[Ξ, Ω, procMailbox algo'] Sₜ)
    (hdone : Algebra.isDone (NetworkPlusCal.Algorithm.algebra Ξ Ω algo') Sₜ) :
    Algebra.isDone (GuardedPlusCal.Algorithm.algebra Ξ Ω algo) Sₛ := by
  obtain ⟨Ps, F₁⟩ := Sₛ
  obtain ⟨Qs, F₂⟩ := Sₜ
  intro p σₛ hS
  obtain ⟨ib, hfwd⟩ := hrel.forward
  obtain ⟨σₜ, hin, -⟩ := hfwd p σₛ hS
  exact procDoneTransfer href hrel hS hin (hdone p σₜ hin)

omit [SeqBuiltins V] in
/-- **The immediate blocking half.** `NetworkPlusCal.Algebra.immediateBlock` — the algorithm
deadlocked now — is matched by the source's, or by the source aborting now. Per-instance dispatch:
`procBlockTransfer` for the wedged processes, `procDoneTransfer` for the finished ones, and one
aborting instance is enough to land in the aborting fallback. -/
theorem algRelatesTo.immediateBlock (hΞ : Ξ.WellScoped)
    (href : ∀ pref : ChanKey V → List V, ProcessesRefine (V := V) Ξ Ω mbox c₀ pref algo algo')
    (used : MailboxUsed mbox algo) :
    StrongRefinement.Blocking (algRelatesTo (V := V) Ξ Ω (procMailbox algo'))
      (instTrace (V := V)).Rτ
      (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).immediateBlock
      (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).aborting
      (NetworkPlusCal.Algorithm.algebra Ξ Ω algo').immediateBlock := by
  rintro ⟨Qs, F₂⟩ ε ⟨Ps, F₁⟩ hrel ⟨⟨p₀, σ₀, hp₀, hp₀blk⟩, hall⟩
  obtain ⟨ib, pref, hmatch, habsent, hinj, hkey, hoff, hpresent, hfifo⟩ := hrel
  have hrel' : (⟨Ps, F₁⟩ : AlgState (String × V) V) ≋[Ξ, Ω, procMailbox algo'] ⟨Qs, F₂⟩ :=
    ⟨ib, pref, hmatch, habsent, hinj, hkey, hoff, hpresent, hfifo⟩
  -- both sides hold a state at exactly the same instances
  have hpair : ∀ p σₜ, Qs p = .some σₜ → ∃ σₛ, Ps p = .some σₛ := by
    intro p σₜ hq
    have hm := hmatch p
    rw [hq] at hm
    rcases Option.eq_none_or_eq_some (Ps p) with hp | ⟨σₛ, hp⟩
    · rw [hp] at hm; exact hm.elim
    · exact ⟨σₛ, hp⟩
  have hpair' : ∀ p σₛ, Ps p = .some σₛ → ∃ σₜ, Qs p = .some σₜ := by
    intro p σₛ hp
    have hm := hmatch p
    rw [hp] at hm
    rcases Option.eq_none_or_eq_some (Qs p) with hq | ⟨σₜ, hq⟩
    · rw [hq] at hm; exact hm.elim
    · exact ⟨σₜ, hq⟩
  -- either some source instance aborts, or every source instance blocks-or-is-done
  by_cases habort : ∃ q σₛ, Ps q = .some σₛ ∧
      (⟨⟨σₛ, F₁⟩, ε⟩ : ProcConfig V × Trace V) ∈
        (GuardedPlusCal.Algorithm.algebra Ξ Ω algo q).procAborting q.2
  · obtain ⟨q, σₛ, hq, habrt⟩ := habort
    exact .inr ⟨ε, by trace_pfx, Relation.star.le_lcomp₁ ⟨q, σₛ, hq, habrt⟩⟩
  · refine .inl ⟨ε, by trace_rel, ?_, ?_⟩
    · -- at least one source instance is genuinely blocked: `p₀`'s target is
      obtain ⟨σₛ₀, hσₛ₀⟩ := hpair p₀ σ₀ hp₀
      rcases procBlockTransfer hΞ href used hrel' hσₛ₀ hp₀ hp₀blk with hb | ha
      · exact ⟨p₀, σₛ₀, hσₛ₀, hb⟩
      · exact (habort ⟨p₀, σₛ₀, hσₛ₀, ha⟩).elim
    · intro q σₛ hq
      obtain ⟨σₜ, hqt⟩ := hpair' q σₛ hq
      rcases hall q σₜ hqt with hbt | hdt
      · rcases procBlockTransfer hΞ href used hrel' hq hqt hbt with hb | ha
        · exact .inl hb
        · exact (habort ⟨q, σₛ, hq, ha⟩).elim
      · exact .inr (procDoneTransfer href hrel' hq hqt hdt)

omit [SeqBuiltins V] in
/-- **The whole blocking semantics.** `NetworkPlusCal.Algebra.blocking` is `step* ∘ᵣ₁
immediateBlock`, so this is `Blocking.starStutter` at that — the immediate half above, lifted over
the run that precedes it by the same per-step `Terminating` the reducing and aborting halves use.
Any `T_rx` relay steps in that prefix stutter on the source side. -/
theorem algRelatesTo.blocking (hΞ : Ξ.WellScoped) [DecidableEq V]
    (href : ∀ pref : ChanKey V → List V, ProcessesRefine (V := V) Ξ Ω mbox c₀ pref algo algo')
    (used : MailboxUsed mbox algo) (fresh : AlgorithmFresh mbox c₀ algo) :
    StrongRefinement.Blocking (algRelatesTo (V := V) Ξ Ω (procMailbox algo'))
      (instTrace (V := V)).Rτ (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).blocking
      (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).aborting
      (NetworkPlusCal.Algorithm.algebra Ξ Ω algo').blocking :=
  StrongRefinement.Blocking.starStutter (algRelatesTo.terminating hΞ href used fresh)
    (algRelatesTo.immediateBlock hΞ href used)

omit [SeqBuiltins V] in
/-- **The terminating semantics, the paper's `⟦A⟧⁺`.** `terminating_reducing` cut down to runs that
end in a done configuration on both sides. The target restriction is free (`Terminating.Mono`); the
source restriction rides on `algRelatesTo.isDone_of`, since a shorter source set is otherwise harder
to land in. -/
theorem algRelatesTo.terminating_done (hΞ : Ξ.WellScoped) [DecidableEq V]
    (href : ∀ pref : ChanKey V → List V, ProcessesRefine (V := V) Ξ Ω mbox c₀ pref algo algo')
    (used : MailboxUsed mbox algo) (fresh : AlgorithmFresh mbox c₀ algo) :
    StrongRefinement.Terminating (algRelatesTo (V := V) Ξ Ω (procMailbox algo'))
      (algRelatesTo (V := V) Ξ Ω (procMailbox algo'))
      (instTrace (V := V)).Rτ
      (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).terminating
      (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).aborting
      (NetworkPlusCal.Algorithm.algebra Ξ Ω algo').terminating :=
  StrongRefinement.Terminating.restrictEnd (algRelatesTo.terminating_reducing hΞ href used fresh)
    (λ _ _ hR hdone ↦ algRelatesTo.isDone_of href hR hdone)

omit [SeqBuiltins V] in
/-- **The algorithm-level refinement, whole.** All four components at the closed forms
`Algebra.terminating`/`.aborting`/`.diverging`/`.blocking`, against one state relation.

`href`/`used`/`fresh` are established from a compiled algorithm by `Algorithm.toNetwork_spec`
and the front end, and `algRelatesTo` at the initial states by `Algorithm.init`; the refinement
argument asks for nothing beyond those. -/
theorem algRelatesTo.refines (hΞ : Ξ.WellScoped) [DecidableEq V]
    (href : ∀ pref : ChanKey V → List V, ProcessesRefine (V := V) Ξ Ω mbox c₀ pref algo algo')
    (used : MailboxUsed mbox algo) (fresh : AlgorithmFresh mbox c₀ algo) :
    StrongRefinement (algRelatesTo (V := V) Ξ Ω (procMailbox algo'))
      (instTrace (V := V)).Rτ
      (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).terminating
      (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).aborting
      (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).diverging
      (NetworkPlusCal.Algorithm.algebra Ξ Ω algo').terminating
      (NetworkPlusCal.Algorithm.algebra Ξ Ω algo').aborting
      (NetworkPlusCal.Algorithm.algebra Ξ Ω algo').diverging
      (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).blocking
      (NetworkPlusCal.Algorithm.algebra Ξ Ω algo').blocking where
  terminating := algRelatesTo.terminating_done hΞ href used fresh
  aborting := algRelatesTo.aborting hΞ href used fresh
  diverging := algRelatesTo.diverging hΞ href used fresh
  blocking := algRelatesTo.blocking hΞ href used fresh

open Std.Do in
/-- **The pass is correct.** Compiling an algorithm yields one whose algebra refines the source's,
under `algRelatesTo` at the mailbox the compiled algorithm itself determines.

Everything in this development meets here. `Algorithm.toNetwork_spec` is the syntactic half, the
four walks; `algRelatesTo.refines` is the refinement argument, `Terminating`/`Aborting`/`Diverging`/
`Blocking` at the four closed forms. `triple_forall` is the joint: `BranchesRefine` is needed at
every prefix function and the spec supplies one per instantiation.

The two front-end hypotheses are not the pass's. `AlgorithmFresh` is the syntactic conditions on the
source program and the generated `inbox`; `MailboxUsed` says a declared mailbox is one its process
receives on (`checkReceiveChannels`).

Relating `Algorithm.init`'s initial states under `algRelatesTo` is a separate statement, and
`Algorithm.toNetwork_spec` reports `globalState` because that is what it is stated against. -/
theorem Algorithm.toNetwork_refines (hΞ : Ξ.WellScoped) [DecidableEq V] {mbox : String → String → Mailbox}
  {c₀ : String → ComputableGuardedPlusCal.Ref} {algo : ComputableGuardedPlusCal.Algorithm}
  (fresh : AlgorithmFresh mbox c₀ algo) (used : MailboxUsed mbox algo) :
    ⦃⌜True⌝⦄
    ComputableGuardedPlusCal.Algorithm.toNetwork (m := G2NM) algo
    ⦃⇓? algo' _ => ⌜algo'.globalState = algo.globalState ∧
      StrongRefinement (algRelatesTo (V := V) Ξ Ω (procMailbox algo'))
        (instTrace (V := V)).Rτ
        (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).terminating
        (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).aborting
        (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).diverging
        (NetworkPlusCal.Algorithm.algebra Ξ Ω algo').terminating
        (NetworkPlusCal.Algorithm.algebra Ξ Ω algo').aborting
        (NetworkPlusCal.Algorithm.algebra Ξ Ω algo').diverging
        (GuardedPlusCal.Algorithm.algebra Ξ Ω algo).blocking
        (NetworkPlusCal.Algorithm.algebra Ξ Ω algo').blocking⌝⦄ := by
  refine triple_forall (ι := ChanKey V → List V)
    (λ pref ↦ Algorithm.toNetwork_spec (V := V) (Ξ := Ξ) (Ω := Ω) (pref := pref) hΞ fresh) ?_
  intro algo' h
  exact ⟨(h λ _ ↦ []).1,
    algRelatesTo.refines hΞ (λ pref ↦ (h pref).2) used fresh⟩

end Guarded2Network

end
