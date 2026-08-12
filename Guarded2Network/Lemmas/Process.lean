module

meta import CustomPrelude
public import Guarded2Network.Lemmas.AtomicBlock
public import Guarded2Network.Lemmas.Thread
public import Guarded2Network.Lemmas.Locality
import all Guarded2Network.Lemmas.AtomicBlock
import all Guarded2Network.PlusCal

@[expose] public section

/-!
  From one compiled block to one process step.

  `Lemmas/AtomicBlock.lean` leaves a compiled block as `List.Forall₂ BranchRefines` over its
  branches. The process layer schedules a *label*, and the block that label names denotes the union
  of its branches (`GuardedPlusCal.Process.codeTable`), so what the process layer needs is that
  union simulated — some target branch's step answered by *some* source branch's step. That is
  `blockRefines_step` below, and it is nothing more than `BranchRefines.refines.terminating` applied
  at the branch `List.Forall₂.exists_left` picks out.

  The other half of the same bridge runs the other way: `relatesTo_of_procRelatesTo` turns the
  algorithm-level invariant, once a process has been picked, into the local `relatesTo` the block
  layer is stated against, and `procRelatesTo_of_relatesTo` turns the block's result back. Both
  halves need `pref` to be a parameter of `relatesTo` — that is what it is for
  (`Lemmas/Relation.lean`).

  The indexed/flat boundary is crossed here too. `CodeTable.reducing` is stated at the indexed
  `LocalState`, every refinement lemma at the flat `LocalState'`, and
  `GuardedPlusCal.LocalState.sem_glue₃`/`.abort_glue₂` are what say those are the same fact.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Memory PathStep)
open GuardedPlusCal (AlgState Block ChanKey FIFOs LocalState LocalState' ProcState Trace)

variable {V : Type} [ExprSemantics V]

/-- **`AtomicBranch.reducing'_evalArgs` against the freshness bundle the block level already
carries.** `BranchesFresh` quantifies its precondition clause over `preconditionList`, the locality
argument over the `Block.toList` of a precondition that is present; the two are the same list, and
saying so is the whole of this lemma. -/
theorem BranchesFresh.evalArgs {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
    {Br : ComputableGuardedPlusCal.AtomicBranch}
    (hf : BranchesFresh (.some (c₀, inbox)) c₀ inbox Br)
    {σ σ' : LocalState' V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
      GuardedPlusCal.AtomicBranch.reducing' Br)
    {path : List (PathStep V)} :
    Ref.EvalArgs σ.mem c₀ path ↔ Ref.EvalArgs σ'.mem c₀ path := by
  refine AtomicBranch.reducing'_evalArgs rfl (λ B' hB' S hS ↦ hf.gfresh S ?_) hf.afresh hf.alast step
  rw [preconditionList, hB']
  exact hS

/-- **Picking a process projects the invariant.** One instance's `procRelatesTo`, together with the
one FIFO equation `algRelatesTo` carries, *is* `relatesTo` on that instance's local state.

This is what the whole `pref` parameter exists for. `relatesTo` reads `pref` at every key but this
instance's own channel, where it uses the instance's own `inbox` instead — and that is exactly the
clause `ib` already pins (`hkey`). So the projection is a repackaging, with no side condition and
nothing to choose.

Stated against `algRelatesTo`'s witnesses rather than against `algRelatesTo` itself: a caller has
already destructured it to get at the instance, and re-assembling it here would only have to be
undone. -/
theorem relatesTo_of_procRelatesTo {mb : Mailbox} {rx : Set String} {pref : ChanKey V → List V}
    {ib : Option (InboxState V)} {M₁ M₂ : Memory V} {L₁ L₂ : Set String} {F₁ F₂ : FIFOs V}
    (h : procRelatesTo mb rx ib ⟨M₁, L₁⟩ ⟨M₂, L₂⟩)
    (hkey : ∀ x, ib = .some x → pref x.key = x.contents)
    (hfifo : ∀ k : ChanKey V, F₁.lookup k = (pref k ++ ·) <$> F₂.lookup k)
    (l : Option String) :
    (⟨M₁, F₁, l⟩ : LocalState' V) ∼[mb, pref] ⟨M₂, F₂, l⟩ := by
  obtain ⟨-, -, hmatch⟩ := h
  match mb, ib with
  | .none, .none => exact relatesTo.none_intro rfl hmatch hfifo
  | .some (c, inbox), .some ibp =>
    obtain ⟨hmem, ⟨sv, hsv, hseq⟩, cpath, hpath, hibkey⟩ := hmatch
    refine relatesTo.chan_intro rfl hmem hpath hsv hseq (λ k _ ↦ hfifo k) ?_
    rw [LocalState'.fifos_mk, LocalState'.fifos_mk, ← hibkey, hfifo ibp.key, hkey ibp rfl]
  | .none, .some _ => exact hmatch.elim
  | .some _, .none => exact hmatch.elim

/-- **And putting the process back.** The block layer hands back `relatesTo` at the post-state; this
turns it into the `procRelatesTo` and the two FIFO clauses the algorithm-level witness is rebuilt
from, with the new `InboxState` read off `relatesTo`'s own existential.

`hstable` is where `Lemmas/Locality.lean` is spent, and it is a *soundness* hypothesis rather than a
convenience. `relatesTo`'s post-state names some key its own `cpath` resolves to; without knowing
that the old key still resolves, nothing forces the two to agree, and an instance whose key moved
would leave its old key's drained prefix accounted to nobody — `algRelatesTo` would then be false,
not merely unprovable. With it, `Ref.EvalArgs.inj` pins the new key to the old, which is what makes
`hsame` — and through it every key-phrased clause of `algRelatesTo` — survive the step.

The label set is handed in rather than derived: which labels the source schedules next is the
process layer's business, and all this needs of it is that the `.rx` labels stay disjoint from it. -/
theorem procRelatesTo_of_relatesTo {mb : Mailbox} {rx : Set String} {pref : ChanKey V → List V}
    {ib : Option (InboxState V)} {M₁ M₂ M₁' M₂' : Memory V} {L₁ L₂ L₁' : Set String}
    {F₁' F₂' : FIFOs V} {l : Option String}
    (hold : procRelatesTo mb rx ib ⟨M₁, L₁⟩ ⟨M₂, L₂⟩)
    (hstable : ∀ (c : ComputableGuardedPlusCal.Ref) (inbox : String), mb = .some (c, inbox) →
      ∀ path : List (PathStep V), Ref.EvalArgs M₁ c path → Ref.EvalArgs M₁' c path)
    (hrel : (⟨M₁', F₁', l⟩ : LocalState' V) ∼[mb, pref] ⟨M₂', F₂', l⟩)
    (hdisj : Disjoint L₁' rx) :
    ∃ ib' : Option (InboxState V),
      procRelatesTo mb rx ib' ⟨M₁', L₁'⟩ ⟨M₂', L₁' ∪ rx⟩ ∧
      (∀ x, ib = .some x → ∃ ws, ib' = .some ⟨x.key, ws⟩) ∧
      (ib = .none → ib' = .none) ∧
      (∀ k : ChanKey V, (∀ y, ib' = .some y → y.key ≠ k) →
        F₁'.lookup k = (pref k ++ ·) <$> F₂'.lookup k) ∧
      ∀ y, ib' = .some y → F₁'.lookup y.key = (y.contents ++ ·) <$> F₂'.lookup y.key := by
  obtain ⟨-, -, hmatch⟩ := hold
  match mb, ib with
  | .none, .none =>
    refine ⟨.none, ⟨rfl, hdisj, hrel.mem_eq⟩, ?_, λ _ ↦ rfl, λ k _ ↦ hrel.none_fifo_split k, ?_⟩
    · intro _ hx
      contradiction
    · intro _ hy
      contradiction
  | .some (c, inbox), .some ibp =>
    obtain ⟨-, -, cpath₀, hpath₀, hkey₀⟩ := hmatch
    obtain ⟨cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩ := hrel.inbox_seq
    obtain rfl : cpath = cpath₀ := Ref.EvalArgs.inj hpath (hstable c inbox rfl cpath₀ hpath₀)
    refine ⟨.some ⟨ibp.key, vs⟩,
      ⟨rfl, hdisj, hrel.mem_agree, ⟨sv, hinbox, hseq⟩, cpath, hpath, hkey₀⟩,
      ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain rfl := Option.some.inj hx
      exact ⟨vs, rfl⟩
    · intro hx
      contradiction
    · intro k hk
      refine hoff k (λ hkc ↦ hk ⟨ibp.key, vs⟩ rfl ?_)
      rw [hkey₀]
      exact hkc.symm
    · intro y hy
      obtain rfl := Option.some.inj hy
      rw [hkey₀]
      exact hsplit
  | .none, .some _ => exact hmatch.elim
  | .some _, .none => exact hmatch.elim

/-- **A compiled block's step is answered by the source block's.** A block denotes the union of its
branches, so a target step is a step of *some* compiled branch; `List.Forall₂.exists_left` names the
source branch it was compiled from, and that branch's own refinement answers it.

The conclusion is `Terminating`'s two disjuncts with the branch existentially quantified inside
each — which is the shape the process layer wants, since a source process step is likewise "some
branch of the block at the scheduled label". -/
theorem blockRefines_step {mbox : Mailbox} {pref : ChanKey V → List V}
    {brs : List ComputableGuardedPlusCal.AtomicBranch}
    {brs' : List ComputableNetworkPlusCal.AtomicBranch}
    (h : BranchesRefine (V := V) mbox pref brs brs')
    {σₛ σₜ σₜ' : LocalState' V} {ε : Trace V} (sim : σₛ ∼[mbox, pref] σₜ)
    {Br' : ComputableNetworkPlusCal.AtomicBranch} (hmem : Br' ∈ brs')
    (step : (⟨σₜ, ε, σₜ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
      NetworkPlusCal.AtomicBranch.reducing' Br') :
    (∃ σₛ' ε', σₛ' ∼[mbox, pref] σₜ' ∧ (instTrace (V := V)).Rτ ε' ε ∧
        ∃ Br ∈ brs, (⟨σₛ, ε', σₛ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
          GuardedPlusCal.AtomicBranch.reducing' Br) ∨
      (∃ ε', ε' ≼[(instTrace (V := V)).Rτ] ε ∧
        ∃ Br ∈ brs, (⟨σₛ, ε'⟩ : LocalState' V × Trace V) ∈
          GuardedPlusCal.AtomicBranch.aborting' Br) := by
  obtain ⟨Br, hBr, href⟩ := h _ hmem
  rcases href.refines.terminating σₜ σₜ' ε σₛ sim step with
    ⟨σₛ', ε', hrel, hτ, hstep⟩ | ⟨ε', hpfx, habort⟩
  · exact .inl ⟨σₛ', ε', hrel, hτ, Br, hBr, hstep⟩
  · exact .inr ⟨ε', hpfx, Br, hBr, habort⟩

/-- `blockRefines_step` at the *indexed* encoding the process layer states its steps in.
`GuardedPlusCal.LocalState.sem_glue₃`/`.abort_glue₂` and their `NetworkPlusCal` twins are the whole
of the difference; nothing about the refinement changes.

The target's post-state is `.done M₂' F₂' l'`, so the flat one carries `some l'` — and
`relatesTo.label_eq` then hands the source the *same* `l'`, which is what makes the two processes
schedule the same label next. That agreement is the reason `BranchRefines` carries `last_eq` at
all. -/
theorem blockRefines_step_indexed {mbox : Mailbox} {pref : ChanKey V → List V}
    {brs : List ComputableGuardedPlusCal.AtomicBranch}
    {brs' : List ComputableNetworkPlusCal.AtomicBranch}
    (h : BranchesRefine (V := V) mbox pref brs brs')
    {M₁ M₂ M₂' : Memory V} {F₁ F₂ F₂' : FIFOs V} {l' : String} {ε : Trace V}
    (sim : (⟨M₁, F₁, none⟩ : LocalState' V) ∼[mbox, pref] ⟨M₂, F₂, none⟩)
    {Br' : ComputableNetworkPlusCal.AtomicBranch} (hmem : Br' ∈ brs')
    (step : (⟨.running M₂ F₂, ε, .done M₂' F₂' l'⟩ :
      LocalState V false × Trace V × LocalState V true) ∈
        NetworkPlusCal.AtomicBranch.reducing Br') :
    (∃ M₁' F₁' ε', (⟨M₁', F₁', some l'⟩ : LocalState' V) ∼[mbox, pref] ⟨M₂', F₂', some l'⟩ ∧
        (instTrace (V := V)).Rτ ε' ε ∧
        ∃ Br ∈ brs, (⟨.running M₁ F₁, ε', .done M₁' F₁' l'⟩ :
          LocalState V false × Trace V × LocalState V true) ∈
          GuardedPlusCal.AtomicBranch.reducing Br) ∨
      (∃ ε', ε' ≼[(instTrace (V := V)).Rτ] ε ∧
        ∃ Br ∈ brs, (⟨.running M₁ F₁, ε'⟩ : LocalState V false × Trace V) ∈
          GuardedPlusCal.AtomicBranch.aborting Br) := by
  rcases blockRefines_step h sim hmem (NetworkPlusCal.LocalState.sem_glue₃.mp step) with
    ⟨⟨M₁', F₁', l₁⟩, ε', hrel, hτ, Br, hBr, hstep⟩ | ⟨ε', hpfx, Br, hBr, habort⟩
  · -- the source ends at the label the target ended at, which is `relatesTo`'s own first clause
    obtain rfl : l₁ = some l' := hrel.label_eq
    exact .inl ⟨M₁', F₁', ε', hrel, hτ, Br, hBr, GuardedPlusCal.LocalState.sem_glue₃.mpr hstep⟩
  · exact .inr ⟨ε', hpfx, Br, hBr, GuardedPlusCal.LocalState.abort_glue₂.mpr habort⟩

/-- **And where a compiled block goes wrong, the source block does too.** `blockRefines_step`'s
twin, and simpler for the same reason `Aborting` is simpler than `Terminating`: an abort has no
post-state, so there is nothing to relate afterwards and no witness to rebuild. -/
theorem blockRefines_abort {mbox : Mailbox} {pref : ChanKey V → List V}
    {brs : List ComputableGuardedPlusCal.AtomicBranch}
    {brs' : List ComputableNetworkPlusCal.AtomicBranch}
    (h : BranchesRefine (V := V) mbox pref brs brs')
    {σₛ σₜ : LocalState' V} {ε : Trace V} (sim : σₛ ∼[mbox, pref] σₜ)
    {Br' : ComputableNetworkPlusCal.AtomicBranch} (hmem : Br' ∈ brs')
    (habort : (⟨σₜ, ε⟩ : LocalState' V × Trace V) ∈ NetworkPlusCal.AtomicBranch.aborting' Br') :
    ∃ ε', ε' ≼[(instTrace (V := V)).Rτ] ε ∧
      ∃ Br ∈ brs, (⟨σₛ, ε'⟩ : LocalState' V × Trace V) ∈
        GuardedPlusCal.AtomicBranch.aborting' Br := by
  obtain ⟨Br, hBr, href⟩ := h _ hmem
  obtain ⟨ε', hpfx, hsabort⟩ := href.refines.aborting σₜ ε σₛ sim habort
  exact ⟨ε', hpfx, Br, hBr, hsabort⟩

/-- `blockRefines_abort` at the *indexed* encoding, exactly as `blockRefines_step_indexed` is for
`blockRefines_step`. -/
theorem blockRefines_abort_indexed {mbox : Mailbox} {pref : ChanKey V → List V}
    {brs : List ComputableGuardedPlusCal.AtomicBranch}
    {brs' : List ComputableNetworkPlusCal.AtomicBranch}
    (h : BranchesRefine (V := V) mbox pref brs brs')
    {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V} {ε : Trace V}
    (sim : (⟨M₁, F₁, none⟩ : LocalState' V) ∼[mbox, pref] ⟨M₂, F₂, none⟩)
    {Br' : ComputableNetworkPlusCal.AtomicBranch} (hmem : Br' ∈ brs')
    (habort : (⟨.running M₂ F₂, ε⟩ : LocalState V false × Trace V) ∈
      NetworkPlusCal.AtomicBranch.aborting Br') :
    ∃ ε', ε' ≼[(instTrace (V := V)).Rτ] ε ∧
      ∃ Br ∈ brs, (⟨.running M₁ F₁, ε'⟩ : LocalState V false × Trace V) ∈
        GuardedPlusCal.AtomicBranch.aborting Br := by
  obtain ⟨ε', hpfx, Br, hBr, hsabort⟩ :=
    blockRefines_abort h sim hmem (NetworkPlusCal.LocalState.abort_glue₂.mp habort)
  exact ⟨ε', hpfx, Br, hBr, GuardedPlusCal.LocalState.abort_glue₂.mpr hsabort⟩

/-- **The block half of the algorithm-level per-step obligation.** One instance takes a step of a
compiled *code* thread's block; the source instance answers with a step of the block it was compiled
from, and the whole `algRelatesTo` witness is rebuilt around it.

The two disjuncts are `Terminating`'s, with the branch existentially quantified inside each and the
new state sets spelled out — the same shape `rx_step` states its (much shorter) conclusion in, and
what the process layer needs to assemble `Algebra.step`.

Everything is one instance's business, which is what makes the proof go: `p`'s own step is
`blockRefines_step_indexed`, and every *other* instance's clause survives because its `ib` entry and
its key are untouched. The clauses phrased over keys — `keys_inj`, and `pref` being empty where
nobody receives — need that this instance's key did not move either, which is `hstable`'s job inside
`procRelatesTo_of_relatesTo` and ultimately `Lemmas/Locality.lean`'s.

`hlabel`/`hlabel'` are the syntactic side of the same split. A code thread's block is scheduled at a
source label and leaves at another, never at an `.rx` thread's; without that the target's new label
set would not be the source's plus `rx p`, and the two would stop scheduling in step. Both are facts
about the compiled process, discharged where the threads are known. -/
theorem algRelatesTo.block_step {ι : Type} [DecidableEq ι] {mb : ι → Mailbox} {rx : ι → Set String}
    {Ps Qs Qs' : Set (ι × ProcState V)} {F₁ F₂ F₂' : FIFOs V}
    {p : ι} {label label' : String} {M₁ M₂ M₂' : Memory V} {L₁ L₂ : Set String} {ε : Trace V}
    {brs : List ComputableGuardedPlusCal.AtomicBranch}
    {brs' : List ComputableNetworkPlusCal.AtomicBranch}
    (href : ∀ pref : ChanKey V → List V,
      BranchesRefine (V := V) (mb p) pref brs brs')
    (fresh : ∀ Br ∈ brs, ∀ c inbox, mb p = .some (c, inbox) →
      BranchesFresh (.some (c, inbox)) c inbox Br)
    (h : (⟨Ps, F₁⟩ : AlgState ι V) ≋[mb, rx] ⟨Qs, F₂⟩)
    (hS : (⟨p, ⟨M₁, L₁⟩⟩ : ι × ProcState V) ∈ Ps)
    (hin : (⟨p, ⟨M₂, L₂⟩⟩ : ι × ProcState V) ∈ Qs)
    (hlabel : label ∈ L₁) (hlabel' : label' ∉ rx p)
    {Br' : ComputableNetworkPlusCal.AtomicBranch} (hmem : Br' ∈ brs')
    (hstep : (⟨.running M₂ F₂, ε, .done M₂' F₂' label'⟩ :
      LocalState V false × Trace V × LocalState V true) ∈
        NetworkPlusCal.AtomicBranch.reducing Br')
    (hQs : Qs' = insert (⟨p, ⟨M₂', insert label' (L₂ \ {label})⟩⟩ : ι × ProcState V)
      (Qs \ {⟨p, ⟨M₂, L₂⟩⟩})) :
    (∃ M₁' F₁' ε',
        (⟨insert (⟨p, ⟨M₁', insert label' (L₁ \ {label})⟩⟩ : ι × ProcState V)
            (Ps \ {⟨p, ⟨M₁, L₁⟩⟩}), F₁'⟩ : AlgState ι V) ≋[mb, rx] ⟨Qs', F₂'⟩ ∧
        (instTrace (V := V)).Rτ ε' ε ∧
        ∃ Br ∈ brs, (⟨.running M₁ F₁, ε', .done M₁' F₁' label'⟩ :
          LocalState V false × Trace V × LocalState V true) ∈
          GuardedPlusCal.AtomicBranch.reducing Br) ∨
      (∃ ε', ε' ≼[(instTrace (V := V)).Rτ] ε ∧
        ∃ Br ∈ brs, (⟨.running M₁ F₁, ε'⟩ : LocalState V false × Trace V) ∈
          GuardedPlusCal.AtomicBranch.aborting Br) := by
  obtain ⟨ib, pref, hfs, hft, hfwd, hbwd, habsent, hinj, hkey, hoff, hpresent, hfifo⟩ := h
  obtain ⟨σ₁, hσ₁, hproc⟩ := hbwd p ⟨M₂, L₂⟩ hin
  obtain rfl := hfs p σ₁ ⟨M₁, L₁⟩ hσ₁ hS
  rcases blockRefines_step_indexed (href pref)
      (relatesTo_of_procRelatesTo hproc (hkey p) hfifo .none) hmem hstep with
    ⟨M₁', F₁', ε', hrel, hτ, Br, hBr, hsstep⟩ | ⟨ε', hpfx, Br, hBr, habort⟩
  · -- the label sets stay in step: the block is entered and left at source labels, so the target's
    -- new set is the source's new set plus the same `.rx` labels
    have hdisj := hproc.2.1
    have hnotrx : label ∉ rx p := Set.disjoint_left.mp hdisj hlabel
    have hT : insert label' (L₂ \ {label}) = insert label' (L₁ \ {label}) ∪ rx p := by
      rw [hproc.1, Set.union_sdiff_distrib, Set.sdiff_singleton_eq_self hnotrx, Set.insert_union]
    have hdisj' : Disjoint (insert label' (L₁ \ {label})) (rx p) := by
      rw [Set.insert_eq]
      refine Set.disjoint_union_left.mpr ⟨Set.disjoint_singleton_left.mpr hlabel', ?_⟩
      exact hdisj.mono_left Set.sdiff_subset
    -- and the key this instance receives on stays where it was
    have hstable : ∀ (c : ComputableGuardedPlusCal.Ref) (inbox : String), mb p = .some (c, inbox) →
        ∀ path : List (PathStep V), Ref.EvalArgs M₁ c path → Ref.EvalArgs M₁' c path := by
      intro c inbox hmb path hp
      have hflat : (⟨(⟨M₁, F₁, .none⟩ : LocalState' V), ε', ⟨M₁', F₁', .some label'⟩⟩ :
          LocalState' V × Trace V × LocalState' V) ∈
          GuardedPlusCal.AtomicBranch.reducing' Br :=
        GuardedPlusCal.LocalState.sem_glue₃.mp hsstep
      exact ((fresh Br hBr c inbox hmb).evalArgs hflat).mp hp
    subst hQs
    rw [hT]
    obtain ⟨ib'p, hproc', hsame, hnone, hoffk, honk⟩ :=
      procRelatesTo_of_relatesTo hproc hstable hrel hdisj'
    -- the old key, recovered from the new one — the direction `hsame` does not state outright
    have hsame' : ∀ y, ib'p = .some y → ∃ x, ib p = .some x ∧ x.key = y.key := by
      intro y hy
      obtain ⟨x, hib⟩ : ∃ x, ib p = .some x := by
        refine Option.ne_none_iff_exists'.mp ?_
        intro hnn
        rw [hnone hnn] at hy
        contradiction
      obtain ⟨ws, hws⟩ := hsame x hib
      rw [hy] at hws
      obtain rfl := Option.some.inj hws
      exact ⟨x, hib, rfl⟩
    -- so every clause phrased in terms of keys transfers from the old witness, both ways round
    have key_of : ∀ q x, Function.update ib p ib'p q = .some x →
        ∃ x₀, ib q = .some x₀ ∧ x₀.key = x.key := by
      intro q x hx
      by_cases hqp : q = p
      · subst hqp
        rw [Function.update_self] at hx
        exact hsame' x hx
      · rw [Function.update_of_ne hqp] at hx
        exact ⟨x, hx, rfl⟩
    have key_of' : ∀ q x₀, ib q = .some x₀ →
        ∃ x, Function.update ib p ib'p q = .some x ∧ x.key = x₀.key := by
      intro q x₀ hx
      by_cases hqp : q = p
      · subst hqp
        obtain ⟨ws, hws⟩ := hsame x₀ hx
        rw [Function.update_self]
        exact ⟨⟨x₀.key, ws⟩, hws, rfl⟩
      · rw [Function.update_of_ne hqp]
        exact ⟨x₀, hx, rfl⟩
    -- the new prefix function: `pref` everywhere but this instance's key, its new inbox there
    obtain ⟨pref', hpref_on, hpref_off⟩ :
        ∃ pref' : ChanKey V → List V,
          (∀ y, ib'p = .some y → pref' y.key = y.contents) ∧
          ∀ k : ChanKey V, (∀ y, ib'p = .some y → y.key ≠ k) → pref' k = pref k := by
      match hib' : ib'p with
      | .none =>
        refine ⟨pref, ?_, λ _ _ ↦ rfl⟩
        intro _ hy
        contradiction
      | .some y =>
        refine ⟨Function.update pref y.key y.contents, ?_, ?_⟩
        · intro y' hy'
          obtain rfl := Option.some.inj hy'
          exact Function.update_self ..
        · intro k hk
          exact Function.update_of_ne (Ne.symm (hk y rfl)) ..
    refine .inl ⟨M₁', F₁', ε', ?_, hτ, Br, hBr, hsstep⟩
    refine algRelatesTo.intro (ib := Function.update ib p ib'p) (pref := pref')
      (hfs.replace hS _) (hft.replace hin _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro q σ hq
      simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff, Prod.mk.injEq] at hq
      rcases hq with ⟨rfl, rfl⟩ | ⟨hmemP, hne⟩
      · refine ⟨_, Set.mem_insert _ _, ?_⟩
        rwa [Function.update_self]
      · by_cases hqp : q = p
        · -- the stepped instance's old pair is exactly what was removed, so this case is empty
          subst hqp
          absurd hne
          exact ⟨rfl, hfs _ σ ⟨M₁, L₁⟩ hmemP hS⟩
        · obtain ⟨σ', hσ', hrelq⟩ := hfwd q σ hmemP
          refine ⟨σ', Set.mem_insert_of_mem _ ⟨hσ', ?_⟩, ?_⟩
          · simp only [Set.mem_singleton_iff, Prod.mk.injEq, not_and]
            exact λ hq ↦ absurd hq hqp
          · rwa [Function.update_of_ne hqp]
    · intro q σ' hq
      simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff, Prod.mk.injEq] at hq
      rcases hq with ⟨rfl, rfl⟩ | ⟨hmemQ, hne⟩
      · refine ⟨_, Set.mem_insert _ _, ?_⟩
        rwa [Function.update_self]
      · by_cases hqp : q = p
        · subst hqp
          absurd hne
          exact ⟨rfl, hft _ σ' ⟨M₂, L₂⟩ hmemQ hin⟩
        · obtain ⟨σ, hσ, hrelq⟩ := hbwd q σ' hmemQ
          refine ⟨σ, Set.mem_insert_of_mem _ ⟨hσ, ?_⟩, ?_⟩
          · simp only [Set.mem_singleton_iff, Prod.mk.injEq, not_and]
            exact λ hq ↦ absurd hq hqp
          · rwa [Function.update_of_ne hqp]
    · intro q hq
      by_cases hqp : q = p
      · subst hqp
        exact (hq _ (Set.mem_insert _ _)).elim
      · rw [Function.update_of_ne hqp]
        refine habsent q (λ σ hσ ↦ hq σ (Set.mem_insert_of_mem _ ⟨hσ, ?_⟩))
        simp only [Set.mem_singleton_iff, Prod.mk.injEq, not_and]
        exact λ hq' ↦ absurd hq' hqp
    · intro q r x y hx hy hkeq
      obtain ⟨x₀, hx₀, hxk⟩ := key_of q x hx
      obtain ⟨y₀, hy₀, hyk⟩ := key_of r y hy
      exact hinj q r x₀ y₀ hx₀ hy₀ (hxk.trans (hkeq.trans hyk.symm))
    · intro q x hx
      by_cases hqp : q = p
      · subst hqp
        rw [Function.update_self] at hx
        exact hpref_on x hx
      · rw [Function.update_of_ne hqp] at hx
        -- this instance's key is its own, so `pref'`'s one update misses `q`'s
        refine (hpref_off x.key (λ y hy heq ↦ ?_)).trans (hkey q x hx)
        obtain ⟨x₀, hx₀, hxk⟩ := hsame' y hy
        exact hqp (hinj q p x x₀ hx hx₀ (hxk.trans heq).symm)
    · intro k hk
      refine (hpref_off k (λ y hy ↦ hk p y ?_)).trans (hoff k (λ q x₀ hx₀ heq ↦ ?_))
      · rwa [Function.update_self]
      · obtain ⟨x, hx, hxk⟩ := key_of' q x₀ hx₀
        exact hk q x hx (hxk.trans heq)
    · -- a step never removes a channel, and every new key is an old one
      intro q x hx
      obtain ⟨x₀, hx₀, hxk⟩ := key_of q x hx
      refine hxk ▸ NetworkPlusCal.AtomicBranch.reducing'_fifos_mem
        (NetworkPlusCal.LocalState.sem_glue₃.mp hstep) (hpresent q x₀ hx₀)
    · intro k
      by_cases! hk : ∀ y, ib'p = .some y → y.key ≠ k
      · rw [hpref_off k hk]
        exact hoffk k hk
      · obtain ⟨y, hy, rfl⟩ := hk
        rw [hpref_on y hy]
        exact honk y hy
  · exact .inr ⟨ε', hpfx, Br, hBr, habort⟩

/-! # The pass at this level: one process, compiled

  The other half of the process layer, and the next rung of D8's ladder after
  `Lemmas/Thread.lean`. Everything above is about a process *step*; everything below is about
  `Process.toNetwork` — what a compiled process owes its source syntactically, so that the algorithm
  level can read `AlgebraRefines` off it.

  This is the rung where `freshName` first matters. `Thread.toNetwork` is *handed* its `inbox`;
  `Process.toNetwork` invents it, one per process and shared by every thread. So a freshness
  hypothesis can no longer be stated at the name — there is no name until the pass has run — and is
  instead quantified over every name the pass could have produced (`ProcessFresh`). `Generated` is
  what makes that dischargeable: the front end knows no source identifier contains `$`, so it proves
  the implication for every counter value at once.
-/

/-- **The source-side half of D8's contract at this level.** Every branch of the process is fresh for
*any* name the pass could generate as its `inbox`.

Quantified over the generated name rather than stated at one, because `Process.toNetwork` invents it
— see the section note above. `c₀`, the process's single channel, stays a parameter: it is a fact
about the source program, which `BranchesFresh.rfresh` pins and well-formedness discharges.

`mbox` is a *function of* the generated name for the same reason. Which mailbox a process gets is
settled before the pass runs — `.none` if it never receives, `.some (c₀, ·)` if it does — but the
name filling the `·` is not, so the caller supplies the shape and the pass supplies the name. -/
def ProcessFresh (mbox : String → Mailbox) (c₀ : ComputableGuardedPlusCal.Ref)
  (p : ComputableGuardedPlusCal.Process) : Prop :=
    ∀ inbox, Generated "inbox" inbox →
      ∀ T ∈ p.threads, ∀ blk ∈ T, ∀ Br ∈ blk.branches, BranchesFresh (mbox inbox) c₀ inbox Br

/-- **A process that never receives is `ProcessFresh` at `.none` for nothing**, whatever name the pass
generates — `BranchesFresh.none_of_no_receive` at every branch. The receive-free half of D8's contract
in one line, and what says the `.none` mailbox costs the front end nothing to supply. -/
theorem ProcessFresh.none_of_no_receive {c₀ : ComputableGuardedPlusCal.Ref}
    {p : ComputableGuardedPlusCal.Process}
    (norecv : ∀ T ∈ p.threads, ∀ blk ∈ T, ∀ Br ∈ blk.branches,
      ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
        GuardedPlusCal.Statement.receive c r coe ∉ preconditionList Br.precondition) :
    ProcessFresh (λ _ ↦ .none) c₀ p :=
  λ _ _ T hT blk hblk Br hBr ↦
    BranchesFresh.none_of_no_receive (norecv T hT blk hblk Br hBr)

/-- **What one compiled process owes its source.**

`threads` is the refinement: a compiled process's threads are the receiving loops the pass
registered, followed by the compiled code threads, and those refine the source's pairwise. The split
is what `AlgebraRefines.labels` dispatches on, and `RxOnly`'s `Generated` conjunct is what keeps the
two groups' labels apart.

`name_eq` is load-bearing rather than bookkeeping. `Algorithm.algebra` resolves both `owned` and
`table` by looking the process up under its *name*, so a compiled process found under a different
name would own no labels at all. `self` needs nothing from here — it is `Prod.snd` on both sides.

`id_eq`/`idShape_eq` are owed to `Algorithm.init` rather than to `AlgebraRefines`: they are what say
the compiled algorithm has the same instances. The rest of what `init` wants — the entry labels a
receiving thread adds, and the `inbox` local the pass declares — is not here, and is the initial-state
obligation's own business. -/
structure ProcessRefines (mbox : Mailbox) (c₀ : ComputableGuardedPlusCal.Ref) (inbox : String)
  (pref : ChanKey V → List V) (p : ComputableGuardedPlusCal.Process)
  (p' : ComputableNetworkPlusCal.Process) : Prop where
    /-- The registered receive loops, then the compiled code threads. -/
    threads : ∃ rxs codes, p'.threads = rxs ++ codes ∧ RxOnly mbox c₀ inbox rxs ∧
      List.Forall₂ (ThreadRefines (V := V) mbox pref) p.threads codes
    /-- The mailbox this is all stated against is a name the pass generated. -/
    inbox_generated : Generated "inbox" inbox
    /-- And the compiled process answers to the same name, `id`, and instance shape. -/
    name_eq : p'.name = p.name
    id_eq : p'.id = p.id
    idShape_eq : p'.«=|∈» = p.«=|∈»

/-- **The source-side hygiene D8's label dispatch rests on.** No name the source process uses as a
label — neither a block's own, nor one a branch's terminal `goto` leaves for — is a name the pass
could have generated for a receiving thread.

A front-end fact, and the mirror of `Generated`'s own argument: `$` cannot occur in a TLA⁺ identifier,
so no source name is `Generated` at any prefix, and the front end proves this for every counter value
at once. Stated at `"rx"` because that is the only generated name a *label* is ever compared against
— `inbox` is a variable, and `Fresh` is what keeps it apart from those.

Both fields are needed and they are different facts. `blocks` is what makes a receiving thread's
label unschedulable as a code label (`CodeLabelRefines.not_rx`, and the collapse of
`Process.codeTable`'s union in `RxLabelRefines.target_le`); `exits` is what stops a compiled block
from *jumping into* a receiving thread (`CodeLabelRefines.exits`). A `goto` is the only terminal
statement (`Core/GuardedPlusCal/Syntax.lean`), so `Br.action.last` is where every exit is. -/
structure LabelsHygienic (p : ComputableGuardedPlusCal.Process) : Prop where
  /-- No block of the process is labelled with a name the pass could generate. -/
  blocks : ∀ T ∈ p.threads, ∀ blk ∈ T, ¬ Generated "rx" blk.label
  /-- Nor does any branch leave for one. -/
  exits : ∀ T ∈ p.threads, ∀ blk ∈ T, ∀ Br ∈ blk.branches, ∀ l,
    Br.action.last = .goto l → ¬ Generated "rx" l

/-- The labels a compiled process's receiving threads own — `AlgebraRefines`' `rx p`, read off the
compiled process rather than supplied alongside it. -/
def rxLabels (p' : ComputableNetworkPlusCal.Process) : Set String :=
  {l | ∃ chan τ inbox, NetworkPlusCal.Thread.rx chan l τ inbox ∈ p'.threads}

variable {mbox : Mailbox} {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
  {pref : ChanKey V → List V} {p : ComputableGuardedPlusCal.Process}
  {p' : ComputableNetworkPlusCal.Process}

/-- **The pass's half: every receiving label was generated.** `stepBranch` takes it from
`freshName`, `RxOnly` carries it, and the compiled process's *code* threads cannot supply one at all
— every one of them is a `.code` thread by `ThreadRefines`, and `.rx` is the other constructor.

Said about `rxLabels` rather than about a thread because that is the form the two corollaries below
want, and they are the only consumers. -/
theorem ProcessRefines.rxLabels_generated
    (h : ProcessRefines (V := V) mbox c₀ inbox pref p p') {l : String} (hl : l ∈ rxLabels p') :
    Generated "rx" l := by
  obtain ⟨_, _, hsplit, hrx, hcode⟩ := h.threads
  obtain ⟨_, _, _, hmem⟩ := hl
  rw [hsplit] at hmem
  rcases List.mem_append.mp hmem with hin | hin
  · obtain ⟨_, _, _, heq, hgen⟩ := hrx _ hin
    injection heq with _ hlbl _ _
    exact hlbl ▸ hgen
  · obtain ⟨_, _, _, hcodeq, _⟩ := hcode.exists_left hin
    exact nomatch hcodeq

/-- **A receiving thread's label is never a source label.** The disjointness every clause of
`AlgebraRefines.labels` is a corollary of: it is what makes the dispatch a dispatch rather than a
choice, and what `procRelatesTo`'s `Disjoint L₁ (rx p)` needs at the algorithm level.

Two facts meet here, one from each side, and neither alone says anything about the other's labels:
the pass generated its receiving labels, and the front end used none that could have been generated.
That split is the whole design — see `Generated`. -/
theorem ProcessRefines.rx_disjoint (h : ProcessRefines (V := V) mbox c₀ inbox pref p p')
    (hyg : LabelsHygienic p) :
    Disjoint (GuardedPlusCal.Process.ownedLabels p) (rxLabels p') := by
  rw [Set.disjoint_left]
  rintro _ ⟨T, hT, blk, hblk, rfl⟩ hl
  exact hyg.blocks T hT blk hblk (h.rxLabels_generated hl)

/-- **The compiled process's labels, split.** Every label a compiled process owns is either one of
its receiving threads' or one the source process already owned — and both directions hold, so this is
an equation rather than a containment.

That is `AlgebraRefines.labels`' case analysis, before any refinement is mentioned: `labels` has to
dispatch on a target label it is handed, and this is what says the two cases are exhaustive.
`rx_disjoint` is what says they do not overlap. The two together make `Process.ownedLabels p'` a
genuine disjoint union, which is what `procRelatesTo`'s `L₂ = L₁ ∪ rx` is stated against.

The `⊇` direction is the one that needs `Forall₂.exists_right`: a *source* thread has to be shown to
have a compiled counterpart, where every other step here goes from a compiled thing back to its
source. -/
theorem ProcessRefines.ownedLabels_eq (h : ProcessRefines (V := V) mbox c₀ inbox pref p p') :
    NetworkPlusCal.Process.ownedLabels p'
      = rxLabels p' ∪ GuardedPlusCal.Process.ownedLabels p := by
  obtain ⟨rxs, codes, hsplit, hrx, hcode⟩ := h.threads
  ext l
  iff_rintro ⟨T, hT, hl⟩ (⟨chan, τ, ib, hmem⟩ | ⟨T₀, hT₀, blk, hblk, rfl⟩)
  · rw [hsplit] at hT
    rcases List.mem_append.mp hT with hin | hin
    · -- a receiving thread owns exactly its own label
      obtain ⟨_, lbl, τ, rfl, _⟩ := hrx _ hin
      obtain rfl := List.mem_singleton.mp hl
      exact .inl ⟨c₀, τ, inbox, hsplit ▸ List.mem_append_left _ hin⟩
    · -- a code thread owns the labels of its blocks, which are its source blocks' unchanged
      obtain ⟨T₀, hT₀, blocks, rfl, hblocks⟩ := hcode.exists_left hin
      obtain ⟨blk', hblk', rfl⟩ := List.mem_map.mp hl
      obtain ⟨blk, hblk, hlabel, _⟩ := hblocks.exists_left hblk'
      exact .inr ⟨T₀, hT₀, blk, hblk, hlabel.symm⟩
  · exact ⟨_, hmem, List.mem_singleton_self _⟩
  · obtain ⟨T', hT', blocks, rfl, hblocks⟩ := hcode.exists_right hT₀
    obtain ⟨blk', hblk', hlabel, _⟩ := hblocks.exists_right hblk
    refine ⟨.code blocks, hsplit ▸ List.mem_append_right _ hT', ?_⟩
    exact List.mem_map.mpr ⟨blk', hblk', hlabel⟩

/-- **And a compiled block never leaves for one.** The same two facts at a branch's terminal `goto`
rather than at a block's own label — `CodeLabelRefines.exits`, which is what stops a code thread
from jumping into a receiving loop. -/
theorem ProcessRefines.exit_not_rx (h : ProcessRefines (V := V) mbox c₀ inbox pref p p')
    (hyg : LabelsHygienic p) {T : ComputableGuardedPlusCal.Thread} (hT : T ∈ p.threads)
    {blk : ComputableGuardedPlusCal.AtomicBlock} (hblk : blk ∈ T)
    {Br : ComputableGuardedPlusCal.AtomicBranch} (hBr : Br ∈ blk.branches) {l : String}
    (hlast : Br.action.last = .goto l) :
    l ∉ rxLabels p' :=
  λ hl ↦ hyg.exits T hT blk hblk Br hBr l hlast (h.rxLabels_generated hl)

/-! ## The branches at a label

  `CodeLabelRefines` wants two branch *lists* — the source's at a label and the target's — and
  `Process.codeTable` lets a label denote the union of every block carrying it. Nothing in the front
  end rejects two blocks with one label (`WellFormedness/Labelling.lean` checks only that every
  `goto` target exists), so these are concatenations over all such blocks rather than one block's
  branches. That is the whole reason `BranchesRefine` is weaker than `List.Forall₂`.
-/

/-- Every block the source process labels `l`, across all of its threads. -/
def srcBlocksAt (p : ComputableGuardedPlusCal.Process) (l : String) :
    List ComputableGuardedPlusCal.AtomicBlock :=
  p.threads.flatten.filter (·.label == l)

/-- And every branch of those blocks — `CodeLabelRefines`' `brs`. -/
def srcBranchesAt (p : ComputableGuardedPlusCal.Process) (l : String) :
    List ComputableGuardedPlusCal.AtomicBranch :=
  (srcBlocksAt p l).flatMap (·.branches)

/-- The blocks of a compiled process's *code* threads. Its receiving threads contribute none: an
`.rx` thread's body is the relay, which `Thread.rxBranch` gives directly rather than as a block. -/
def codeBlocks (p' : ComputableNetworkPlusCal.Process) :
    List ComputableNetworkPlusCal.AtomicBlock :=
  p'.threads.flatMap λ T ↦ match T with | .code blocks => blocks | .rx .. => []

/-- Every branch of the compiled blocks labelled `l` — `CodeLabelRefines`' `brs'`. -/
def tgtBranchesAt (p' : ComputableNetworkPlusCal.Process) (l : String) :
    List ComputableNetworkPlusCal.AtomicBranch :=
  ((codeBlocks p').filter (·.label == l)).flatMap (·.branches)

/-- Membership in `srcBranchesAt`, in the thread/block/branch form every consumer wants. -/
theorem mem_srcBranchesAt {p : ComputableGuardedPlusCal.Process} {l : String}
    {Br : ComputableGuardedPlusCal.AtomicBranch} :
    Br ∈ srcBranchesAt p l ↔
      ∃ T ∈ p.threads, ∃ blk ∈ T, blk.label = l ∧ Br ∈ blk.branches := by
  simp only [srcBranchesAt, srcBlocksAt, List.mem_flatMap, List.mem_filter, List.mem_flatten,
    beq_iff_eq]
  iff_rintro ⟨blk, ⟨⟨T, hT, hblk⟩, hlab⟩, hBr⟩ ⟨T, hT, blk, hblk, hlab, hBr⟩
  · exact ⟨T, hT, blk, hblk, hlab, hBr⟩
  · exact ⟨blk, ⟨⟨T, hT, hblk⟩, hlab⟩, hBr⟩

/-- And in `tgtBranchesAt`. The `.code` is not incidental: it is what says the block came from a
compiled code thread rather than from a relay. -/
theorem mem_tgtBranchesAt {p' : ComputableNetworkPlusCal.Process} {l : String}
    {Br' : ComputableNetworkPlusCal.AtomicBranch} :
    Br' ∈ tgtBranchesAt p' l ↔
      ∃ blocks, NetworkPlusCal.Thread.code blocks ∈ p'.threads ∧
        ∃ blk' ∈ blocks, blk'.label = l ∧ Br' ∈ blk'.branches := by
  simp only [tgtBranchesAt, codeBlocks, List.mem_flatMap, List.mem_filter, beq_iff_eq]
  iff_rintro ⟨blk', ⟨⟨T, hT, hblk'⟩, hlab⟩, hBr'⟩ ⟨blocks, hblocks, blk', hblk', hlab, hBr'⟩
  · match T, hblk' with
    | .code blocks, hblk' => exact ⟨blocks, hT, blk', hblk', hlab, hBr'⟩
  · exact ⟨blk', ⟨⟨.code blocks, hblocks, hblk'⟩, hlab⟩, hBr'⟩

/-- **A compiled step at a code label is a step of one of that label's compiled branches** —
`CodeLabelRefines.target_le`.

`l ∉ rxLabels p'` is what kills `Process.codeTable`'s second summand. Without it a receiving thread's
relay at this label would have to be attributed to a compiled branch, and there is no compiled branch
it came from — which is the whole reason the dispatch needs `label_cases`' negative half. -/
theorem tgt_reducing_le {p' : ComputableNetworkPlusCal.Process} {l : String}
    (hl : l ∉ rxLabels p') :
    ∀ x ∈ (NetworkPlusCal.Process.codeTable (V := V) p').reducing l,
      ∃ Br' ∈ tgtBranchesAt p' l, x ∈ NetworkPlusCal.AtomicBranch.reducing Br' := by
  rintro x (⟨_, hT, blocks, rfl, blk', hblk', hlab, Br', hBr', hx⟩ | ⟨_, hT, chan, τ, ib, rfl, _⟩)
  · exact ⟨Br', mem_tgtBranchesAt.mpr ⟨blocks, hT, blk', hblk', hlab, hBr'⟩, hx⟩
  · exact (hl ⟨chan, τ, ib, hT⟩).elim

/-- The same where it goes wrong — `CodeLabelRefines.target_abort_le`. -/
theorem tgt_aborting_le {p' : ComputableNetworkPlusCal.Process} {l : String}
    (hl : l ∉ rxLabels p') :
    ∀ x ∈ (NetworkPlusCal.Process.codeTable (V := V) p').aborting l,
      ∃ Br' ∈ tgtBranchesAt p' l, x ∈ NetworkPlusCal.AtomicBranch.aborting Br' := by
  rintro x (⟨_, hT, blocks, rfl, blk', hblk', hlab, Br', hBr', hx⟩ | ⟨_, hT, chan, τ, ib, rfl, _⟩)
  · exact ⟨Br', mem_tgtBranchesAt.mpr ⟨blocks, hT, blk', hblk', hlab, hBr'⟩, hx⟩
  · exact (hl ⟨chan, τ, ib, hT⟩).elim

/-- **And a source branch at a label is schedulable at it** — `CodeLabelRefines.source_reducing`.
The converse direction of the same unfolding, and it needs no side condition: the source language has
no second summand to rule out. -/
theorem src_reducing_le {p : ComputableGuardedPlusCal.Process} {l : String}
    {Br : ComputableGuardedPlusCal.AtomicBranch} (h : Br ∈ srcBranchesAt p l) :
    GuardedPlusCal.AtomicBranch.reducing (V := V) Br ⊆
      (GuardedPlusCal.Process.codeTable p).reducing l := by
  obtain ⟨T, hT, blk, hblk, hlab, hBr⟩ := mem_srcBranchesAt.mp h
  exact λ _ hx ↦ ⟨T, hT, blk, hblk, hlab, Br, hBr, hx⟩

/-- The same where it goes wrong — `CodeLabelRefines.source_aborting`. -/
theorem src_aborting_le {p : ComputableGuardedPlusCal.Process} {l : String}
    {Br : ComputableGuardedPlusCal.AtomicBranch} (h : Br ∈ srcBranchesAt p l) :
    GuardedPlusCal.AtomicBranch.aborting (V := V) Br ⊆
      (GuardedPlusCal.Process.codeTable p).aborting l := by
  obtain ⟨T, hT, blk, hblk, hlab, hBr⟩ := mem_srcBranchesAt.mp h
  exact λ _ hx ↦ ⟨T, hT, blk, hblk, hlab, Br, hBr, hx⟩

/-- **The refinement, at a label rather than at a block** — `CodeLabelRefines.refines`.

Three `exists_left`s stacked: a compiled branch sits in a compiled block, which sits in a compiled
code thread, which is some source thread's; the block correspondence carries `blk'.label = blk.label`,
so the source block is at the *same* label and its branches are the ones to match against. The
labels agreeing is what makes this a statement about a label at all — otherwise the two
concatenations would be over unrelated blocks. -/
theorem ProcessRefines.branchesRefine (h : ProcessRefines (V := V) mbox c₀ inbox pref p p')
    (l : String) :
    BranchesRefine (V := V) mbox pref (srcBranchesAt p l) (tgtBranchesAt p' l) := by
  obtain ⟨rxs, codes, hsplit, hrx, hcode⟩ := h.threads
  intro Br' hBr'
  obtain ⟨blocks, hblocks, blk', hblk', hlab, hmem⟩ := mem_tgtBranchesAt.mp hBr'
  rw [hsplit] at hblocks
  rcases List.mem_append.mp hblocks with hin | hin
  · -- a `.code` thread is never one the pass registered
    obtain ⟨_, _, _, heq, _⟩ := hrx _ hin
    exact nomatch heq
  · obtain ⟨T₀, hT₀, blocks₀, hcodeq, hblocks₀⟩ := hcode.exists_left hin
    injection hcodeq with hbl
    obtain ⟨blk, hblk, hlabeq, hbranches⟩ := hblocks₀.exists_left (hbl ▸ hblk')
    obtain ⟨Br, hBr, href⟩ := hbranches.exists_left hmem
    exact ⟨Br, mem_srcBranchesAt.mpr ⟨T₀, hT₀, blk, hblk, hlabeq ▸ hlab, hBr⟩, href⟩

/-- **The dispatch itself.** A label the compiled process owns belongs to exactly one of the two
groups, and the case analysis carries the *negative* fact as well as the positive one.

`ownedLabels_eq` gives exhaustiveness and `rx_disjoint` exclusivity; this is the two packaged in the
shape `AlgebraRefines.labels` consumes. The negative halves are not decoration —
`CodeLabelRefines.not_rx` is one of them, and the other is what collapses `Process.codeTable`'s union
at a receiving label. -/
theorem ProcessRefines.label_cases (h : ProcessRefines (V := V) mbox c₀ inbox pref p p')
    (hyg : LabelsHygienic p) {l : String}
    (hl : l ∈ NetworkPlusCal.Process.ownedLabels p') :
    (l ∈ GuardedPlusCal.Process.ownedLabels p ∧ l ∉ rxLabels p') ∨
      (l ∈ rxLabels p' ∧ l ∉ GuardedPlusCal.Process.ownedLabels p) := by
  rcases h.ownedLabels_eq ▸ hl with hrx | hsrc
  · exact .inr ⟨hrx, Set.disjoint_right.mp (h.rx_disjoint hyg) hrx⟩
  · exact .inl ⟨hsrc, Set.disjoint_left.mp (h.rx_disjoint hyg) hsrc⟩

open Std.Do in
/-- **The walk over a process's threads.** `Thread.toNetwork_spec` iterated by `Spec.mapM_list`, at
the invariant "the code threads compiled so far refine pairwise, and every receiving thread
registered so far is an `.rx` on this `inbox`".

Stated at a fixed `inbox` — the *caller* is what generates one. That is what keeps this a plain
`mapM` lemma and leaves `Process.toNetwork_spec` below with nothing to do but read the accumulator
apart. -/
private theorem mapM_threadToNetwork_spec [SeqBuiltins V] {chans : Guarded2NetworkChans}
  {mbox : Mailbox} {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V}
  {Ts : List ComputableGuardedPlusCal.Thread}
  (fresh : ∀ T ∈ Ts, ∀ blk ∈ T, ∀ Br ∈ blk.branches, BranchesFresh mbox c₀ inbox Br) :
    ⦃⌜True⌝⦄
    Ts.mapM (ComputableGuardedPlusCal.Thread.toNetwork (m := G2NM) chans inbox)
    ⦃⇓? rs _ =>
      ⌜List.Forall₂ (ThreadRefines (V := V) mbox pref) Ts (rs.map (·.2.2)) ∧
        RxOnly mbox c₀ inbox (rs.flatMap (·.2.1))⌝⦄ := by
  mvcgen [Thread.toNetwork_spec]
  invariants
  | inv1 => ⇓? ⟨cur, res⟩ _ =>
    ⌜List.Forall₂ (ThreadRefines (V := V) mbox pref) cur.prefix (res.map (·.2.2)) ∧
      RxOnly mbox c₀ inbox (res.flatMap (·.2.1))⌝
  with
  -- `Thread.toNetwork_spec`'s implicits, abstracted over the loop's context and wrapped in `id`
  | vc5 | vc6 | vc7 | vc8 | vc9 | vc10 => intro _ _; assumption

  case vc1.pre => exact ⟨.nil, nofun⟩
  case vc2.post.success => intro hthr hrx; exact ⟨hthr, hrx⟩

  case vc3.post.success _ _ _ _ _ _ _ hinv _ =>
    intro _ hthr hrx
    rw [List.map_append, List.flatMap_append, List.flatMap_singleton]
    refine ⟨List.rel_append hinv.1 (List.forall₂_singleton.mpr hthr), ?_⟩
    exact List.forall_mem_append.mpr ⟨hinv.2, hrx⟩

  -- the freshness hypothesis at whichever thread the walk is currently on
  case vc11 _ _ cur _ hsplit _ =>
    intro _ _
    rw [hsplit] at fresh
    exact fresh cur (List.mem_append_right _ List.mem_cons_self)

open Std.Do in
/-- **One process, compiled.** The `inbox` generated, the walk over the threads, and the compiled
process read off the accumulator.

The `inbox` is existential in the conclusion for the reason `Generated` exists: a postcondition
cannot name the counter the program started at, and nothing above needs the number — only that there
is a single name, shared by every thread of this process, that no source identifier can equal. -/
theorem Process.toNetwork_spec [SeqBuiltins V] {globalChans : Guarded2NetworkChans}
  {mbox : String → Mailbox} {c₀ : ComputableGuardedPlusCal.Ref} {pref : ChanKey V → List V}
  {p : ComputableGuardedPlusCal.Process} (fresh : ProcessFresh mbox c₀ p) :
    ⦃⌜True⌝⦄
    ComputableGuardedPlusCal.Process.toNetwork (m := G2NM) globalChans p
    ⦃⇓? p' _ => ⌜∃ inbox, ProcessRefines (V := V) (mbox inbox) c₀ inbox pref p p'⌝⦄ := by
  -- `-Spec.mapM_list`, or the generic loop spec matches the walk before `mapM_threadToNetwork_spec`
  -- does and `mvcgen` asks for an invariant that was already supplied one level down
  mvcgen [ComputableGuardedPlusCal.Process.toNetwork, freshName_spec, mapM_threadToNetwork_spec,
    -Std.Do.Spec.mapM_list]

  -- the mailbox and the walk's freshness hypothesis, both at the name `freshName` just generated
  case vc4.mbox _ ib _ _ _ => exact mbox ib
  case vc7.fresh => exact fresh _ ‹_›

  case vc8.post.success.post.success _ _ _ _ hgen _ _ _ _ _ hinv =>
    refine ⟨_, ?_, hgen, rfl, rfl, rfl⟩
    exact ⟨_, _, rfl, hinv.2, hinv.1⟩

end Guarded2Network

end
