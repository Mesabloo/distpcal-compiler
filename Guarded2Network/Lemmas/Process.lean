module

meta import CustomPrelude
public import Guarded2Network.Lemmas.AtomicBlock
public import Guarded2Network.Lemmas.Locality
import all Guarded2Network.Lemmas.AtomicBlock

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
    {Br : ComputableGuardedPlusCal.AtomicBranch} (hf : BranchesFresh c₀ inbox Br)
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
    (h : List.Forall₂ (BranchRefines (V := V) mbox pref) brs brs')
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
  obtain ⟨Br, hBr, href⟩ := h.exists_left hmem
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
    (h : List.Forall₂ (BranchRefines (V := V) mbox pref) brs brs')
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
    (h : List.Forall₂ (BranchRefines (V := V) mbox pref) brs brs')
    {σₛ σₜ : LocalState' V} {ε : Trace V} (sim : σₛ ∼[mbox, pref] σₜ)
    {Br' : ComputableNetworkPlusCal.AtomicBranch} (hmem : Br' ∈ brs')
    (habort : (⟨σₜ, ε⟩ : LocalState' V × Trace V) ∈ NetworkPlusCal.AtomicBranch.aborting' Br') :
    ∃ ε', ε' ≼[(instTrace (V := V)).Rτ] ε ∧
      ∃ Br ∈ brs, (⟨σₛ, ε'⟩ : LocalState' V × Trace V) ∈
        GuardedPlusCal.AtomicBranch.aborting' Br := by
  obtain ⟨Br, hBr, href⟩ := h.exists_left hmem
  obtain ⟨ε', hpfx, hsabort⟩ := href.refines.aborting σₜ ε σₛ sim habort
  exact ⟨ε', hpfx, Br, hBr, hsabort⟩

/-- `blockRefines_abort` at the *indexed* encoding, exactly as `blockRefines_step_indexed` is for
`blockRefines_step`. -/
theorem blockRefines_abort_indexed {mbox : Mailbox} {pref : ChanKey V → List V}
    {brs : List ComputableGuardedPlusCal.AtomicBranch}
    {brs' : List ComputableNetworkPlusCal.AtomicBranch}
    (h : List.Forall₂ (BranchRefines (V := V) mbox pref) brs brs')
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
      List.Forall₂ (BranchRefines (V := V) (mb p) pref) brs brs')
    (fresh : ∀ Br ∈ brs, ∀ c inbox, mb p = .some (c, inbox) → BranchesFresh c inbox Br)
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

end Guarded2Network

end
