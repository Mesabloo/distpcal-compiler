module

meta import CustomPrelude
public import Guarded2Network.Lemmas.AtomicBlock
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
  layer is stated against. Both halves need `pref` to be a parameter of `relatesTo` — that is what
  it is for (`Lemmas/Relation.lean`).

  The indexed/flat boundary is crossed here too. `CodeTable.reducing` is stated at the indexed
  `LocalState`, every refinement lemma at the flat `LocalState'`, and
  `GuardedPlusCal.LocalState.sem_glue₃`/`.abort_glue₂` are what say those are the same fact.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Memory)
open GuardedPlusCal (ChanKey FIFOs LocalState LocalState' ProcState Trace)

variable {V : Type} [ExprSemantics V]

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

end Guarded2Network

end
