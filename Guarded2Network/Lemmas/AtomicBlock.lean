module

meta import CustomPrelude
public import Guarded2Network.Lemmas.AtomicBranch
import all Guarded2Network.Lemmas.AtomicBranch
import all Guarded2Network.PlusCal

@[expose] public section

/-!
  One atomic block, compiled.

  `stepBlock` (`Guarded2Network/PlusCal.lean`) maps `stepBranch` over the block's branches and keeps
  the label. So this file is `stepBranch_spec` under `Spec.mapM_list`, and the only thing worth
  saying about it is what the loop invariant carries.

  Three things come out, and each is needed one level up. The branches are pairwise `BranchRefines`,
  which is the refinement itself. The label is unchanged, and every branch still ends on the same
  `goto` (`BranchRefines.last_eq`) — together, "the gotos agree": a block is entered by label and
  left by its branches' terminal statements, so a compiled block agreeing on neither would refine
  its source branch by branch and still be scheduled differently. And `RxThreads` is threaded
  through, since `stepBranch` is what appends to it and the thread level is what consumes it.

  There is deliberately no `StrongRefinement` between *block* semantics here.
  `AtomicBlock.reducing` exists only on the `NetworkPlusCal` side
  (`Core/NetworkPlusCal/Semantics/Denotational.lean`'s module doc says why: a source block is only
  ever existentially quantified, never required to match a target's type), so the pairwise statement
  over branches is the strongest thing statable — and it is what the process level wants anyway,
  since that is where a target branch gets matched to *some* source branch.
-/

namespace Guarded2Network

universe u

open ComputableTLAPlus (OperatorEnv Model)
open GuardedPlusCal (Block ChanKey LocalState Trace)

variable {V : Type u} [ComputableTLAPlus.ExprSemantics V] [SeqBuiltins V] {Ξ : OperatorEnv}
  {Ω : Model V}

/-- Every freshness hypothesis `stepBranch_spec` takes, at every branch of a block. Bundled because
all six travel together from here up: they are conditions on the source program and on the pass's
generated `inbox`, discharged by the passes before this one.

`mbox` is a parameter and `mbox_some` is what makes it one. A process with no `receive` is compiled
without an `inbox` local and has to be related at `.none` (`Mailbox`'s own doc); every other field
here holds at either mailbox, and `receive` is the only construct that forces the `.some` one. -/
structure BranchesFresh (mbox : Mailbox) (c₀ : ComputableGuardedPlusCal.Ref) (inbox : String)
    (Br : ComputableGuardedPlusCal.AtomicBranch) : Prop where
  /-- A branch that receives at all is a branch of a process with a mailbox. -/
  mbox_some : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
    GuardedPlusCal.Statement.receive c r coe ∈ preconditionList Br.precondition →
      mbox = .some (c₀, inbox)
  /-- Every `receive` in the precondition reads the process's one channel, and neither its channel
  nor its target mentions the generated `inbox`. -/
  rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
    GuardedPlusCal.Statement.receive c r coe ∈ preconditionList Br.precondition →
      c = c₀ ∧ ReceiveFresh c r coe inbox
  /-- No precondition statement mentions the mailbox. -/
  gfresh : ∀ S ∈ preconditionList Br.precondition, Fresh mbox S
  /-- No `with` in the precondition binds a name a consumption pair reads. -/
  pfresh : PairsFresh inbox (preconditionList Br.precondition)
  /-- Nor does any action statement mention the mailbox. -/
  afresh : ∀ S ∈ Br.action.begin, Fresh mbox S
  /-- Including the terminal one. -/
  alast : Fresh mbox Br.action.last

/-- **A branch that never receives is fresh at `.none` for nothing.** Every field above is a
condition on the generated `inbox`, and at `.none` there is no `inbox` to condition on: `Fresh .none`
is vacuous by definition, and `mbox_some`/`rfresh`/`pfresh` all quantify over the branch's
`receive`s, of which there are none.

This is what makes the `.none` mailbox *reachable* rather than merely statable, and so it is the
whole point of `mbox` being a parameter. A process with no `receive` is compiled without an `inbox`
local, so `relatesTo (.some (c, inbox))` — which requires the target's memory to bind `inbox` — is
false of it at `Algorithm.init`. `.none` is the only mailbox such a process can have, and this is how
it gets one. -/
theorem BranchesFresh.none_of_no_receive {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
  {Br : ComputableGuardedPlusCal.AtomicBranch}
  (norecv : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
    GuardedPlusCal.Statement.receive c r coe ∉ preconditionList Br.precondition) :
    BranchesFresh .none c₀ inbox Br where
  mbox_some c r coe h := (norecv c r coe h).elim
  rfresh c r coe h := (norecv c r coe h).elim
  gfresh _ _ := nofun
  pfresh _ _ _ _ _ c r coe h := (norecv c r coe h).elim
  afresh _ _ := nofun
  alast := nofun

/-- A block one of whose branches receives — `BranchReceives` at the level the walk above is over.
What a block owes about receiving is conditioned on this, and one branch is enough: the pass
registers a thread the first time any branch of any block of the thread asks for one. -/
def BlockReceives (blk : ComputableGuardedPlusCal.AtomicBlock) : Prop :=
  ∃ Br ∈ blk.branches, BranchReceives Br

/-- What one compiled block owes its source: the same label, and branches pairwise `BranchRefines`.

The thread level quantifies over it — a compiled `.code` thread's blocks are pairwise this,
`List.Forall₂`-style — for the same reason `BranchRefines` exists one level down: a conjunction
cannot be the argument of a relation combinator.

A `def` rather than a `structure` on purpose. `stepBlock_spec` below is a `mvcgen` proof whose
postcondition is assembled automatically from the loop invariant, and that assembly sees through a
`reducible` conjunction where it would have to be taught a constructor. -/
@[reducible] def BlockRefines (Ξ : OperatorEnv) (Ω : Model V) (mbox : Mailbox)
    (pref : ChanKey V → List V) (blk : ComputableGuardedPlusCal.AtomicBlock)
    (blk' : ComputableNetworkPlusCal.AtomicBlock) : Prop :=
  blk'.label = blk.label ∧
    List.Forall₂ (BranchRefines (V := V) Ξ Ω mbox pref) blk.branches blk'.branches

open Std.Do in
/-- **One block, compiled.** `stepBranch_spec` iterated over the branches by `Spec.mapM_list`, at
the invariant "the branches compiled so far are pairwise `BranchRefines`, and `RxThreads` still
holds".

The label is `rfl` — `stepBlock` copies it — and the per-branch `goto` agreement rides along inside
`BranchRefines`. Together they are what makes the compiled block schedulable in the source block's
place.

The invariant is supplied to `mvcgen` rather than proved after it: `Spec.mapM_list` is `@[spec]`, so
`mvcgen` finds the loop on its own and only wants the invariant. -/
private theorem stepBlock_spec {chans : Guarded2NetworkChans} {mbox : Mailbox}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V} {H : Prop}
    {blk : ComputableGuardedPlusCal.AtomicBlock} {Ξ : OperatorEnv} {Ω : Model V}
    (hΞ : Ξ.WellScoped)
    (fresh : ∀ Br ∈ blk.branches, BranchesFresh mbox c₀ inbox Br) :
    ⦃λ st ↦ ⌜RxThreads mbox c₀ inbox st ∧ Registered H st⌝⦄
    stepBlock (m := G2NM) chans inbox blk
    ⦃⇓? blk' st' =>
      ⌜BlockRefines (V := V) Ξ Ω mbox pref blk blk' ∧ RxThreads mbox c₀ inbox st' ∧
        Registered (H ∨ BlockReceives blk) st'⌝⦄ := by
  mvcgen [stepBlock, stepBranch_spec]
  invariants
  | inv1 => ⇓? ⟨cur, res⟩ st =>
    ⌜List.Forall₂ (BranchRefines (V := V) Ξ Ω mbox pref) cur.prefix res ∧
      RxThreads mbox c₀ inbox st ∧ Registered (H ∨ ∃ Br ∈ cur.prefix, BranchReceives Br) st⌝
  with
  -- `stepBranch_spec`'s remaining implicits and instances, discharged before any case has to unify
  -- against them. `mbox`, `c₀` and `H` are deliberately absent: the loop invariant pins all three,
  -- and answering them by `assumption` instead would supply `H` where the accumulated disjunction
  -- is meant.
  | vc4 | vc5 | vc8 | vc9 | vc10 | vc11 | vc12 | vc13 =>
    solve | assumption | (intro _ _ _; assumption)

  -- the label is `rfl`; re-associating the rest is all that separates the loop's invariant from
  -- `BlockRefines`
  case vc21.post.success _ _ _ _ _ _ h => exact ⟨⟨rfl, h.1⟩, h.2⟩

  case vc1.step.pre h => exact h.2

  case vc2.step.post.success _ _ _ _ _ _ _ _ _ _ hinv _ =>
    intro _ _ hbr hrx hreg
    refine ⟨List.rel_append hinv.1 (List.forall₂_singleton.mpr hbr), hrx, λ h ↦ hreg ?_⟩
    -- the branch spec registers against "everything before this branch, or this branch"; the
    -- invariant reads the same fact off the walked prefix with this branch appended
    rcases h with h | ⟨Br, hmem, hBr⟩
    · exact .inl (.inl h)
    · rcases List.mem_append.mp hmem with hm | hm
      · exact .inl (.inr ⟨Br, hm, hBr⟩)
      · exact .inr (List.mem_singleton.mp hm ▸ hBr)

  case vc20.pre =>
    obtain ⟨hrx, hreg⟩ := ‹_ ∧ _›
    -- nothing walked yet, so the walk has registered nothing and owes nothing
    refine ⟨.nil, hrx, λ h ↦ hreg ?_⟩
    simp_all
  -- one `BranchesFresh` field each, at whichever branch the walk is currently on
  case vc14 _ _ _ _ cur _ hsplit _ | vc15 _ _ _ _ cur _ hsplit _ | vc16 _ _ _ _ cur _ hsplit _
     | vc17 _ _ _ _ cur _ hsplit _ | vc18 _ _ _ _ cur _ hsplit _ | vc19 _ _ _ _ cur _ hsplit _ =>
    intro _ _
    rw [hsplit] at fresh
    obtain ⟨_, _, _, _, _, _⟩ := fresh cur (List.mem_append_right _ List.mem_cons_self)
    -- the invariant arrives as one conjunction or curried per conjunct, depending on the field
    solve | assumption | (intro _; assumption) | (intro _ _ _; assumption)

end Guarded2Network

end
