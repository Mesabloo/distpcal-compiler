module

meta import CustomPrelude
public import Guarded2Network.Lemmas.AtomicBlock
import all Guarded2Network.Lemmas.AtomicBlock
import all Guarded2Network.PlusCal

@[expose] public section

/-!
  One thread, compiled.

  `Thread.toNetwork` (`Guarded2Network/PlusCal.lean`) maps `stepBlock` over the thread's blocks at a
  `ThreadState` accumulator and hands back three things: the locals the pass invented, the receiving
  threads it registered, and the compiled code thread itself. So this file is `stepBlock_spec` under
  `Spec.mapM_list`, exactly as the level below is `stepBranch_spec` under it — and then the same
  statement once more at `.run {}`, which is the form the pass's own body presents.

  Two of the three outputs get a conclusion. The compiled thread is `ThreadRefines`, the blocks
  pairwise `BlockRefines`; and the registered threads are `RxOnly`, each an `.rx` on this call's
  `inbox`. The locals get none: they are a declaration list, and what a compiled process owes about
  its declarations is a scoping question the process level asks, not a refinement one.
-/

namespace Guarded2Network

open GuardedPlusCal (ChanKey)

variable {V : Type} [ComputableTLAPlus.ExprSemantics V] [SeqBuiltins V]

/-- What one compiled **code** thread owes its source: it is a `.code` thread at all, and its blocks
are pairwise `BlockRefines`.

The `.code` half is not bookkeeping. A source thread is a list of blocks and a target thread is
either that or a receive loop, so "the compiled thread is not itself an `.rx`" is a real thing to
say — and it is what lets the process level split a compiled process's threads into the two groups
`AlgebraRefines` dispatches on. -/
def ThreadRefines (mbox : Mailbox) (pref : ChanKey V → List V)
  (T : ComputableGuardedPlusCal.Thread) (T' : ComputableNetworkPlusCal.Thread) : Prop :=
    ∃ blocks, T' = .code blocks ∧ List.Forall₂ (BlockRefines (V := V) mbox pref) T blocks

open Std.Do in
/-- **The walk over a thread's blocks.** `stepBlock_spec` iterated by `Spec.mapM_list`, at the
invariant "the blocks compiled so far are pairwise `BlockRefines`, and every registered thread is
still an `.rx` on this `inbox`".

Both conjuncts are needed. The first is the refinement; the second is what the *next* block's
`stepBlock_spec` asks for in its precondition, `stepBranch` being free to append a receiving thread
at any branch of any block. -/
private theorem mapM_stepBlock_spec {chans : Guarded2NetworkChans}
  {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V}
  {T : ComputableGuardedPlusCal.Thread}
  (fresh : ∀ blk ∈ T, ∀ Br ∈ blk.branches, BranchesFresh c₀ inbox Br) :
    ⦃λ st ↦ ⌜RxThreads inbox st⌝⦄
    T.mapM (stepBlock (m := G2NM) chans inbox)
    ⦃⇓? blocks st' =>
      ⌜List.Forall₂ (BlockRefines (V := V) (.some (c₀, inbox)) pref) T blocks ∧
        RxThreads inbox st'⌝⦄ := by
  mvcgen [stepBlock_spec]
  invariants
  | inv1 => ⇓? ⟨cur, res⟩ st =>
    ⌜List.Forall₂ (BlockRefines (V := V) (.some (c₀, inbox)) pref) cur.prefix res ∧
      RxThreads inbox st⌝
  with
  -- `stepBlock_spec`'s implicits, abstracted over the loop's context and wrapped in `id` — the value
  -- type and the channel a block's receives read are in neither the program nor the invariant
  | vc6 | vc7 | vc8 | vc9 | vc10 => intro _ _ _; assumption

  case vc1.pre => exact ⟨.nil, ‹_›⟩
  case vc2.post.success => intro _ hblk hrx; exact ⟨hblk, hrx⟩
  case vc3.pre _ _ _ _ _ _ _ _ _ _ hinv => exact hinv.2

  case vc4.post.success _ _ _ _ _ _ _ _ _ _ hinv _ =>
    intro _ _ hlabel hbrs hrx
    exact ⟨List.rel_append hinv.1 (List.forall₂_singleton.mpr ⟨hlabel, hbrs⟩), hrx⟩

  -- the freshness hypothesis at whichever block the walk is currently on
  case vc11 _ _ _ _ cur _ hsplit _ =>
    intro _ _ _
    rw [hsplit] at fresh
    exact fresh cur (List.mem_append_right _ List.mem_cons_self)

open Std.Do in
/-- `mapM_stepBlock_spec` at the initial accumulator, which is the form `Thread.toNetwork`'s own body
presents: it writes `(… .mapM …).run {}`, and `StateT.run x s` reduces to `x s`, so the toolchain's
`[spec] StateT.run` never fires and `mvcgen` cannot descend on its own — the same reason
`mapM_stepStatement_refines_run` exists one pass level down.

The initial accumulator is `{}`, whose `rxThreads` is `[]`, so the precondition is vacuous. -/
@[spec] private theorem mapM_stepBlock_spec_run {chans : Guarded2NetworkChans}
  {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V}
  {T : ComputableGuardedPlusCal.Thread}
  (fresh : ∀ blk ∈ T, ∀ Br ∈ blk.branches, BranchesFresh c₀ inbox Br) :
    ⦃⌜True⌝⦄
    ((T.mapM (stepBlock (m := G2NM) chans inbox)).run {})
    ⦃⇓? p _ => ⌜List.Forall₂ (BlockRefines (V := V) (.some (c₀, inbox)) pref) T p.1 ∧
      RxOnly inbox p.2.rxThreads⌝⦄ := by
  intro n _
  refine mapM_stepBlock_spec (V := V) (pref := pref) fresh {} n ?_
  nofun

open Std.Do in
/-- **One thread, compiled.** The walk, plus reading the accumulator apart into the pass's three
outputs.

Everything difficult already happened in `stepBlock_spec`; what this adds is the `ThreadRefines`
packaging and the fact that the returned thread is `.code` — `Thread.toNetwork` builds it, so that
half is `rfl`. -/
theorem Thread.toNetwork_spec {chans : Guarded2NetworkChans}
  {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V}
  {T : ComputableGuardedPlusCal.Thread}
  (fresh : ∀ blk ∈ T, ∀ Br ∈ blk.branches, BranchesFresh c₀ inbox Br) :
    ⦃⌜True⌝⦄
    ComputableGuardedPlusCal.Thread.toNetwork (m := G2NM) chans inbox T
    ⦃⇓? r => ⌜ThreadRefines (V := V) (.some (c₀, inbox)) pref T r.2.2 ∧ RxOnly inbox r.2.1⌝⦄ := by
  -- `-StateT.run`, or the toolchain's own spec for it wins and `mapM_stepBlock_spec_run` never
  -- matches — the same removal `processPrecondition_spec` needs one pass level down
  mvcgen [ComputableGuardedPlusCal.Thread.toNetwork, -StateT.run]
  case vc7.post.success _ _ _ h => exact ⟨⟨_, rfl, h.1⟩, h.2⟩

end Guarded2Network

end
