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

/-- A thread one of whose blocks receives — the level at which the pass's registration promise is
finally cashed, `Thread.toNetwork` being what hands `rxThreads` back as a list of threads. -/
def ThreadReceives (T : ComputableGuardedPlusCal.Thread) : Prop :=
  ∃ blk ∈ T, BlockReceives blk

open Std.Do in
/-- **The walk over a thread's blocks.** `stepBlock_spec` iterated by `Spec.mapM_list`, at the
invariant "the blocks compiled so far are pairwise `BlockRefines`, every registered thread is still
an `.rx` on this `inbox`, and a block walked so far that receives has left one registered".

All three are needed. The first is the refinement; the second and third are what the *next* block's
`stepBlock_spec` asks for in its precondition, `stepBranch` being free to append a receiving thread
at any branch of any block. -/
private theorem mapM_stepBlock_spec {chans : Guarded2NetworkChans}
  {mbox : Mailbox} {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V}
  {H : Prop} {T : ComputableGuardedPlusCal.Thread}
  (fresh : ∀ blk ∈ T, ∀ Br ∈ blk.branches, BranchesFresh mbox c₀ inbox Br) :
    ⦃λ st ↦ ⌜RxThreads mbox c₀ inbox st ∧ Registered H st⌝⦄
    T.mapM (stepBlock (m := G2NM) chans inbox)
    ⦃⇓? blocks st' =>
      ⌜List.Forall₂ (BlockRefines (V := V) mbox pref) T blocks ∧
        RxThreads mbox c₀ inbox st' ∧ Registered (H ∨ ThreadReceives T) st'⌝⦄ := by
  mvcgen [stepBlock_spec]
  invariants
  | inv1 => ⇓? ⟨cur, res⟩ st =>
    ⌜List.Forall₂ (BlockRefines (V := V) mbox pref) cur.prefix res ∧
      RxThreads mbox c₀ inbox st ∧ Registered (H ∨ ∃ blk ∈ cur.prefix, BlockReceives blk) st⌝
  with
  -- `stepBlock_spec`'s implicits and instances, abstracted over the loop's context and wrapped in
  -- `id` — the value type and the prefix function are in neither the program nor the invariant.
  -- `mbox`, `c₀` and `H` are, so they are pinned and deliberately absent here: `H`'s goal is a
  -- `Prop` to supply, and `assumption` would supply `H` itself rather than the disjunction the walk
  -- has accumulated (`AtomicBlock.lean` says the same at more length).
  | vc9 | vc10 | vc11 | vc12 => intro _ _ _; assumption

  case vc1.pre =>
    obtain ⟨hrx, hreg⟩ := ‹_ ∧ _›
    refine ⟨.nil, hrx, λ h ↦ hreg ?_⟩
    simp_all
  case vc2.post.success => intro _ hblk hrx hreg; exact ⟨hblk, hrx, hreg⟩
  case vc3.pre _ _ _ _ _ _ _ _ _ _ hinv => exact hinv.2

  case vc4.post.success _ _ _ _ _ _ _ _ _ _ hinv _ =>
    intro _ _ hlabel hbrs hrx hreg
    refine ⟨List.rel_append hinv.1 (List.forall₂_singleton.mpr ⟨hlabel, hbrs⟩), hrx, λ h ↦ hreg ?_⟩
    -- the block spec registers against "everything before this block, or this block"; the invariant
    -- reads the same fact off the walked prefix with this block appended
    rcases h with h | ⟨blk, hmem, hblk⟩
    · exact .inl (.inl h)
    · rcases List.mem_append.mp hmem with hm | hm
      · exact .inl (.inr ⟨blk, hm, hblk⟩)
      · exact .inr (List.mem_singleton.mp hm ▸ hblk)

  -- the freshness hypothesis at whichever block the walk is currently on
  case vc13 _ _ _ _ cur _ hsplit _ =>
    intro _ _ _
    rw [hsplit] at fresh
    exact fresh cur (List.mem_append_right _ List.mem_cons_self)

open Std.Do in
/-- `mapM_stepBlock_spec` at the initial accumulator, which is the form `Thread.toNetwork`'s own body
presents: it writes `(… .mapM …).run {}`, and `StateT.run x s` reduces to `x s`, so the toolchain's
`[spec] StateT.run` never fires and `mvcgen` cannot descend on its own — the same reason
`mapM_stepStatement_refines_run` exists one pass level down.

The initial accumulator is `{}`, whose `rxThreads` is `[]`, so the precondition is vacuous — and the
same emptiness is what collapses the walk's ghost: `Registered`'s carried proposition is what *has*
already registered a thread, which before the walk starts is nothing, so `H` is `False` here. It
appears as such in the conclusion, and dies one level up in `Thread.toNetwork_spec`, which is a
`mvcgen` proof and can weaken a postcondition where this one has to match it up to defeq. -/
@[spec] private theorem mapM_stepBlock_spec_run {chans : Guarded2NetworkChans}
  {mbox : Mailbox} {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V}
  {T : ComputableGuardedPlusCal.Thread}
  (fresh : ∀ blk ∈ T, ∀ Br ∈ blk.branches, BranchesFresh mbox c₀ inbox Br) :
    ⦃⌜True⌝⦄
    ((T.mapM (stepBlock (m := G2NM) chans inbox)).run {})
    ⦃⇓? p _ => ⌜List.Forall₂ (BlockRefines (V := V) mbox pref) T p.1 ∧
      RxThreads mbox c₀ inbox p.2 ∧ Registered (False ∨ ThreadReceives T) p.2⌝⦄ := by
  intro n _
  refine mapM_stepBlock_spec (V := V) (pref := pref) (H := False) fresh {} n ?_
  exact ⟨⟨nofun, nofun, iff_of_true rfl rfl⟩, nofun⟩

open Std.Do in
/-- **One thread, compiled.** The walk, plus reading the accumulator apart into the pass's three
outputs.

Everything difficult already happened in `stepBlock_spec`; what this adds is the `ThreadRefines`
packaging and the fact that the returned thread is `.code` — `Thread.toNetwork` builds it, so that
half is `rfl`. -/
theorem Thread.toNetwork_spec {chans : Guarded2NetworkChans}
  {mbox : Mailbox} {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V}
  {T : ComputableGuardedPlusCal.Thread}
  (fresh : ∀ blk ∈ T, ∀ Br ∈ blk.branches, BranchesFresh mbox c₀ inbox Br) :
    ⦃⌜True⌝⦄
    ComputableGuardedPlusCal.Thread.toNetwork (m := G2NM) chans inbox T
    ⦃⇓? r => ⌜ThreadRefines (V := V) mbox pref T r.2.2 ∧ RxOnly mbox c₀ inbox r.2.1 ∧
      (ThreadReceives T → r.2.1 ≠ []) ∧ (∀ e ∈ r.1, InboxLocal inbox e) ∧
      (r.1 = [] ↔ r.2.1 = [])⌝⦄ := by
  -- `-StateT.run`, or the toolchain's own spec for it wins and `mapM_stepBlock_spec_run` never
  -- matches — the same removal `processPrecondition_spec` needs one pass level down
  mvcgen [ComputableGuardedPlusCal.Thread.toNetwork, -StateT.run]
  case vc8.post.success _ _ _ h =>
    exact ⟨⟨_, rfl, h.1⟩, h.2.1.1, (λ hrecv ↦ h.2.2 (.inr hrecv)), h.2.1.2.1, h.2.1.2.2⟩

end Guarded2Network

end
