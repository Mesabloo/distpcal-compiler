module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Precondition
import all Guarded2Network.Lemmas.Precondition
import all Guarded2Network.PlusCal

@[expose] public section

/-!
  One atomic branch, compiled.

  `stepBranch` (`Guarded2Network/PlusCal.lean`) does two things to a branch: it walks the
  precondition with `processPrecondition`, and it converts the action block statement by statement
  with `convertActionStmt` — prepending the consumption assignments the walk hoisted out to the
  *action* block rather than leaving them where the `receive`s were.

  So this file is two lemmas and their composition. `actionBlock_refines` lifts
  `Lemmas/Statement.lean`'s per-statement `action_refines` over a whole block, which is one
  `StrongRefinement.Comp` per statement and nothing more — the action language is unchanged by this
  pass, so no reordering is involved. `Lemmas/Precondition.lean`'s `processPrecondition_spec` covers
  the other half. Composing them is where the assignments move from the precondition's right edge
  (where the precondition triple leaves them) to the action block's left edge (where the pass
  actually puts them), which is one associativity step.

  Freshness stays a hypothesis here, as it does at every level of this proof: these are syntactic
  conditions on the source program and on the pass's generated `inbox`, and discharging them needs
  the passes before this one (type checking, well-formedness). Prior art carries them the same way,
  as fields of a per-level `wellFormed` structure.
-/

namespace Guarded2Network

open GuardedPlusCal (Block ChanKey LocalState' Trace)

variable {V : Type} [ComputableTLAPlus.ExprSemantics V] [SeqBuiltins V]

/-- `Block.map` distributes over `cons`, and leaves `end` alone. Both hold by `rfl` — `Block.map`
rewrites `begin` pointwise and `last` once — and are named so that a `cons_end_induct` over a
mapped block can rewrite rather than unfold. -/
@[simp] theorem Block.map_end {α β : Bool → Type} {f : ⦃b : Bool⦄ → α b → β b} {b : Bool} {S : α b} :
    Block.map f (Block.end S) = Block.end (f S) := rfl

@[simp, inherit_doc Block.map_end]
theorem Block.map_cons {α β : Bool → Type} {f : ⦃b : Bool⦄ → α b → β b} {b : Bool}
    {S : α false} {B : Block α b} :
    Block.map f (Block.cons S B) = Block.cons (f S) (Block.map f B) := rfl

omit [SeqBuiltins V] in
/-- **An action block refines, statement by statement.** `action_refines` lifted over a whole block
by one `StrongRefinement.Comp` per statement.

Nothing is reordered and nothing is generated: `convertActionStmt` is a relabelling of the same
statement into the target language, so this is the plain structural lift. All the work of this pass
is in the precondition, which is why that half needed a whole file and this one is an induction.

Divergence is `∅` throughout, as everywhere else in this development — no statement of either
language diverges. -/
theorem actionBlock_refines {mbox : Mailbox} {pref : ChanKey V → List V} {b : Bool}
    {A : Block (ComputableGuardedPlusCal.Statement false) b}
    (fresh : ∀ S ∈ A.begin, Fresh mbox S) (freshLast : Fresh mbox A.last) :
    StrongRefinement (relatesTo (V := V) mbox pref) (instTrace (V := V)).Rτ
      (Block.reducing (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing') A)
      (Block.aborting (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.aborting')
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing') A)
      (Block.diverging (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.diverging')
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing') A)
      (Block.reducing (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing') (A.map (λ ⦃_⦄ ↦ convertActionStmt)))
      (Block.aborting (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.aborting')
        (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing') (A.map (λ ⦃_⦄ ↦ convertActionStmt)))
      (Block.diverging (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.diverging')
        (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing') (A.map (λ ⦃_⦄ ↦ convertActionStmt))) := by
  induction A using Block.cons_end_induct with
  | «end» S =>
    rw [Block.map_end, Block.reducing_end, Block.reducing_end, Block.aborting_end,
      Block.aborting_end, Block.diverging_end, Block.diverging_end]
    exact action_refines S freshLast
  | cons S A IH =>
    rw [Block.map_cons, Block.reducing_cons, Block.reducing_cons, Block.aborting_cons,
      Block.aborting_cons, Block.diverging_cons, Block.diverging_cons]
    exact StrongRefinement.Comp _ (action_refines S (fresh S List.mem_cons_self))
      (IH (λ S' hS' ↦ fresh S' (List.mem_cons_of_mem _ hS')) freshLast)

/-- **The two halves of a branch, joined.** The precondition's refinement (as
`processPrecondition_spec` leaves it, with the hoisted assignments on its right edge) composed with
the action block's, against the branch the pass actually builds — which carries those assignments on
the action block's *left* edge instead.

`Block.reducing_prepend'`/`Block.aborting_prepend` are what say those are the same relation; after
them the join is one `StrongRefinement.Comp` and an associativity step. Stated separately from the
triple below because it is the whole mathematical content of that triple: everything else there is
`mvcgen` walking the pass's state bookkeeping, which no refinement depends on. -/
private theorem branch_refines {mbox : Mailbox} {pref : ChanKey V → List V}
    {Br : ComputableGuardedPlusCal.AtomicBranch}
    {pre' : Option (Block (ComputableNetworkPlusCal.Statement true) false)}
    {assigns : List (ComputableNetworkPlusCal.Statement false false)}
    (hpre : StrongRefinement (relatesTo (V := V) mbox pref) (instTrace (V := V)).Rτ
      (Br.precondition.elim Relation.Idle (Block.reducing (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing')))
      (Br.precondition.elim ∅ (Block.aborting (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.aborting')
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing')))
      ∅
      (pre'.elim Relation.Idle (Block.reducing (β := λ _ ↦ LocalState' V)
          (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing')) ∘ᵣ₂
        NetworkPlusCal.Statement.listReducing' assigns)
      (pre'.elim ∅ (Block.aborting (β := λ _ ↦ LocalState' V)
          (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.aborting')
          (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing')) ∪
        pre'.elim Relation.Idle (Block.reducing (β := λ _ ↦ LocalState' V)
            (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing')) ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting' assigns)
      ∅)
    (afresh : ∀ S ∈ Br.action.begin, Fresh mbox S) (alast : Fresh mbox Br.action.last) :
    StrongRefinement (relatesTo (V := V) mbox pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.AtomicBranch.reducing' Br) (GuardedPlusCal.AtomicBranch.aborting' Br) ∅
      (NetworkPlusCal.AtomicBranch.reducing' ⟨pre',
        Block.prepend assigns (Br.action.map (λ ⦃_⦄ ↦ convertActionStmt))⟩)
      (NetworkPlusCal.AtomicBranch.aborting' ⟨pre',
        Block.prepend assigns (Br.action.map (λ ⦃_⦄ ↦ convertActionStmt))⟩)
      ∅ := by
  have hcomp := StrongRefinement.Comp _ hpre (actionBlock_refines (V := V) afresh alast)
  -- `union_lcomp₂` normalizes `Comp`'s output, not the goal: the goal is already in its right-hand
  -- form once `Block.aborting_prepend` has split the prepended assignments off
  simp only [GuardedPlusCal.Block.diverging'_eq_empty, NetworkPlusCal.Block.diverging'_eq_empty,
    Relation.lcomp₁.right_empty_eq_empty, Set.union_self, Set.empty_union,
    Relation.lcomp₁.union_lcomp₂] at hcomp
  simp only [GuardedPlusCal.AtomicBranch.reducing', GuardedPlusCal.AtomicBranch.aborting'_eq,
    NetworkPlusCal.AtomicBranch.reducing', NetworkPlusCal.AtomicBranch.aborting'_eq,
    Block.reducing_prepend', Block.aborting_prepend, Relation.lcomp₂.assoc]
  exact hcomp

/-- Every thread of a list is a receive loop on this `inbox`, rather than arbitrary code. Stated on
the bare list rather than on `ThreadState` because `Thread.toNetwork` hands the accumulator's
`rxThreads` back as a plain list, and the levels above it never see the state again. -/
def RxOnly (inbox : String) (Ts : List ComputableNetworkPlusCal.Thread) : Prop :=
  ∀ T ∈ Ts, ∃ chan label τ, T = .rx chan label τ inbox

/-- Every thread the pass has put in `rxThreads` is an `.rx` on this call's `inbox`. `stepBranch` is
the only place one is ever appended, so this is where the fact has to be established; the thread
level is where it is needed, since `Thread.toNetwork` hands `rxThreads` back as threads and what
makes that sound is that each is a receive loop rather than arbitrary code. -/
private def RxThreads (inbox : String) (st : ThreadState) : Prop :=
  RxOnly inbox st.rxThreads

/-- What one compiled branch owes its source: the refinement, and agreement on where the branch
goes next. Named because the block level quantifies over it — a compiled block's branches are
pairwise this, `List.Forall₂`-style — and a bare `StrongRefinement` conjunction cannot be the
argument of a relation combinator. -/
structure BranchRefines (mbox : Mailbox) (pref : ChanKey V → List V)
    (Br : ComputableGuardedPlusCal.AtomicBranch)
    (Br' : ComputableNetworkPlusCal.AtomicBranch) : Prop where
  /-- The branch refines its source, precondition and action block together. -/
  refines : StrongRefinement (relatesTo (V := V) mbox pref) (instTrace (V := V)).Rτ
    (GuardedPlusCal.AtomicBranch.reducing' Br) (GuardedPlusCal.AtomicBranch.aborting' Br) ∅
    (NetworkPlusCal.AtomicBranch.reducing' Br') (NetworkPlusCal.AtomicBranch.aborting' Br') ∅
  /-- And it leaves for the same place: `Block.prepend` does not touch `last`, and
  `convertActionBlock` maps it pointwise, so a terminal `goto` survives compilation unchanged. -/
  last_eq : Br'.action.last = convertActionStmt Br.action.last

open Std.Do in
/-- **One branch, compiled.** The two halves composed: `processPrecondition_spec` for the
precondition, `actionBlock_refines` for the action block, and one `StrongRefinement.Comp` joining
them.

The composition is where the consumption assignments change hands. `processPrecondition_spec`
leaves them on the *precondition's* right edge, which is where the reorder lemmas put them; the pass
puts them on the *action block's* left edge (`Block.prepend`). `Block.reducing_prepend'` is what
says those are the same relation, and after it the join is associativity.

`Br'.action.last` is reported alongside: `Block.prepend` does not touch `last` and
`convertActionBlock` maps it pointwise, so a branch's terminal `goto` survives compilation
unchanged. That is what the block level needs to know its branches still agree on where they go. -/
private theorem stepBranch_spec {chans : Guarded2NetworkChans}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V}
    {Br : ComputableGuardedPlusCal.AtomicBranch}
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ preconditionList Br.precondition →
        c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : ∀ S ∈ preconditionList Br.precondition, Fresh (.some (c₀, inbox)) S)
    (pfresh : PairsFresh inbox (preconditionList Br.precondition))
    (afresh : ∀ S ∈ Br.action.begin, Fresh (.some (c₀, inbox)) S)
    (alast : Fresh (.some (c₀, inbox)) Br.action.last) :
    ⦃λ st ↦ ⌜RxThreads inbox st⌝⦄
    stepBranch (m := G2NM) chans inbox Br
    ⦃⇓? Br' st' =>
      ⌜BranchRefines (V := V) (.some (c₀, inbox)) pref Br Br' ∧ RxThreads inbox st'⌝⦄ := by
  mvcgen [stepBranch, processPrecondition_spec, freshName, MonadFresh.fresh]
  with {
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact branch_refines ‹_› afresh alast
    · rfl
    -- `or_imp`/`forall_and` split the appended `.rx` off the accumulated list; the branch that
    -- registers a new channel is the only one where the two halves differ
    · simp_all [RxThreads, RxOnly, or_imp, forall_and]
  }

/-! ## Owed: `stepBranch_spec`

  Written against `GuardedPlusCal.Thread.toNetwork_spec₁` in the prior development, which is the
  model — not `processPrecondition_spec₁`, the trivial one next to it.

  The shape: `mvcgen`, then supply the loop invariants at the `case inv1`/`inv2` goals as
  `⇓ (_, ⟨_, _, rxs⟩) => ⌜…⌝`. That is where `ThreadState` enters, and it is what a postcondition of
  bare existentials leaves out. The invariant to carry is prior art's — every thread accumulated in
  `rxThreads` is an `.rx` — alongside the branch's own shape, `processPrecondition`'s rewritten
  precondition paired with the converted action block carrying the hoisted assignments on its left
  edge.

  One mechanical fact worth not rediscovering: `⇓` is `PostCond.noThrow`, so under `G2NM`'s `except`
  shape every postcondition here is a `⇓?`.
-/

end Guarded2Network

end
