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
  pass, so no reordering is involved. `Lemmas/Precondition.lean`'s `processPrecondition_refines`
  covers the other half. Composing them is where the assignments move from the precondition's right
  edge (where the precondition lemma leaves them) to the action block's left edge (where the pass
  actually puts them), which is one associativity step.

  Freshness stays a hypothesis here, as it does at every level of this proof: these are syntactic
  conditions on the source program and on the pass's generated `inbox`, and discharging them needs
  the passes before this one (type checking, well-formedness). Prior art carries them the same way,
  as fields of a per-level `wellFormed` structure.
-/

namespace Guarded2Network

open GuardedPlusCal (Block LocalState' Trace)

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
theorem actionBlock_refines {mbox : Mailbox} {b : Bool}
    {A : Block (ComputableGuardedPlusCal.Statement false) b}
    (fresh : ∀ S ∈ A.begin, Fresh mbox S) (freshLast : Fresh mbox A.last) :
    StrongRefinement (relatesTo (V := V) mbox) (instTrace (V := V)).Rτ
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

/-- The statements of a branch's precondition, `[]` when it has none. What every freshness
hypothesis below quantifies over — `Block.toList` cannot, an `Option` having no `toList` of the
right shape. -/
def preconditionList
    (pre : Option (Block (ComputableGuardedPlusCal.Statement true) false)) :
    List (ComputableGuardedPlusCal.Statement true false) :=
  pre.elim [] Block.toList

/-- **A branch's precondition refines, present or absent.** `processPrecondition_refines` with the
`none` case filled in, so that the branch-level composition below is a single `Comp` rather than a
case split repeated on both halves.

The absent case is not degenerate-by-convention: a branch with no precondition compiles to no
guards, no assignments and no receives (`processPrecondition_none`), so both sides are
`Relation.Idle` and the refinement is `Terminating.Id`. That is also why `AtomicBranch.reducing`
composes the missing precondition with the identity relation rather than with `∅`. -/
private theorem precondition_refines {chans : Guarded2NetworkChans}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
    {pre : Option (Block (ComputableGuardedPlusCal.Statement true) false)}
    {pre' : Option (Block (ComputableNetworkPlusCal.Statement true) false)}
    {assigns : List (ComputableNetworkPlusCal.Statement false false)}
    {rxs : List (ComputableGuardedPlusCal.Ref × ComputableTLAPlus.Typ)} {n n' : Nat}
    (h : ((processPrecondition (m := G2NM) chans inbox pre).run.run n) =
      (.ok (pre', assigns, rxs), n'))
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ preconditionList pre →
        c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : ∀ S ∈ preconditionList pre, Fresh (.some (c₀, inbox)) S)
    (pfresh : PairsFresh inbox (preconditionList pre)) :
    StrongRefinement (relatesTo (V := V) (.some (c₀, inbox))) (instTrace (V := V)).Rτ
      (pre.elim Relation.Idle (Block.reducing (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing')))
      (pre.elim ∅ (Block.aborting (β := λ _ ↦ LocalState' V)
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
      ∅ := by
  cases pre with
  | none =>
    rw [processPrecondition_none] at h
    injections
    subst_vars
    rw [Option.elim, Option.elim, Option.elim, Option.elim,
      NetworkPlusCal.Statement.listReducing'_nil, NetworkPlusCal.Statement.listAborting'_nil,
      Relation.lcomp₂.left_id_eq, Relation.lcomp₁.right_empty_eq_empty, Set.empty_union]
    exact StrongRefinement.ofNonDiverging _ (StrongRefinement.Terminating.Id _)
      (StrongRefinement.Aborting.Empty _)
  | some B =>
    obtain ⟨B', rfl⟩ := processPrecondition_isSome h
    have hrefines := processPrecondition_refines (V := V) h rfresh gfresh pfresh
    rwa [GuardedPlusCal.Block.diverging'_eq_empty] at hrefines

/-! ## Owed: `stepBranch_spec`

  Written against `GuardedPlusCal.Thread.toNetwork_spec₁` in the prior development, which is the
  model — not `processPrecondition_spec₁`, the trivial one next to it.

  The shape: `mvcgen`, then supply the loop invariants at the `case inv1`/`inv2` goals as
  `⇓ (_, ⟨_, _, rxs⟩) => ⌜…⌝`. That is where `ThreadState` enters, and it is what a postcondition of
  bare existentials leaves out. The invariant to carry is prior art's — every thread accumulated in
  `rxThreads` is an `.rx` — alongside the branch's own shape, `processPrecondition`'s rewritten
  precondition paired with the converted action block carrying the hoisted assignments on its left
  edge.

  Two mechanical facts established while flailing at this, worth not rediscovering:
  `processPrecondition` must stay opaque to `mvcgen` (unfolding it exposes
  `wp⟦List.mapM (stepStatement …) … { }⟧`, the mapM with `StateT.run` already applied, which
  `Spec.mapM_list` cannot match — it sees the mapM *before* the run); and `⇓` is `PostCond.noThrow`,
  so under `G2NM`'s `except` shape a postcondition needs `(·, ExceptConds.true)` instead.
-/

end Guarded2Network

end
