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
