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
  the passes before this one (type checking, well-formedness).
-/

namespace Guarded2Network

open GuardedPlusCal (Block ChanKey LocalState Trace)

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
      (Block.reducing
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing) A)
      (Block.aborting
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.aborting)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing) A)
      (Block.diverging
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.diverging)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing) A)
      (Block.reducing
        (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing) (A.map (λ ⦃_⦄ ↦ convertActionStmt)))
      (Block.aborting
        (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.aborting)
        (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing) (A.map (λ ⦃_⦄ ↦ convertActionStmt)))
      (Block.diverging
        (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.diverging)
        (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing) (A.map (λ ⦃_⦄ ↦ convertActionStmt))) := by
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

omit [SeqBuiltins V] in
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
      (Br.precondition.elim Relation.Idle (Block.reducing
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing)))
      (Br.precondition.elim ∅ (Block.aborting
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.aborting)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing)))
      ∅
      (pre'.elim Relation.Idle (Block.reducing
          (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing)) ∘ᵣ₂
        NetworkPlusCal.Statement.listReducing assigns)
      (pre'.elim ∅ (Block.aborting
          (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.aborting)
          (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing)) ∪
        pre'.elim Relation.Idle (Block.reducing
            (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing)) ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting assigns)
      ∅)
    (afresh : ∀ S ∈ Br.action.begin, Fresh mbox S) (alast : Fresh mbox Br.action.last) :
    StrongRefinement (relatesTo (V := V) mbox pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.AtomicBranch.reducing Br) (GuardedPlusCal.AtomicBranch.aborting Br) ∅
      (NetworkPlusCal.AtomicBranch.reducing ⟨pre',
        Block.prepend assigns (Br.action.map (λ ⦃_⦄ ↦ convertActionStmt))⟩)
      (NetworkPlusCal.AtomicBranch.aborting ⟨pre',
        Block.prepend assigns (Br.action.map (λ ⦃_⦄ ↦ convertActionStmt))⟩)
      ∅ := by
  have hcomp := StrongRefinement.Comp _ hpre (actionBlock_refines (V := V) afresh alast)
  -- `union_lcomp₂` normalizes `Comp`'s output, not the goal: the goal is already in its right-hand
  -- form once `Block.aborting_prepend` has split the prepended assignments off
  simp only [GuardedPlusCal.Statement.blockDiverging_eq_empty, NetworkPlusCal.Statement.blockDiverging_eq_empty,
    Relation.lcomp₁.right_empty_eq_empty, Set.union_self, Relation.lcomp₁.union_lcomp₂] at hcomp
  simp only [GuardedPlusCal.AtomicBranch.reducing, GuardedPlusCal.AtomicBranch.aborting_eq,
    NetworkPlusCal.AtomicBranch.reducing, NetworkPlusCal.AtomicBranch.aborting_eq,
    GuardedPlusCal.Statement.blockReducing, GuardedPlusCal.Statement.blockAborting,
    NetworkPlusCal.Statement.blockReducing, NetworkPlusCal.Statement.blockAborting,
    Block.reducing_prepend', Block.aborting_prepend, Relation.lcomp₂.assoc]
  exact hcomp

/-- Every thread of a list is a receive loop on this process's channel and `inbox`, under a label the
pass generated. Stated on the bare list rather than on `ThreadState` because `Thread.toNetwork` hands
the accumulator's `rxThreads` back as a plain list, and the levels above it never see the state
again.

All three extra conjuncts ride along for the same reason the rest does: `stepBranch` is the only
place a receiving thread is ever appended, so it is the only place any of them can be established.
The process level is what spends them. `Generated` keeps a receiving thread's label out of the
source's, or a code thread could be scheduled at it. `c₀` makes the mailbox the algorithm level
assigns the process name the same channel its receiving thread drains — a process has only one
channel (`BranchesFresh.rfresh`), so there is only one to name. `mbox = .some (c₀, inbox)` rules out
the other mailbox: a thread is registered only for a branch that receives, and a branch that receives
is what `BranchesFresh.mbox_some` says has a mailbox at all. And the channel does not mention the
generated name, which is `ReceiveFresh`'s first clause and what `ProcessRefines.rxThread` reports it
for — a relay resolves its channel in a memory the relay itself is about to write `inbox` in.
`algRelatesTo.step_or_stutter`/`.immediateAbort` read it off `rxThread` at the resolved instance. -/
def IsRxThread (mbox : Mailbox) (c₀ : ComputableGuardedPlusCal.Ref) (inbox : String)
  (T : ComputableNetworkPlusCal.Thread) : Prop :=
    mbox = .some (c₀, inbox) ∧ inbox ∉ GuardedPlusCal.Ref.freeVars c₀ ∧
      ∃ label τ, T = .rx c₀ label τ inbox ∧ Generated "rx" label

@[inherit_doc IsRxThread]
def RxOnly (mbox : Mailbox) (c₀ : ComputableGuardedPlusCal.Ref) (inbox : String)
  (Ts : List ComputableNetworkPlusCal.Thread) : Prop :=
    ∀ T ∈ Ts, IsRxThread mbox c₀ inbox T

/-- **One entry of the locals list the pass invents**: the `inbox`, declared as a sequence and
initialized empty.

Owed to `Algorithm.init`, which is the only thing that reads it: a compiled instance's memory has to
bind `inbox` to something `isSeq`-related to the empty inbox contents, and this is what says the
declaration puts it there. -/
def InboxLocal (inbox : String)
    (e : String × ComputableTLAPlus.Typ × Bool ×
      Option (Bool × ComputablePlusCal.Expression)) : Prop :=
  ∃ τ, e = (inbox, .seq τ, false, some (true, .seq [] τ))

/-- The same declaration after `GuardedPlusCal.initsOf` has kept only what `InitProc` reads — the
name and the initializer. The type annotation and the constant flag play no part in what an initial
memory is, so this is all `Algorithm.init` ever sees of the local the pass declares. -/
def InboxInit (inbox : String) (ne : String × ComputablePlusCal.Expression) : Prop :=
  ∃ τ, ne = (inbox, .seq [] τ)

/-- `initOf` keeps an `InboxLocal` and turns it into an `InboxInit` — the one step between the two
definitions above, and the reason neither has to be unfolded where they meet. -/
theorem initOf_inboxLocal {inbox : String}
    {e : String × ComputableTLAPlus.Typ × Bool × Option (Bool × ComputablePlusCal.Expression)}
    (h : InboxLocal inbox e) :
    ∃ ne, GuardedPlusCal.initOf e = .some ne ∧ InboxInit inbox ne := by
  obtain ⟨τ, rfl⟩ := h
  exact ⟨_, rfl, τ, rfl⟩

/-- What the pass has put in its accumulator: every thread in `rxThreads` is an `.rx` on this call's
channel and `inbox`, every entry in `newLocals` is that `inbox`'s declaration, and the two lists are
empty together.

`stepBranch` is the only place either list is ever appended to, so this is where all three have to be
established. The thread level is where the first is needed — `Thread.toNetwork` hands `rxThreads`
back as threads, and what makes that sound is that each is a receive loop rather than arbitrary code.
The other two are `Algorithm.init`'s: a process that receives is compiled with an `inbox` to receive
into, and one that does not is compiled with no extra local at all, so its memory is the source's.

The third is what ties them, and it needs no ghost: `stepBranch` appends to both lists or to neither,
so "empty together" is an invariant of the state rather than a fact about the walk so far. -/
private def RxThreads (mbox : Mailbox) (c₀ : ComputableGuardedPlusCal.Ref) (inbox : String)
    (st : ThreadState) : Prop :=
  RxOnly mbox c₀ inbox st.rxThreads ∧ (∀ e ∈ st.newLocals, InboxLocal inbox e) ∧
    (st.newLocals = [] ↔ st.rxThreads = [])

/-- **A branch that receives at all** — what makes the pass register a receiving thread, and so what
the registration fact is conditioned on.

Existential where `BranchesFresh`'s fields are universal, and the difference is not cosmetic: those
are hypotheses, discharged once per `receive` a branch has, while this is what a *conclusion* is
conditioned on, and one `receive` is all it takes. -/
def BranchReceives (Br : ComputableGuardedPlusCal.AtomicBranch) : Prop :=
  ∃ c r coe, GuardedPlusCal.Statement.receive c r coe ∈ preconditionList Br.precondition

/-- **The registration fact, in the form that survives a walk.** `H` is whatever the caller already
knows has registered a thread — everything walked before this call — and each level hands back
`Registered (H ∨ ‹this step receives›)`, so the fact accumulates along the walk instead of being
re-established at each step.

The parameter is what makes that possible at all. A Hoare postcondition cannot mention the pre-state,
so "and the list was already non-empty" — which is what every step but the first needs — has nowhere
else to enter. It leaves again at `mapM_stepBlock_spec_run`, instantiated at `False`: a thread's walk
starts at `{}`, whose `rxThreads` is `[]`, so there is nothing yet to have registered.

Kept out of `RxThreads` deliberately, though both are state predicates threaded the same way.
`RxThreads` is unfolded into the `simp` set at every level; this is not, and an opaque implication is
what keeps `H` pinned by unification against the loop invariant rather than shredded into the
surrounding goal. -/
private def Registered (H : Prop) (st : ThreadState) : Prop := H → st.rxThreads ≠ []

/-- What one compiled branch owes its source: the refinement, and agreement on where the branch
goes next. Named because the block level quantifies over it — a compiled block's branches are
pairwise this, `List.Forall₂`-style — and a bare `StrongRefinement` conjunction cannot be the
argument of a relation combinator. -/
structure BranchRefines (mbox : Mailbox) (pref : ChanKey V → List V)
    (Br : ComputableGuardedPlusCal.AtomicBranch)
    (Br' : ComputableNetworkPlusCal.AtomicBranch) : Prop where
  /-- The branch refines its source, precondition and action block together. -/
  refines : StrongRefinement (relatesTo (V := V) mbox pref) (instTrace (V := V)).Rτ
    (GuardedPlusCal.AtomicBranch.reducing Br) (GuardedPlusCal.AtomicBranch.aborting Br) ∅
    (NetworkPlusCal.AtomicBranch.reducing Br') (NetworkPlusCal.AtomicBranch.aborting Br') ∅
  /-- And it leaves for the same place: `Block.prepend` does not touch `last`, and
  `convertActionBlock` maps it pointwise, so a terminal `goto` survives compilation unchanged. -/
  last_eq : Br'.action.last = convertActionStmt Br.action.last

/-- **What a whole label's worth of branches owes**: every compiled branch is *some* source branch,
refined. Deliberately weaker than the positional `List.Forall₂` a single compiled block satisfies.

Positional pairing is more than any consumer uses — `blockRefines_step` only ever asks for some
source branch matching the target one it was handed, which is `Forall₂.exists_left` — and it is more
than a *label* can supply. `Process.codeTable` lets a label denote the union of every block carrying
it, and nothing in the front end rejects two blocks with one label, so the branch lists at a label
are concatenations rather than a pair of aligned lists. This is what survives that. -/
def BranchesRefine (mbox : Mailbox) (pref : ChanKey V → List V)
  (brs : List ComputableGuardedPlusCal.AtomicBranch)
  (brs' : List ComputableNetworkPlusCal.AtomicBranch) : Prop :=
    ∀ Br' ∈ brs', ∃ Br ∈ brs, BranchRefines (V := V) mbox pref Br Br'

omit [SeqBuiltins V] in
/-- One compiled block's branches, as a whole label's worth — the positional form forgetting its
positions. -/
theorem BranchesRefine.of_forall₂ {mbox : Mailbox} {pref : ChanKey V → List V}
    {brs : List ComputableGuardedPlusCal.AtomicBranch}
    {brs' : List ComputableNetworkPlusCal.AtomicBranch}
    (h : List.Forall₂ (BranchRefines (V := V) mbox pref) brs brs') :
    BranchesRefine (V := V) mbox pref brs brs' :=
  λ _ hBr' ↦ h.exists_left hBr'

/-- **The locals list `stepBranch` leaves still holds only `inbox` declarations** — it either kept the
one it had or appended this call's.

Standalone rather than a step inside the proof below, where the goal is over a pair-typed list and
the statement would be split per component. -/
private theorem inboxLocal_ite {inbox : String} {τ : ComputableTLAPlus.Typ}
    {l : List (String × ComputableTLAPlus.Typ × Bool ×
      Option (Bool × ComputablePlusCal.Expression))} (h : ∀ e ∈ l, InboxLocal inbox e) :
    ∀ e ∈ (if l.isEmpty then l.concat (inbox, .seq τ, false, some (true, .seq [] τ)) else l),
      InboxLocal inbox e := by
  split
  · intro e he
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact h e he
    · exact ⟨τ, rfl⟩
  · exact h

/-- A branch that registers leaves the locals list non-empty: it appended to it, or it was already
non-empty and that is why it did not. -/
private theorem ite_isEmpty_concat_ne_nil {α : Type} (l : List α) (a : α) :
    (if l.isEmpty then l.concat a else l) ≠ [] := by
  split
  · simp
  · simp_all

/-- And a list some element of which matched a guard is not empty — the shape the receiving-thread
list is in on the branch where `stepBranch` found a thread for this channel already registered. -/
private theorem ne_nil_of_any {α : Type} {l : List α} {p : α → Bool} (h : l.any p = true) :
    l ≠ [] := by
  rintro rfl
  simp at h

/-- A list of channel/type pairs that is not a cons is empty — the shape `stepBranch`'s `if let`
leaves behind when the precondition walk recorded no channel. -/
private theorem eq_nil_of_not_cons
    {l : List (ComputableGuardedPlusCal.Ref × ComputableTLAPlus.Typ)}
    (h : ∀ chan τ tail, l ≠ (chan, τ) :: tail) : l = [] :=
  match l with
  | [] => rfl
  | (chan, τ) :: tail => (h chan τ tail rfl).elim

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
unchanged. That is what the block level needs to know its branches still agree on where they go.

And `Registered`: a branch that receives leaves a receiving thread registered, and one that was
registered before this branch stays registered. This is the only place either can be established —
`stepBranch` is the sole writer of `rxThreads` — and the process level is what spends them, to know
that a source process which receives is compiled to one with a thread to drain its channel. -/
private theorem stepBranch_spec {chans : Guarded2NetworkChans} {mbox : Mailbox}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V} {H : Prop}
    {Br : ComputableGuardedPlusCal.AtomicBranch}
    (hmb : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ preconditionList Br.precondition →
        mbox = .some (c₀, inbox))
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ preconditionList Br.precondition →
        c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : ∀ S ∈ preconditionList Br.precondition, Fresh mbox S)
    (pfresh : PairsFresh inbox (preconditionList Br.precondition))
    (afresh : ∀ S ∈ Br.action.begin, Fresh mbox S)
    (alast : Fresh mbox Br.action.last) :
    ⦃λ st ↦ ⌜RxThreads mbox c₀ inbox st ∧ Registered H st⌝⦄
    stepBranch (m := G2NM) chans inbox Br
    ⦃⇓? Br' st' =>
      ⌜BranchRefines (V := V) mbox pref Br Br' ∧ RxThreads mbox c₀ inbox st' ∧
        Registered (H ∨ BranchReceives Br) st'⌝⦄ := by
  mvcgen [stepBranch, processPrecondition_spec, freshName, MonadFresh.fresh]
  with {
    -- the precondition, split: three conjuncts below would otherwise find it before
    -- `processPrecondition_spec`'s postcondition, which is the one that is three deep
    obtain ⟨⟨hrx₀, hloc₀, hboth₀⟩, hreg⟩ := ‹RxThreads _ _ _ _ ∧ Registered _ _›
    -- `processPrecondition_spec`'s postcondition arrives as one unsplit conjunction: what the walk
    -- recorded about the channels, that a `receive` leaves `rxs` non-empty, and the refinement
    obtain ⟨hrxs, hrecv, href⟩ := ‹_ ∧ _ ∧ _›
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact branch_refines href afresh alast
    · rfl
    -- `or_imp`/`forall_and` split the appended `.rx` off the accumulated list; `IsRxThread` stays
    -- out of the simp set, one obligation per thread. The locals hypotheses are cleared first, so
    -- `simp_all` does not shred a pair-typed `∀ e ∈ …` it has no use for here.
    · clear hloc₀ hboth₀
      simp_all [RxOnly, or_imp, forall_and]
      -- what is left is the single new thread, at the label `freshName` just handed it: the mailbox
      -- `simp_all` already rewrote to the right one, the channel's freshness is in context
      all : refine ⟨rfl, ?_, _, _, rfl, _, rfl⟩
      all : simp_all
    -- the locals list: unchanged where nothing was registered, `inboxLocal_ite` where it was
    · clear href
      first
        | exact hloc₀
        | exact inboxLocal_ite hloc₀
    -- and the two lists stay empty together — where one grew so did the other, so both are non-empty
    · clear href
      first
        | exact hboth₀
        | (refine iff_of_false (ite_isEmpty_concat_ne_nil _ _) ?_
           first
             | exact ne_nil_of_any ‹_›
             | simp)
    · rintro (hH | ⟨c, r, coe, hmem⟩) hnil
      -- the carried half: a list this step found non-empty it also leaves non-empty, since the only
      -- thing done to it is a `concat`
      · refine hreg hH ?_
        simp_all
      -- and the half this step establishes, at the one case that is not already contradictory: the
      -- `if let` found no channel to register, which `hrecv` rules out for a branch that receives
      · refine hrecv c r coe hmem (eq_nil_of_not_cons ?_)
        simp_all
  }

end Guarded2Network

end
