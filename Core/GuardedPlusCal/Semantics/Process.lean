module

public import Core.GuardedPlusCal.Semantics.Denotational
public import Mathlib.Order.FixedPoints
public import Mathlib.Tactic.Monotonicity

@[expose] public section

/-!
  The process and algorithm layers, following `reference/jlamp.pdf` §3.3.

  Nothing here mentions either language's AST. A thread has no denotation of its own — it only owns
  labels — and a process is scheduled entirely by label, so the whole layer is parameterized by two
  things: a **code table** saying what the block at each label does, and, per process, the set of
  labels that process owns. Both `GuardedPlusCal` and `NetworkPlusCal` build those from their own
  syntax and instantiate what follows; `NetworkPlusCal`'s table additionally answers for its `.rx`
  threads' labels, which is the only way the two languages differ at this level.

  Processes are indexed by an arbitrary `ι` rather than by a `Process` value. The paper writes the
  algorithm state as a set of pairs `⟨P, σ⟩` and updates it with `Ps \ {⟨P,σ⟩} ∪ {⟨P,σ'⟩}`, which
  needs `P` only as a name to pair the state with.

  The three algorithm-level semantics are fixed points of monotone endofunctions on the relation:
  least for terminating and aborting behaviour, greatest for divergence.
-/

namespace GuardedPlusCal

open ComputableTLAPlus (Memory ExprSemantics)

variable {V : Type} {ι : Type}

/-- The trace alphabet: a sequence of observable events. `Extra/List.lean`'s `Monoid (List α)` makes
it the paper's `⟨T, *, ε, ≤⟩`. -/
abbrev Trace (V : Type) : Type := List (Behavior V)

/-- The name a process instance's own identity is bound to, matching `Elaborator/PlusCal.lean`'s
`extend "self" .address`. -/
def selfName : String := "self"

/-- A process state: the process's local memory together with the set of labels currently scheduled
for execution — at most one per thread, though nothing here enforces that. The paper's
`PState = (Var → Value) × 𝒫(Labels)`. -/
abbrev ProcState (V : Type) : Type := Memory V × Set String

/-- A process's full state, including the channels it can see. Channels are global, so the algorithm
layer threads one copy through every process rather than giving each its own. -/
abbrev ProcConfig (V : Type) : Type := ProcState V × FIFOs V

/-- The paper's `Ξₚ`: what the atomic block at each label does. Two relations rather than one,
because a block can step or go wrong; there is no third, since a block never diverges (its
non-terminating semantics is empty, every statement being a single step).

A label with no block maps to `∅` in both, which makes it unschedulable rather than an error. -/
structure CodeTable (V : Type) : Type where
  /-- Where the block at this label can step to, and what it emits. -/
  reducing : String → Set (LocalState V false × Trace V × LocalState V true)
  /-- Where the block at this label goes wrong. -/
  aborting : String → Set (LocalState V false × Trace V)

/-! # Processes -/

/-- One step of a process: pick a scheduled label the process owns, run the block at that label, and
replace the label with the one the block's terminal `goto` reached.

`self` is the process instance's identity. The paper's `self ↦ p ∈ M` side condition appears here as
a lookup: a process only steps in a memory that binds its own identity, which `initProc` establishes
and no step disturbs. -/
def CodeTable.procReducing (Ξ : CodeTable V) (owned : Set String) (self : V) :
    Set (ProcConfig V × Trace V × ProcConfig V) :=
  {⟨⟨⟨M, L⟩, F⟩, τ, ⟨⟨M', L'⟩, F'⟩⟩ | ∃ l ∈ L ∩ owned, ∃ l',
    ⟨LocalState.running M F, τ, LocalState.done M' F' l'⟩ ∈ Ξ.reducing l ∧
    M.lookup selfName = .some self ∧
    L' = insert l' (L \ {l})}

/-- A process goes wrong when the block at one of its scheduled labels does. -/
def CodeTable.procAborting (Ξ : CodeTable V) (owned : Set String) (self : V) :
    Set (ProcConfig V × Trace V) :=
  {⟨⟨⟨M, L⟩, F⟩, τ⟩ | ∃ l ∈ L ∩ owned,
    ⟨LocalState.running M F, τ⟩ ∈ Ξ.aborting l ∧ M.lookup selfName = .some self}

/-- A process never diverges *in one step*: its semantics is one execution of one atomic block, and
an atomic block's non-terminating semantics is empty. Divergence is an algorithm-level notion, and
appears below as a greatest fixed point over infinitely many process steps. -/
def CodeTable.procDiverging (_Ξ : CodeTable V) (_owned : Set String) (_self : V) :
    Set (ProcConfig V × Trace V) := ∅

/-! # Algorithms -/

/-- An algorithm state: every process instance paired with its own state, plus the shared channels.
-/
abbrev AlgState (ι V : Type) : Type := Set (ι × ProcState V) × FIFOs V

/-- Everything the algorithm layer needs to know about its processes: which labels each owns, what
the block at each label does, and each instance's identity. -/
structure Algebra (ι V : Type) : Type where
  /-- The code table in force for a given process instance. -/
  table : ι → CodeTable V
  /-- The labels a given process instance owns, across all of its threads. -/
  owned : ι → Set String
  /-- A given process instance's identity, the value bound to `self`. -/
  self : ι → V

/-- The paper's `P*_red`: one step of one process, chosen non-deterministically, with every other
process and the channels carried through. -/
def Algebra.step (A : Algebra ι V) : Set (AlgState ι V × Trace V × AlgState ι V) :=
  {⟨⟨Ps, F⟩, τ, ⟨Ps', F'⟩⟩ | ∃ p σ, ⟨p, σ⟩ ∈ Ps ∧ ∃ σ',
    ⟨⟨σ, F⟩, τ, ⟨σ', F'⟩⟩ ∈ (A.table p).procReducing (A.owned p) (A.self p) ∧
    Ps' = insert ⟨p, σ'⟩ (Ps \ {⟨p, σ⟩})}

/-- The identity relation on algorithm states, emitting nothing. The base case of `Algebra.reducing`:
the empty execution is a finite execution. -/
def Algebra.idle : Set (AlgState ι V × Trace V × AlgState ι V) :=
  {⟨x, τ, y⟩ | x = y ∧ τ = 1}

/-- The paper's `P⊥_red`: either some process goes wrong now, or the algorithm takes a step and goes
wrong later. -/
def Algebra.abortStep (A : Algebra ι V) (X : Set (AlgState ι V × Trace V)) :
    Set (AlgState ι V × Trace V) :=
  {⟨⟨Ps, F⟩, τ⟩ | ∃ p σ, ⟨p, σ⟩ ∈ Ps ∧
    ⟨⟨σ, F⟩, τ⟩ ∈ (A.table p).procAborting (A.owned p) (A.self p)}
  ∪ A.step ∘ᵣ₁ X

theorem Algebra.abortStep_mono (A : Algebra ι V) : Monotone A.abortStep := by
  intro X Y X_sub
  exact Set.union_subset_union_right _ (Relation.lcomp₁.subset_of_subset_right X_sub)

/-- Every **finite** sequence of algorithm steps: the reflexive-transitive closure of
`Algebra.step`, as a least fixed point.

The reflexive disjunct is load-bearing. Without it the endofunction `X ↦ X ∘ᵣ₂ A.step` has `∅` as a
fixed point — every element of a composition needs a witness drawn from `X` — so its *least* fixed
point is `∅` and the semantics of every algorithm would be empty. -/
def Algebra.reducing (A : Algebra ι V) : Set (AlgState ι V × Trace V × AlgState ι V) :=
  OrderHom.lfp {
    toFun := λ X ↦ Algebra.idle ∪ X ∘ᵣ₂ A.step
    monotone' := by
      intro X Y X_sub
      exact Set.union_subset_union_right _ (Relation.lcomp₂.mono X_sub le_rfl)
  }

/-- Every finite sequence of steps ending in a process going wrong. Needs no reflexive disjunct: the
left half of `Algebra.abortStep` does not mention `X`, so it already seeds the iteration. -/
def Algebra.aborting (A : Algebra ι V) : Set (AlgState ι V × Trace V) :=
  OrderHom.lfp { toFun := A.abortStep, monotone' := A.abortStep_mono }

/-- Every infinite sequence of steps, as a *greatest* fixed point. The degeneracy that forces
`Algebra.reducing`'s reflexive disjunct does not arise here: `∅` being a fixed point is irrelevant
when taking the largest one. -/
def Algebra.diverging (A : Algebra ι V) : Set (AlgState ι V × Trace V) :=
  OrderHom.gfp {
    toFun := λ X ↦ A.step ∘ᵣ₁ X
    monotone' := by
      intro X Y X_sub
      exact Relation.lcomp₁.subset_of_subset_right X_sub
  }

/-! # Restricting to executions from the initial state

  The paper's `⟦A⟧*`/`⟦A⟧⊥`/`⟦A⟧∞` are these three relations restricted to executions starting from
  `init(A)`. `init` is a *relation* here, not a function: a process's local variables are given by
  initializer expressions, and evaluation is relational (`ExprSemantics.Eval`), so an algorithm with
  a meaningless initializer has no initial state rather than a junk one.
-/

/-- `InitProc self inits σ` — `σ` is a valid initial state for a process instance with identity
`self`, local variable initializers `inits`, and initial label set `entry`. -/
def InitProc [ExprSemantics V] (self : V) (inits : List (String × ComputablePlusCal.Expression))
    (entry : Set String) (σ : ProcState V) : Prop :=
  ∃ vs : List V,
    List.Forall₂ (λ ie v ↦ ExprSemantics.Eval (AList.singleton selfName self) (Prod.snd ie) v)
      inits vs ∧
    σ.1 = (((inits.map Prod.fst).zip vs).foldl (λ M xv ↦ M.insert xv.1 xv.2)
            (AList.singleton selfName self)) ∧
    σ.2 = entry

/-- Executions of `A` from an initial state satisfying `init`. -/
def Algebra.reducingFrom (A : Algebra ι V) (init : AlgState ι V → Prop) :
    Set (AlgState ι V × Trace V × AlgState ι V) :=
  {x ∈ A.reducing | init x.1}

@[inherit_doc Algebra.reducingFrom]
def Algebra.abortingFrom (A : Algebra ι V) (init : AlgState ι V → Prop) :
    Set (AlgState ι V × Trace V) :=
  {x ∈ A.aborting | init x.1}

@[inherit_doc Algebra.reducingFrom]
def Algebra.divergingFrom (A : Algebra ι V) (init : AlgState ι V → Prop) :
    Set (AlgState ι V × Trace V) :=
  {x ∈ A.diverging | init x.1}

/-! # Instantiating for Guarded PlusCal

  Every `GuardedPlusCal.Thread` is a plain `List AtomicBlock`, so a process owns exactly its blocks'
  labels and a label denotes the union of its block's branches. `NetworkPlusCal` has its own
  instantiation, differing only in that a `.rx` thread contributes one more label
  (`Core/NetworkPlusCal/Semantics/Process.lean`).
-/

/-- Every label a process owns, across all of its threads. -/
def Process.ownedLabels (p : ComputableGuardedPlusCal.Process) : Set String :=
  {l | ∃ T ∈ p.threads, ∃ B ∈ T, B.label = l}

/-- The label each thread starts at — the paper's `init(Tᵢ)`, the first block in program order. A
thread with no blocks contributes nothing and is simply never scheduled. -/
def Process.entryLabels (p : ComputableGuardedPlusCal.Process) : Set String :=
  {l | ∃ T ∈ p.threads, ∃ B, T.head? = .some B ∧ B.label = l}

/-- The paper's `Ξₚ`: a label denotes the union of its block's branches. A label the process does not
own denotes `∅` in both components, making it unschedulable. -/
def Process.codeTable [ExprSemantics V] (p : ComputableGuardedPlusCal.Process) : CodeTable V where
  reducing l :=
    {x | ∃ T ∈ p.threads, ∃ B ∈ T, B.label = l ∧ ∃ Br ∈ B.branches, x ∈ AtomicBranch.reducing Br}
  aborting l :=
    {x | ∃ T ∈ p.threads, ∃ B ∈ T, B.label = l ∧ ∃ Br ∈ B.branches, x ∈ AtomicBranch.aborting Br}

end GuardedPlusCal

end
