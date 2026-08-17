module

public import Core.GuardedPlusCal.Semantics.Denotational
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

  The three algorithm-level semantics are closed forms over the algorithm step — `step*`,
  `step* ∘ᵣ₁ immediateAbort`, `step^∞` — rather than fixed points of endofunctions. The refinement
  framework proves one preservation law per operator (`VerifiedCompiler/Denotational/
  StrongRefinement.lean`), so nothing downstream has to unfold a fixed point; the identities with
  the corresponding least fixed points are in `VerifiedCompiler/ClosedForm.lean`, as checks.
-/

namespace GuardedPlusCal

open ComputableTLAPlus (Memory ExprSemantics)

variable {V : Type} {ι : Type}

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
appears below as the infinite iteration of the process step. -/
def CodeTable.procDiverging (_Ξ : CodeTable V) (_owned : Set String) (_self : V) :
    Set (ProcConfig V × Trace V) := ∅

/-! # Algorithms -/

/-- Every process instance paired with its own state. Named apart from `AlgState` so that the
well-formedness condition below — and the refinement invariants that have to carry it — can be
stated about the instances alone; the channels are shared and have nothing to do with it. -/
abbrev Instances (ι V : Type) : Type := Set (ι × ProcState V)

/-- **At most one state per instance.** `Instances` is a set of pairs, so nothing in the type says
so: `Algorithm.init` produces one pair per declared instance, and `Algebra.step` *replaces* the pair
an instance had rather than adding one, so every reachable state satisfies it.

Named because a refinement invariant over an algorithm state generally cannot be stated without it.
An invariant that accounts for anything *per instance* — `Guarded2Network`'s per-instance inbox, and
the FIFO prefix it is accounted against — is outright false at a state holding two states for one
instance: that instance's step updates the accounting, and the second state, which did not move, is
left related against the old one. So it is carried as a clause of the invariant rather than derived
from reachability, which would put a reachability hypothesis on every lemma below it. -/
def Instances.Functional (Ps : Instances ι V) : Prop :=
  ∀ p σ σ', (⟨p, σ⟩ : ι × ProcState V) ∈ Ps → (⟨p, σ'⟩ : ι × ProcState V) ∈ Ps → σ = σ'

/-- Replacing one instance's state keeps it — which is what an algorithm step does, and so what
every per-step lemma has to re-establish for its own post-state. -/
theorem Instances.Functional.replace {Ps : Instances ι V} (h : Ps.Functional) {p : ι}
    {σ : ProcState V} (hmem : (⟨p, σ⟩ : ι × ProcState V) ∈ Ps) (σ' : ProcState V) :
    Instances.Functional (insert (⟨p, σ'⟩ : ι × ProcState V) (Ps \ {⟨p, σ⟩})) := by
  intro q τ τ' hτ hτ'
  simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff, Prod.mk.injEq] at hτ hτ'
  rcases hτ with ⟨rfl, rfl⟩ | ⟨hτ, hne⟩
  · rcases hτ' with ⟨-, rfl⟩ | ⟨hτ', hne'⟩
    · rfl
    · absurd hne'
      exact ⟨rfl, h q τ' σ hτ' hmem⟩
  · rcases hτ' with ⟨rfl, rfl⟩ | ⟨hτ', -⟩
    · absurd hne
      exact ⟨rfl, h q τ σ hτ hmem⟩
    · exact h q τ τ' hτ hτ'

/-- An algorithm state: every process instance paired with its own state, plus the shared channels.
-/
abbrev AlgState (ι V : Type) : Type := Instances ι V × FIFOs V

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

/-- Some process goes wrong *now*: the immediate half of the paper's `P⊥_red`, with no steps taken
first. Named on its own because the aborting semantics is built from it by composition rather than
by iterating a functional that mentions it. -/
def Algebra.immediateAbort (A : Algebra ι V) : Set (AlgState ι V × Trace V) :=
  {⟨⟨Ps, F⟩, τ⟩ | ∃ p σ, ⟨p, σ⟩ ∈ Ps ∧
    ⟨⟨σ, F⟩, τ⟩ ∈ (A.table p).procAborting (A.owned p) (A.self p)}

/-- Every **finite** sequence of algorithm steps, with the concatenated trace: `step*`.

Given directly rather than as `μX. Id ∪ X ∘ᵣ₂ step`, for the same reason as `Algebra.diverging` and
`Algebra.aborting` — all three semantics are the closed forms the refinement framework's
operator-preservation lemmas are stated at, so no proof has to unfold a fixed point before it can
say anything. The empty execution is `Relation.star.refl`, not a disjunct to be supplied.
`VerifiedCompiler/ClosedForm.lean` carries the identity with the least fixed point. -/
def Algebra.reducing (A : Algebra ι V) : Set (AlgState ι V × Trace V × AlgState ι V) :=
  Relation.star A.step

/-- Every finite sequence of steps ending in a process going wrong: `step* ∘ᵣ₁ immediateAbort`. -/
def Algebra.aborting (A : Algebra ι V) : Set (AlgState ι V × Trace V) :=
  Relation.star A.step ∘ᵣ₁ A.immediateAbort

/-- Every infinite sequence of steps, each execution paired with the infinite product of the traces
its steps emit.

**Not** the greatest fixed point of `X ↦ step ∘ᵣ₁ X`. That functional is not contractive when a
step can emit the empty trace: at `step = {(σ, 1, σ)}` it is the identity, whose greatest fixed
point is `⊤` — every trace whatsoever paired with `σ`, rather than the `1` that execution actually
emits. Silent steps are not a corner case here, since `Behavior` observes only `print`/`send` and so
`while TRUE { x := x + 1 }` is an infinite chain of them. `Relation.omega` takes the product
of what the steps emit and gets this right by construction.

The two agree exactly when `Relation.Productive step` holds, which `Algebra.step` does not satisfy;
`Relation.gfp_eq_closedForm` states that boundary. -/
def Algebra.diverging (A : Algebra ι V) : Set (AlgState ι V × Trace V) :=
  Relation.omega A.step

/-! # Restricting to executions from the initial state

  The paper's `⟦A⟧*`/`⟦A⟧⊥`/`⟦A⟧∞` are these three relations restricted to executions starting from
  `init(A)`. `init` is a *relation* here, not a function: a process's local variables are given by
  initializer expressions, and evaluation is relational (`ExprSemantics.Eval`), so an algorithm with
  a meaningless initializer has no initial state rather than a junk one.
-/

/-- The memory a list of initializers and their values builds on top of a memory already in hand:
each declared name bound to its own value, in declaration order, so a name declared twice keeps the
later binding. Named rather than written inline in `InitProc` below because relating the state of an
instance whose initializer list one pass *extended* to the state of the source's is exactly a
statement about this function. -/
def InitMem [ExprSemantics V] (inits : List (String × ComputablePlusCal.Expression)) (vs : List V)
    (M : Memory V) : Memory V :=
  ((inits.map Prod.fst).zip vs).foldl (λ M xv ↦ M.insert xv.1 xv.2) M

/-- `InitProc self inits σ` — `σ` is a valid initial state for a process instance with identity
`self`, local variable initializers `inits`, and initial label set `entry`. -/
def InitProc [ExprSemantics V] (self : V) (inits : List (String × ComputablePlusCal.Expression))
    (entry : Set String) (σ : ProcState V) : Prop :=
  ∃ vs : List V,
    List.Forall₂ (λ ie v ↦ ExprSemantics.Eval (Finmap.singleton selfName self) (Prod.snd ie) v)
      inits vs ∧
    σ.1 = InitMem inits vs (Finmap.singleton selfName self) ∧
    σ.2 = entry

/-- An initial state starts at the entry labels, and nothing else. The one projection of `InitProc`
that needs no work, named so that reading it does not cost an `obtain` of the whole existential. -/
theorem InitProc.labels [ExprSemantics V] {self : V}
    {inits : List (String × ComputablePlusCal.Expression)} {entry : Set String} {σ : ProcState V}
    (h : InitProc self inits entry σ) : σ.2 = entry := by
  obtain ⟨-, -, -, hlab⟩ := h
  exact hlab

/-- A list of expressions evaluates to at most one list of values — `ExprSemantics.evalUnique`
pointwise. -/
theorem eval_forall₂_inj [ExprSemantics V] {M : Memory V}
    {inits : List (String × ComputablePlusCal.Expression)} {vs ws : List V}
    (h : List.Forall₂ (λ ie v ↦ ExprSemantics.Eval M (Prod.snd ie) v) inits vs)
    (h' : List.Forall₂ (λ ie v ↦ ExprSemantics.Eval M (Prod.snd ie) v) inits ws) : vs = ws := by
  induction h generalizing ws with
  | nil => cases h'; rfl
  | @cons _ _ _ _ hv _ ih =>
    cases h' with
    | cons hw htl => rw [ExprSemantics.evalUnique hv hw, ih htl]

/-- **An instance has at most one initial state.** Everything `InitProc` fixes is fixed: the label
set is `entry` outright, and the memory is a fold over the initializers' values, which
`ExprSemantics.evalUnique` pins one by one.

What wants it is `Instances.Functional` — `Guarded2Network`'s algorithm-level invariant requires one
state per instance on both sides, for soundness rather than bookkeeping (see that field's own doc). -/
theorem InitProc.inj [ExprSemantics V] {self : V}
    {inits : List (String × ComputablePlusCal.Expression)} {entry : Set String}
    {σ σ' : ProcState V} (h : InitProc self inits entry σ) (h' : InitProc self inits entry σ') :
    σ = σ' := by
  obtain ⟨vs, hvs, hmem, hlab⟩ := h
  obtain ⟨ws, hws, hmem', hlab'⟩ := h'
  obtain rfl := eval_forall₂_inj hvs hws
  exact Prod.ext (hmem.trans hmem'.symm) (hlab.trans hlab'.symm)

/-- **`InitMem` over an appended list is one fold on top of the other**, provided the values split
where the names do. The equation the two `InitProc.append` lemmas below share. -/
theorem InitMem.append [ExprSemantics V]
    {is₁ is₂ : List (String × ComputablePlusCal.Expression)} {ws₁ ws₂ : List V} {M : Memory V}
    (hlen : is₁.length = ws₁.length) :
    InitMem (is₁ ++ is₂) (ws₁ ++ ws₂) M = InitMem is₂ ws₂ (InitMem is₁ ws₁ M) := by
  have hlen' : (is₁.map Prod.fst).length = ws₁.length := by rw [List.length_map, hlen]
  unfold InitMem
  rw [List.map_append, List.zip_append hlen', List.foldl_append]

/-- **Initializers all declaring one name touch only that name.** Every write the fold makes is at
`y`, so a lookup anywhere else reads straight through to the memory the fold started from. -/
theorem InitMem.lookup_ne [ExprSemantics V]
    {inits : List (String × ComputablePlusCal.Expression)} {ws : List V} {x y : String}
    {M : Memory V} (hname : ∀ e ∈ inits, e.1 = y) (hxy : x ≠ y) :
    (InitMem inits ws M).lookup x = M.lookup x := by
  unfold InitMem
  induction inits generalizing ws M with
  | nil => rfl
  | cons a rest ih =>
    cases ws with
    | nil => rfl
    | cons w _ =>
      obtain rfl := hname a List.mem_cons_self
      rw [List.map_cons, List.zip_cons_cons, List.foldl_cons,
        ih (λ e he ↦ hname e (List.mem_cons_of_mem _ he)), Finmap.lookup_insert_of_ne _ hxy]

/-- **And a non-empty such list leaves that name bound to one of their values.** Which one is the
last, but no caller needs to know that — what they need is that the value is *one of* those the
initializers evaluated to, so that a property shared by all of them holds of it. -/
theorem InitMem.lookup_mem [ExprSemantics V]
    {inits : List (String × ComputablePlusCal.Expression)} {ws : List V} {y : String}
    {M : Memory V} (hname : ∀ e ∈ inits, e.1 = y) (hne : inits ≠ [])
    (hlen : inits.length = ws.length) : ∃ v ∈ ws, (InitMem inits ws M).lookup y = .some v := by
  unfold InitMem
  induction inits generalizing ws M with
  | nil => exact (hne rfl).elim
  | cons a rest ih =>
    cases ws with
    | nil => exact nomatch hlen
    | cons w ws' =>
      obtain rfl := hname a List.mem_cons_self
      rw [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      cases rest with
      | nil => exact ⟨w, List.mem_cons_self, Finmap.lookup_insert _⟩
      | cons _ _ =>
        obtain ⟨v, hv, hlk⟩ :=
          ih (λ e he ↦ hname e (List.mem_cons_of_mem _ he)) (List.cons_ne_nil _ _)
            (Nat.succ_injective hlen)
        exact ⟨v, List.mem_cons_of_mem _ hv, hlk⟩

/-- **A state over a longer initializer list is one over the shorter, written on top of.** Every
initializer is evaluated under the *same* memory — `self` alone, never the one being accumulated —
so appending to the list neither disturbs the values already taken nor makes new ones depend on
them, and the fold splits where the list does.

What reads it is `Guarded2Network`: a compiled process declares the source's locals plus the `inbox`
the pass invented, and relating the two initial memories is exactly this split. The shorter state's
label set is free, being whatever the caller's own `init` asks for. -/
theorem InitProc.append [ExprSemantics V] {self : V}
  {is₁ is₂ : List (String × ComputablePlusCal.Expression)} {e₁ e₂ : Set String} {σ' : ProcState V}
  (h : InitProc self (is₁ ++ is₂) e₂ σ') :
    ∃ (M : Memory V) (ws : List V), InitProc self is₁ e₁ (M, e₁) ∧
      List.Forall₂ (λ ie v ↦ ExprSemantics.Eval (Finmap.singleton selfName self) (Prod.snd ie) v)
        is₂ ws ∧
      σ'.1 = InitMem is₂ ws M := by
  obtain ⟨vs, hvs, hmem, -⟩ := h
  obtain ⟨ws₁, ws₂, rfl, hw₁, hw₂⟩ := hvs.exists_append_left
  refine ⟨InitMem is₁ ws₁ (Finmap.singleton selfName self), ws₂, ⟨ws₁, hw₁, rfl, rfl⟩, hw₂, ?_⟩
  rw [hmem, InitMem.append hw₁.length_eq]

/-- The converse: values for the added initializers build a state over the longer list. What wants
this direction is the *existence* half — a source instance's initial state is only usable as a
witness if the compiled instance has one too. -/
theorem InitProc.append_of [ExprSemantics V] {self : V}
  {is₁ is₂ : List (String × ComputablePlusCal.Expression)} {e₁ e₂ : Set String} {σ : ProcState V}
  {ws : List V} (h : InitProc self is₁ e₁ σ)
  (hws : List.Forall₂ (λ ie v ↦ ExprSemantics.Eval (Finmap.singleton selfName self) (Prod.snd ie) v)
    is₂ ws) : InitProc self (is₁ ++ is₂) e₂ (InitMem is₂ ws σ.1, e₂) := by
  obtain ⟨vs, hvs, hmem, -⟩ := h
  refine ⟨vs ++ ws, List.rel_append hvs hws, ?_, rfl⟩
  rw [hmem, InitMem.append hvs.length_eq]

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

/-- A thread's first block is one of its blocks, so a process starts at labels it owns. What reads it
is disjointness: a fact about every owned label holds of every entry label without being re-proved. -/
theorem Process.entryLabels_subset_ownedLabels {p : ComputableGuardedPlusCal.Process} :
    Process.entryLabels p ⊆ Process.ownedLabels p := by
  rintro _ ⟨T, hT, B, hhead, rfl⟩
  exact ⟨T, hT, B, List.mem_of_mem_head? hhead, rfl⟩

/-- The paper's `Ξₚ`: a label denotes the union of its block's branches. A label the process does not
own denotes `∅` in both components, making it unschedulable. -/
def Process.codeTable [ExprSemantics V] (p : ComputableGuardedPlusCal.Process) : CodeTable V where
  reducing l :=
    {x | ∃ T ∈ p.threads, ∃ B ∈ T, B.label = l ∧ ∃ Br ∈ B.branches, x ∈ AtomicBranch.reducing Br}
  aborting l :=
    {x | ∃ T ∈ p.threads, ∃ B ∈ T, B.label = l ∧ ∃ Br ∈ B.branches, x ∈ AtomicBranch.aborting Br}

/-! # Instantiating the algorithm layer

  Processes are indexed by `String × V` — the declaring `Process`'s own name together with a
  specific instance's identity. `table`/`owned` don't depend on *which* instance, only on the
  `Process` the name resolves to, so both look the name up and answer from that `Process`'s own
  `codeTable`/`ownedLabels`; a name with no matching `Process` (unreachable for any `ι` an actual
  `Algorithm.init`-satisfying state ever contains) answers with the empty table, same "absent
  label is just unschedulable" convention `codeTable` itself already uses. -/

/-- Assembles a whole `Algorithm`'s `Algebra`, per the module doc above. -/
def Algorithm.algebra [ExprSemantics V] (algo : ComputableGuardedPlusCal.Algorithm) :
    Algebra (String × V) V where
  table := λ ⟨name, _⟩ ↦
    (algo.processes.find? (·.name == name)).elim { reducing := λ _ ↦ ∅, aborting := λ _ ↦ ∅ }
      Process.codeTable
  owned := λ ⟨name, _⟩ ↦ (algo.processes.find? (·.name == name)).elim ∅ Process.ownedLabels
  self := Prod.snd

/-- The instance identities an `«=|∈»`/`id` pair contributes: `id`'s own value for `=`, each member
of `id`'s (set) value for `∈`. Evaluated under the empty memory — `WellFormedness/Restrictions.lean`
bans a process from referencing any module-level `VARIABLE`, so `id` can only mention `CONSTANT`s and
literals, and there is nothing else to evaluate it against.

Stated about the two fields rather than about a process so that `NetworkPlusCal` can share it: the
two languages' `Process.identities` are then the *same* function of the same two fields, and a pass
that preserves them preserves the instances by rewriting, with no unfolding downstream. -/
def identitiesOf [ExprSemantics V] (shape : Bool) (id : ComputablePlusCal.Expression) : Set V :=
  {self | match shape with
    | true => ExprSemantics.Eval ∅ id self
    | false => ∃ S, ExprSemantics.Eval ∅ id S ∧ ExprSemantics.mem self S}

@[inherit_doc identitiesOf]
def Process.identities [ExprSemantics V] (p : ComputableGuardedPlusCal.Process) : Set V :=
  identitiesOf p.«=|∈» p.id

/-- `Process.identities` reads nothing but the two fields. The form every statement relating a
process to a compiled copy of it goes through. -/
theorem Process.identities_eq [ExprSemantics V] {p : ComputableGuardedPlusCal.Process} :
    Process.identities (V := V) p = identitiesOf p.«=|∈» p.id := rfl

/-- One declared local in the shape `InitProc` takes it — its name paired with its initializer, and
nothing when it has none. Named rather than written inline in `initsOf` below so that `List`'s own
`filterMap` lemmas apply to `initsOf` with no unfolding at the sites that reason about it. -/
def initOf (v : String × ComputableTLAPlus.Typ × Bool ×
    Option (Bool × ComputablePlusCal.Expression)) : Option (String × ComputablePlusCal.Expression) :=
  v.2.2.2.map λ (_, e) ↦ (v.1, e)

/-- A declared-locals list's initializers, in the shape `InitProc` takes them: the variables that
have one, paired with it.

Stated about the list rather than about a process so that `NetworkPlusCal` can share it — the two
languages' `Process.inits` are then the same function of the same field, which is what lets a pass
that only *extends* the list say so. -/
def initsOf (vars : List (String × ComputableTLAPlus.Typ × Bool ×
    Option (Bool × ComputablePlusCal.Expression))) : List (String × ComputablePlusCal.Expression) :=
  vars.filterMap initOf

section

variable {vars vs ws : List (String × ComputableTLAPlus.Typ × Bool ×
  Option (Bool × ComputablePlusCal.Expression))}

@[inherit_doc initsOf]
theorem initsOf_eq_filterMap : initsOf vars = vars.filterMap initOf := rfl

/-- The initializers of an appended locals list split where the list does. -/
theorem initsOf_append : initsOf (vs ++ ws) = initsOf vs ++ initsOf ws := by
  unfold initsOf
  exact List.filterMap_append ..

end

@[inherit_doc initsOf]
def Process.inits (p : ComputableGuardedPlusCal.Process) :
    List (String × ComputablePlusCal.Expression) :=
  initsOf p.localState.variables

/-- `Process.inits` reads nothing but the declared locals. The form every statement relating a
process to a compiled copy of it goes through. -/
theorem Process.inits_eq {p : ComputableGuardedPlusCal.Process} :
    Process.inits p = initsOf p.localState.variables := rfl

/-- A valid initial state: every declared `Process` contributes exactly the instances its own
`«=|∈»`/`id` calls for, each starting per `InitProc` at its own entry labels, **and no others**.

Stated as a characterization of membership rather than as "for each declared instance some state
exists". The weaker reading does not constrain `Ps` at all — it is satisfied by an `Instances` that
*also* holds junk pairs, or two states for one instance, since an existential is still witnessed. It
is the membership form that makes `Instances.Functional` derivable (`init.functional` below), and
that clause of `Guarded2Network`'s algorithm-level invariant is a soundness obligation rather than
bookkeeping.

Every declared channel/fifo starts with an empty queue at every index its own domain admits — not
simply "`F` has no entries": `Statement.reducing`/`.aborting`'s `F.lookup = none` case is an
*abort* (`Denotational.lean`), reserved for an index outside the declared domain entirely, not for
"nothing sent yet". -/
def Algorithm.init [ExprSemantics V] (algo : ComputableGuardedPlusCal.Algorithm) :
    AlgState (String × V) V → Prop
  | ⟨Ps, F⟩ =>
    (∀ (i : String × V) (σ : ProcState V), (⟨i, σ⟩ : (String × V) × ProcState V) ∈ Ps ↔
      ∃ p ∈ algo.processes, ∃ self ∈ Process.identities (V := V) p,
        i = (p.name, self) ∧ InitProc self p.inits (Process.entryLabels p) σ)
    ∧ ∀ nτd ∈ algo.globalState.channels ++ algo.globalState.fifos, ∀ idx : List V,
        (∃ Ss, List.Forall₂ (ExprSemantics.Eval ∅) nτd.2.2 Ss ∧ List.Forall₂ ExprSemantics.mem idx Ss) →
          F.lookup ⟨nτd.1, idx.map .inr⟩ = .some []

/-- **An initial state holds one state per instance.** The two halves of the argument: membership
pins which process an instance came from, and `InitProc.inj` pins that process's initial state.

`hnames` is the front end's — no two declared processes share a name. Without it a single
`⟨name, self⟩` could be contributed by two processes with different bodies, and the two initial
states would genuinely differ. It is the same condition `Algorithm.algebra` already rests on, that
one resolving an instance by `find?` on the name and so answering for the *first* process carrying
it. -/
theorem Algorithm.init.functional [ExprSemantics V] {algo : ComputableGuardedPlusCal.Algorithm}
    {Ps : Instances (String × V) V} {F : FIFOs V}
    (hnames : ∀ p ∈ algo.processes, ∀ q ∈ algo.processes, p.name = q.name → p = q)
    (h : Algorithm.init algo ⟨Ps, F⟩) : Ps.Functional := by
  intro i σ σ' hσ hσ'
  obtain ⟨p, hp, self, -, rfl, hinit⟩ := (h.1 i σ).mp hσ
  obtain ⟨q, hq, self', -, heq, hinit'⟩ := (h.1 _ σ').mp hσ'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hname, rfl⟩ := heq
  obtain rfl := hnames p hp q hq hname
  exact hinit.inj hinit'

end GuardedPlusCal

end
