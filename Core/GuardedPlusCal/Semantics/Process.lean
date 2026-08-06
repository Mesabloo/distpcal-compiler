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
emits. Silent steps are not a corner case here, since `Behavior` observes only `print`/`send`/`recv`
and so `while TRUE { x := x + 1 }` is an infinite chain of them. `Relation.omega` takes the product
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

/-- A valid initial state: every declared `Process` contributes exactly the instances its own
`«=|∈»`/`id` calls for — one, at `id`'s value, for `=`; one per member of `id`'s (set) value, for
`∈` — each starting per `InitProc` at its own entry labels, and no others. `id` (and each
channel/fifo's index domain, below) evaluates under the empty memory: `WellFormedness/
Restrictions.lean` already bans a process from referencing any module-level `VARIABLE`, so these
expressions can only mention `CONSTANT`s/literals, never runtime state — there is nothing else to
evaluate them against.

Every declared channel/fifo starts with an empty queue at every index its own domain admits — not
simply "`F` has no entries": `Statement.reducing`/`.aborting`'s `F.lookup = none` case is an
*abort* (`Denotational.lean`), reserved for an index outside the declared domain entirely, not for
"nothing sent yet". -/
def Algorithm.init [ExprSemantics V] (algo : ComputableGuardedPlusCal.Algorithm) :
    AlgState (String × V) V → Prop
  | ⟨Ps, F⟩ =>
    (∀ p ∈ algo.processes, ∀ self : V,
      (∃ σ, ((p.name, self), σ) ∈ Ps ∧
        InitProc self
          (p.localState.variables.filterMap λ (n, _, _, e?) ↦ e?.map λ (_, e) ↦ (n, e))
          (Process.entryLabels p) σ) ↔
      match p.«=|∈» with
        | true => ExprSemantics.Eval ∅ p.id self
        | false => ∃ S, ExprSemantics.Eval ∅ p.id S ∧ ExprSemantics.mem self S)
    ∧ ∀ nτd ∈ algo.globalState.channels ++ algo.globalState.fifos, ∀ idx : List V,
        (∃ Ss, List.Forall₂ (ExprSemantics.Eval ∅) nτd.2.2 Ss ∧ List.Forall₂ ExprSemantics.mem idx Ss) →
          F.lookup ⟨nτd.1, idx.map .inr⟩ = .some []

end GuardedPlusCal

end
