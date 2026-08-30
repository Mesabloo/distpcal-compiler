module

public import Core.NetworkPlusCal.Semantics.Denotational
public import Core.GuardedPlusCal.Semantics.Process

@[expose] public section

/-!
  Network PlusCal's instantiation of the process and algorithm layers. Everything structural —
  `ProcState`, `CodeTable`, `Algebra`, the three fixed points — is `GuardedPlusCal`'s and is used
  here unchanged; see `Core/GuardedPlusCal/Semantics/Process.lean`.

  The only difference between the two languages at this level is what a process's threads
  contribute. A `.code` thread contributes its blocks' labels and their branches, exactly as in
  Guarded PlusCal. A `.rx` thread contributes no label — it contributes one label-free step,
  `Thread.rxStep`, collected into the code table's `relay` component and taken by the process step
  with no scheduled label consumed.
-/

namespace NetworkPlusCal

open ComputableTLAPlus (ExprSemantics OperatorEnv Model)
open GuardedPlusCal (CodeTable Algebra AlgState EvalStep InitProc)

universe u

variable {V : Type u}

/-- Every label a process owns, across all of its threads. A `.rx` thread owns none. -/
def Process.ownedLabels (p : ComputableNetworkPlusCal.Process) : Set String :=
  {l | ∃ T ∈ p.threads, l ∈ Thread.labels T}

/-- The label each `.code` thread starts at — its first block's. A `.rx` thread owns no label and
contributes nothing. -/
def Process.entryLabels (p : ComputableNetworkPlusCal.Process) : Set String :=
  {l | ∃ T ∈ p.threads, (Thread.labels T).head? = .some l}

/-- The paper's `Ξₚ`. `reducing`/`aborting`/`blocking`/`owned` match `GuardedPlusCal.Process.codeTable`
over the `.code` threads; `relay` collects every `.rx` thread's receiving step and `relayBlocking`
says every such thread's channel is empty. -/
def Process.codeTable [ExprSemantics V] (Ξ : OperatorEnv) (Ω : Model V)
    (p : ComputableNetworkPlusCal.Process) : CodeTable V where
  reducing l :=
    {x | ∃ T ∈ p.threads, ∃ blocks, T = .code blocks ∧
      ∃ B ∈ blocks, B.label = l ∧ ∃ Br ∈ B.branches, x ∈ AtomicBranch.reducing Ξ Ω Br}
  aborting l :=
    {x | ∃ T ∈ p.threads, ∃ blocks, T = .code blocks ∧
      ∃ B ∈ blocks, B.label = l ∧ ∃ Br ∈ B.branches, x ∈ AtomicBranch.aborting Ξ Ω Br}
  relay :=
    {x | ∃ T ∈ p.threads, ∃ chan label τ inbox, T = .rx chan label τ inbox ∧
      x ∈ Thread.rxStep Ξ Ω chan inbox}
  blocking l :=
    {x | ∀ T ∈ p.threads, ∀ blocks, T = .code blocks →
      ∀ B ∈ blocks, B.label = l → ∀ Br ∈ B.branches, x ∈ AtomicBranch.blocking Ξ Ω Br}
  owned := Process.ownedLabels p
  relayBlocking :=
    {σ | ∀ T ∈ p.threads, ∀ chan label τ inbox, T = .rx chan label τ inbox →
      ∃ cpath, List.Forall₂ (EvalStep Ξ Ω σ.mem) chan.args cpath ∧
        σ.fifos.lookup ⟨chan.name, cpath⟩ = .some []}

/-- A step at a label is a step of some thread's own block, so the label is one the process owns —
`codeTable`'s "absent label is unschedulable" convention, read the other way round. Used at the
algorithm level to derive `l ∈ ownedLabels p'` straight from the step in hand, rather than carrying
ownership as a separate hypothesis to case on. -/
theorem Process.ownedLabels_of_reducing [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}
    {p : ComputableNetworkPlusCal.Process}
    {l : String} {x} (hx : x ∈ (Process.codeTable (V := V) Ξ Ω p).reducing l) :
    l ∈ Process.ownedLabels p := by
  obtain ⟨T, hT, blocks, rfl, B, hB, rfl, -⟩ := hx
  exact ⟨_, hT, by simp only [Thread.labels]; exact List.mem_map_of_mem hB⟩

@[inherit_doc Process.ownedLabels_of_reducing]
theorem Process.ownedLabels_of_aborting [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}
    {p : ComputableNetworkPlusCal.Process}
    {l : String} {x} (hx : x ∈ (Process.codeTable (V := V) Ξ Ω p).aborting l) :
    l ∈ Process.ownedLabels p := by
  obtain ⟨T, hT, blocks, rfl, B, hB, rfl, -⟩ := hx
  exact ⟨_, hT, by simp only [Thread.labels]; exact List.mem_map_of_mem hB⟩

/-! # Instantiating the algorithm layer

  `ι = String × V`: an instance is a declared process's name paired with the identity it runs under,
  so every lookup below resolves the name against `algo.processes` and reads this language's
  `codeTable`/`ownedLabels`/`entryLabels` off the process it finds. -/

/-- Assembles a whole `Algorithm`'s `Algebra`. -/
def Algorithm.algebra [ExprSemantics V] (Ξ : OperatorEnv) (Ω : Model V)
    (algo : ComputableNetworkPlusCal.Algorithm) :
    Algebra V :=
  λ ⟨name, _⟩ ↦
    (algo.processes.find? (·.name == name)).elim
      { reducing := λ _ ↦ ∅, aborting := λ _ ↦ ∅, relay := ∅,
        blocking := λ _ ↦ ∅, owned := ∅, relayBlocking := Set.univ }
      (Process.codeTable Ξ Ω)

/-- The instance identities a declared process contributes, read off its `=`/`∈` form and its `id`
expression. -/
def Process.identities [ExprSemantics V] (Ξ : OperatorEnv) (Ω : Model V)
    (p : ComputableNetworkPlusCal.Process) : Set V :=
  GuardedPlusCal.identitiesOf Ξ Ω p.«=|∈» p.id

/-- `Process.identities` reads nothing but the two fields, which is what lets a pass preserving them
preserve the instances by rewriting. -/
theorem Process.identities_eq [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}
    {p : ComputableNetworkPlusCal.Process} :
    Process.identities (V := V) Ξ Ω p = GuardedPlusCal.identitiesOf Ξ Ω p.«=|∈» p.id := rfl

/-- A declared process's local initializers, in the shape `InitProc` takes them. -/
def Process.inits (p : ComputableNetworkPlusCal.Process) :
    List (String × ComputablePlusCal.Expression) :=
  GuardedPlusCal.initsOf p.localState.variables

/-- `Process.inits` reads nothing but the declared locals, which is what lets a pass that only
*extends* the locals say so. -/
theorem Process.inits_eq {p : ComputableNetworkPlusCal.Process} :
    Process.inits p = GuardedPlusCal.initsOf p.localState.variables := rfl

/-- A valid initial state: the instance map holds exactly one state per declared process and
identity, each at that process's entry labels under its declared initializers, and every declared
channel starts empty. A characterization of membership, not an existence claim. -/
def Algorithm.init [ExprSemantics V] (Ξ : OperatorEnv) (Ω : Model V)
    (algo : ComputableNetworkPlusCal.Algorithm) :
    AlgState (String × V) V → Prop
  | ⟨Ps, F⟩ =>
    (∀ (i : String × V) (σ : GuardedPlusCal.ProcState V), Ps i = .some σ ↔
      ∃ p ∈ algo.processes, ∃ self ∈ Process.identities (V := V) Ξ Ω p,
        i = (p.name, self) ∧ GuardedPlusCal.InitProc Ξ Ω self p.inits (Process.entryLabels p) σ)
    ∧ ∀ nτd ∈ algo.globalState.channels ++ algo.globalState.fifos, ∀ idx : List V,
        (∃ Ss, List.Forall₂ (ExprSemantics.Eval Ξ Ω ∅) nτd.2.2 Ss ∧
            List.Forall₂ ExprSemantics.mem idx Ss) →
          F.lookup ⟨nτd.1, idx.map .inr⟩ = .some []

end NetworkPlusCal

end
