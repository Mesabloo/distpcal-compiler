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
  Guarded PlusCal. A `.rx` thread contributes its own single label, denoting the one atomic block of
  `Thread.rxBranch` — so a receiving loop is scheduled by the same mechanism as any other block,
  which is what keeps the process step free of a special case for it.
-/

namespace NetworkPlusCal

open ComputableTLAPlus (ExprSemantics OperatorEnv Model)
open GuardedPlusCal (CodeTable Algebra AlgState InitProc)

variable {V : Type}

/-- Every label a process owns, across all of its threads — including each `.rx` thread's own. -/
def Process.ownedLabels (p : ComputableNetworkPlusCal.Process) : Set String :=
  {l | ∃ T ∈ p.threads, l ∈ Thread.labels T}

/-- The label each thread starts at. A `.rx` thread starts at its own label, since its block is its
whole body. -/
def Process.entryLabels (p : ComputableNetworkPlusCal.Process) : Set String :=
  {l | ∃ T ∈ p.threads, (Thread.labels T).head? = .some l}

/-- The paper's `Ξₚ`. The `.code` half matches `GuardedPlusCal.Process.codeTable`; the `.rx` half is
the receiving loop's single block. -/
def Process.codeTable [ExprSemantics V] (Ξ : OperatorEnv) (Ω : Model V)
    (p : ComputableNetworkPlusCal.Process) : CodeTable V where
  reducing l :=
    {x | ∃ T ∈ p.threads, ∃ blocks, T = .code blocks ∧
      ∃ B ∈ blocks, B.label = l ∧ ∃ Br ∈ B.branches, x ∈ AtomicBranch.reducing Ξ Ω Br}
    ∪ {x | ∃ T ∈ p.threads, ∃ chan τ inbox, T = .rx chan l τ inbox ∧
      x ∈ Thread.rxBranch Ξ Ω chan l inbox}
  aborting l :=
    {x | ∃ T ∈ p.threads, ∃ blocks, T = .code blocks ∧
      ∃ B ∈ blocks, B.label = l ∧ ∃ Br ∈ B.branches, x ∈ AtomicBranch.aborting Ξ Ω Br}
    ∪ {x | ∃ T ∈ p.threads, ∃ chan τ inbox, T = .rx chan l τ inbox ∧
      x ∈ Thread.rxBranchAborting Ξ Ω chan inbox}

/-- A step at a label is a step of some thread's own block, so the label is one the process owns —
`codeTable`'s "absent label is unschedulable" convention, read the other way round. Used at the
algorithm level to derive `l ∈ ownedLabels p'` straight from the step in hand, rather than carrying
ownership as a separate hypothesis to case on. -/
theorem Process.ownedLabels_of_reducing [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}
    {p : ComputableNetworkPlusCal.Process}
    {l : String} {x} (hx : x ∈ (Process.codeTable (V := V) Ξ Ω p).reducing l) :
    l ∈ Process.ownedLabels p := by
  rcases hx with ⟨T, hT, blocks, rfl, B, hB, rfl, -⟩ | ⟨T, hT, chan, τ, inbox, rfl, -⟩
  · exact ⟨_, hT, by simp only [Thread.labels]; exact List.mem_map_of_mem hB⟩
  · exact ⟨_, hT, by simp only [Thread.labels]; exact List.mem_singleton_self l⟩

@[inherit_doc Process.ownedLabels_of_reducing]
theorem Process.ownedLabels_of_aborting [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}
    {p : ComputableNetworkPlusCal.Process}
    {l : String} {x} (hx : x ∈ (Process.codeTable (V := V) Ξ Ω p).aborting l) :
    l ∈ Process.ownedLabels p := by
  rcases hx with ⟨T, hT, blocks, rfl, B, hB, rfl, -⟩ | ⟨T, hT, chan, τ, inbox, rfl, -⟩
  · exact ⟨_, hT, by simp only [Thread.labels]; exact List.mem_map_of_mem hB⟩
  · exact ⟨_, hT, by simp only [Thread.labels]; exact List.mem_singleton_self l⟩

/-! # Instantiating the algorithm layer

  `ι = String × V`: an instance is a declared process's name paired with the identity it runs under,
  so every lookup below resolves the name against `algo.processes` and reads this language's
  `codeTable`/`ownedLabels`/`entryLabels` off the process it finds. -/

/-- Assembles a whole `Algorithm`'s `Algebra`. -/
def Algorithm.algebra [ExprSemantics V] (Ξ : OperatorEnv) (Ω : Model V)
    (algo : ComputableNetworkPlusCal.Algorithm) :
    Algebra V :=
  λ ⟨name, _⟩ ↦
    (algo.processes.find? (·.name == name)).elim { reducing := λ _ ↦ ∅, aborting := λ _ ↦ ∅ }
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
