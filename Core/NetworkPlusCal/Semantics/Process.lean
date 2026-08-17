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
  which is what makes the paper's `T_rx` treatment work rather than needing a special case in the
  process step.
-/

namespace NetworkPlusCal

open ComputableTLAPlus (ExprSemantics)
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
def Process.codeTable [ExprSemantics V] (p : ComputableNetworkPlusCal.Process) : CodeTable V where
  reducing l :=
    {x | ∃ T ∈ p.threads, ∃ blocks, T = .code blocks ∧
      ∃ B ∈ blocks, B.label = l ∧ ∃ Br ∈ B.branches, x ∈ AtomicBranch.reducing Br}
    ∪ {x | ∃ T ∈ p.threads, ∃ chan τ inbox, T = .rx chan l τ inbox ∧
      x ∈ Thread.rxBranch chan l inbox}
  aborting l :=
    {x | ∃ T ∈ p.threads, ∃ blocks, T = .code blocks ∧
      ∃ B ∈ blocks, B.label = l ∧ ∃ Br ∈ B.branches, x ∈ AtomicBranch.aborting Br}
    ∪ {x | ∃ T ∈ p.threads, ∃ chan τ inbox, T = .rx chan l τ inbox ∧
      x ∈ Thread.rxBranchAborting chan inbox}

/-! # Instantiating the algorithm layer — see `GuardedPlusCal.Semantics.Process`'s own section for
why `ι = String × V`; identical reasoning here, just against this language's `codeTable`/
`ownedLabels`/`entryLabels`. -/

/-- Assembles a whole `Algorithm`'s `Algebra`. -/
def Algorithm.algebra [ExprSemantics V] (algo : ComputableNetworkPlusCal.Algorithm) :
    Algebra (String × V) V where
  table := λ ⟨name, _⟩ ↦
    (algo.processes.find? (·.name == name)).elim { reducing := λ _ ↦ ∅, aborting := λ _ ↦ ∅ }
      Process.codeTable
  owned := λ ⟨name, _⟩ ↦ (algo.processes.find? (·.name == name)).elim ∅ Process.ownedLabels
  self := Prod.snd

/-- The instance identities a declared process contributes — see
`GuardedPlusCal.Process.identities`, identical reasoning here. -/
def Process.identities [ExprSemantics V] (p : ComputableNetworkPlusCal.Process) : Set V :=
  GuardedPlusCal.identitiesOf p.«=|∈» p.id

/-- `Process.identities` reads nothing but the two fields — the same statement as
`GuardedPlusCal.Process.identities_eq`, at the same shared function, which is what lets a pass
preserving those two fields preserve the instances by rewriting. -/
theorem Process.identities_eq [ExprSemantics V] {p : ComputableNetworkPlusCal.Process} :
    Process.identities (V := V) p = GuardedPlusCal.identitiesOf p.«=|∈» p.id := rfl

/-- A declared process's local initializers, in the shape `InitProc` takes them. -/
def Process.inits (p : ComputableNetworkPlusCal.Process) :
    List (String × ComputablePlusCal.Expression) :=
  GuardedPlusCal.initsOf p.localState.variables

/-- `Process.inits` reads nothing but the declared locals — the same statement as
`GuardedPlusCal.Process.inits_eq`, at the same shared function, which is what lets a pass that only
*extends* the locals say so. -/
theorem Process.inits_eq {p : ComputableNetworkPlusCal.Process} :
    Process.inits p = GuardedPlusCal.initsOf p.localState.variables := rfl

/-- A valid initial state — see `GuardedPlusCal.Algorithm.init`'s doc comment, identical reasoning
here, including why this is a characterization of membership rather than an existence claim. -/
def Algorithm.init [ExprSemantics V] (algo : ComputableNetworkPlusCal.Algorithm) :
    AlgState (String × V) V → Prop
  | ⟨Ps, F⟩ =>
    (∀ (i : String × V) (σ : GuardedPlusCal.ProcState V),
      (⟨i, σ⟩ : (String × V) × GuardedPlusCal.ProcState V) ∈ Ps ↔
      ∃ p ∈ algo.processes, ∃ self ∈ Process.identities (V := V) p,
        i = (p.name, self) ∧ GuardedPlusCal.InitProc self p.inits (Process.entryLabels p) σ)
    ∧ ∀ nτd ∈ algo.globalState.channels ++ algo.globalState.fifos, ∀ idx : List V,
        (∃ Ss, List.Forall₂ (ExprSemantics.Eval ∅) nτd.2.2 Ss ∧ List.Forall₂ ExprSemantics.mem idx Ss) →
          F.lookup ⟨nτd.1, idx.map .inr⟩ = .some []

/-- **An initial state holds one state per instance** — `GuardedPlusCal.Algorithm.init.functional`
at this language's `init`, and the same two halves. -/
theorem Algorithm.init.functional [ExprSemantics V] {algo : ComputableNetworkPlusCal.Algorithm}
    {Ps : GuardedPlusCal.Instances (String × V) V} {F : GuardedPlusCal.FIFOs V}
    (hnames : ∀ p ∈ algo.processes, ∀ q ∈ algo.processes, p.name = q.name → p = q)
    (h : Algorithm.init algo ⟨Ps, F⟩) : Ps.Functional := by
  intro i σ σ' hσ hσ'
  obtain ⟨p, hp, self, -, rfl, hinit⟩ := (h.1 i σ).mp hσ
  obtain ⟨q, hq, self', -, heq, hinit'⟩ := (h.1 _ σ').mp hσ'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hname, rfl⟩ := heq
  obtain rfl := hnames p hp q hq hname
  exact hinit.inj hinit'

end NetworkPlusCal

end
