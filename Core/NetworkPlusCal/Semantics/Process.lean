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
open GuardedPlusCal (CodeTable)

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

end NetworkPlusCal

end
