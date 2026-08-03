module

public import Core.NetworkPlusCal.Syntax
public import Core.GuardedPlusCal.Semantics.Denotational

@[expose] public section

/-!
  The denotational semantics of Network PlusCal. `Statement` here is `GuardedPlusCal.Statement`
  minus `receive`, so every case below is that language's case verbatim — see
  `Core/GuardedPlusCal/Semantics/Denotational.lean`'s module doc for what `reducing`/`aborting`/
  `diverging` mean and why blocking and aborting are kept distinct.

  The state space is *shared*, not re-declared: `Behavior`, `ChanKey`, `FIFOs`, `LocalState`,
  `EvalStep` and `Ref.pathAborts` are taken from `GuardedPlusCal` unchanged. This pass does not
  touch memories, channels or references — it only moves a `receive` out of the guard position and
  into a `Thread.rx`. Sharing the state space is also what lets item 7 state a refinement between
  the two languages without first transporting across two isomorphic copies of the same types.
-/

namespace NetworkPlusCal

open ComputableTLAPlus (Memory ExprSemantics)
open GuardedPlusCal (Block Behavior ChanKey FIFOs LocalState EvalStep selfName)

variable {V : Type} [ExprSemantics V]

/-! # Reduction of statements -/

def Statement.reducing : {b b' : Bool} → ComputableNetworkPlusCal.Statement b b' →
    Set (LocalState V false × List (Behavior V) × LocalState V b')
  | true, false, .with name _ bound e =>
    {⟨σ, ε, σ'⟩ | ∃ M F v,
      M ⊢ e ⇒ v ∧
      AList.lookup name M = none ∧
      σ = .running M F ∧ ε = [] ∧ match bound with
        | true => σ' = .running (M.insert name v) F
        | false => ∃ v', ExprSemantics.mem v' v ∧ σ' = .running (M.insert name v') F
    }
  | true, false, .await e => test e ExprSemantics.tru
  | false, false, .skip => idle
  | false, true, .goto label =>
    {⟨σ, ε, σ'⟩ | ∃ M F, σ = .running M F ∧ σ' = .done M F label ∧ ε = []}
  | false, false, .print e =>
    {⟨σ, ε, σ'⟩ | ∃ M F v p,
      σ = .running M F ∧ σ' = .running M F ∧ M ⊢ e ⇒ v ∧ M.lookup selfName = .some p ∧
      ε = [.print p v]}
  | false, false, .assert e => test e ExprSemantics.tru
  | false, false, .send c e =>
    {⟨σ, ε, σ'⟩ | ∃ M F v cpath vs p,
      M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) c.args cpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some vs ∧ M.lookup selfName = .some p ∧
      σ = .running M F ∧ σ' = .running M (F.replace ⟨c.name, cpath⟩ (vs.concat v)) ∧
      ε = [.send p ⟨c.name, cpath⟩ v]
    }
  -- TODO(item 7): `multicast` has no semantics yet, exactly as on the Guarded side — see
  -- `Core/GuardedPlusCal/Semantics/Denotational.lean`'s `Statement.reducing`. The two must be
  -- resolved together: a refinement between them is only provable once both say something.
  | false, false, .multicast _ _ => ∅
  | false, false, .assign r e =>
    {⟨σ, ε, σ'⟩ | ∃ M F M' v rpath,
      M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
      Memory.update M r.name rpath v = .some M' ∧
      σ = .running M F ∧ σ' = .running M' F ∧ ε = []
    }
where
  /-- `test e v` is the identity transition restricted to states that evaluate `e` to `v`. -/
  test (e : ComputablePlusCal.Expression) (v : V) :
      Set (LocalState V false × List (Behavior V) × LocalState V false) :=
    {⟨σ, ε, σ'⟩ | ∃ M F, σ = .running M F ∧ σ' = .running M F ∧ M ⊢ e ⇒ v ∧ ε = []}

  /-- The identity transition, i.e. nothing is performed. -/
  idle : Set (LocalState V false × List (Behavior V) × LocalState V false) :=
    {⟨σ, ε, σ'⟩ | ∃ M F, σ = .running M F ∧ σ' = .running M F ∧ ε = []}

def Statement.aborting : {b b' : Bool} → ComputableNetworkPlusCal.Statement b b' →
    Set (LocalState V false × List (Behavior V))
  | true, false, .with _ _ bound e =>
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F v, M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = [] ∧ match bound with
        | true => False
        | false => ¬ ExprSemantics.isSet v}
  | true, false, .await e =>
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F v, ¬ ExprSemantics.isBool v ∧ M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = []}
  | false, false, .skip => ∅
  | false, true, .goto _ => ∅
  | false, false, .print e => {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
  | false, false, .assert e =>
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F v, v ≠ ExprSemantics.tru ∧ M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = []}
  | false, false, .send c e =>
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F, GuardedPlusCal.Ref.pathAborts M c ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep M) c.args cpath ∧
        F.lookup ⟨c.name, cpath⟩ = .none ∧ σ = .running M F ∧ ε = []}
  -- TODO(item 7): see `Statement.reducing`'s `multicast` case.
  | false, false, .multicast _ _ => ∅
  | false, false, .assign r e =>
    {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F, GuardedPlusCal.Ref.pathAborts M r ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F v rpath,
        M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
        Memory.update M r.name rpath v = .none ∧ σ = .running M F ∧ ε = []}

/-- No statement can diverge — same as on the Guarded side. -/
def Statement.diverging : {b b' : Bool} → ComputableNetworkPlusCal.Statement b b' →
    Set (LocalState V false × List (Behavior V))
  | _, _, _ => ∅

/-! # Reduction of blocks and atomic branches

  `GuardedPlusCal.Block.reducing`/`.aborting`/`.diverging` are generic in the statement family, so
  they are applied here directly rather than restated.
-/

/-- A block of Network PlusCal statements, all of guard class `g`. -/
def Statement.blockReducing {g b : Bool} (B : Block (ComputableNetworkPlusCal.Statement g) b) :
    Set (LocalState V false × List (Behavior V) × LocalState V b) :=
  Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B

@[inherit_doc Statement.blockReducing]
def Statement.blockAborting {g b : Bool} (B : Block (ComputableNetworkPlusCal.Statement g) b) :
    Set (LocalState V false × List (Behavior V)) :=
  Block.aborting (λ ⦃_⦄ ↦ Statement.aborting) (λ ⦃_⦄ ↦ Statement.reducing) B

@[inherit_doc Statement.blockReducing]
def Statement.blockDiverging {g b : Bool} (B : Block (ComputableNetworkPlusCal.Statement g) b) :
    Set (LocalState V false × List (Behavior V)) :=
  Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) B

def AtomicBranch.reducing (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState V false × List (Behavior V) × LocalState V true) :=
  B.precondition.elim {⟨x, e, y⟩ | x = y ∧ e = 1} Statement.blockReducing ∘ᵣ₂
    Statement.blockReducing B.action

def AtomicBranch.aborting (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState V false × List (Behavior V)) :=
  match B.precondition with
  | .none => Statement.blockAborting B.action
  | .some B' =>
    Statement.blockAborting B' ∪ Statement.blockReducing B' ∘ᵣ₁ Statement.blockAborting B.action

def AtomicBranch.diverging (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState V false × List (Behavior V)) :=
  match B.precondition with
  | .none => Statement.blockDiverging B.action
  | .some B' =>
    Statement.blockDiverging B' ∪ Statement.blockReducing B' ∘ᵣ₁ Statement.blockDiverging B.action

/-! # Reduction of atomic blocks

  A block picks one of its branches nondeterministically — reducing/aborting/diverging as *some*
  branch, chosen from `B.branches`. Only needed on the `NetworkPlusCal` side: the refinement
  relation's target type is what needs the flat `LocalState'` encoding uniformly
  (`Semantics/Lemmas.lean`'s `sem_glue₃`/`abort_glue₂`/`div_glue₂`/`div_glue₃`), the source stays
  indexed throughout since it is only ever existentially quantified, never required to match the
  target's type — so `GuardedPlusCal` never needed this layer built (confirmed against prior art,
  `Guarded2Network/Lemmas.lean`: no `GuardedPlusCal.AtomicBlock.reducing`/`.aborting`/`.diverging`
  anywhere). -/

def AtomicBlock.reducing (B : ComputableNetworkPlusCal.AtomicBlock) :
    Set (LocalState V false × List (Behavior V) × LocalState V true) :=
  {⟨σ, ε, σ'⟩ | ∃ Br ∈ B.branches, ⟨σ, ε, σ'⟩ ∈ AtomicBranch.reducing Br}

def AtomicBlock.aborting (B : ComputableNetworkPlusCal.AtomicBlock) :
    Set (LocalState V false × List (Behavior V)) :=
  {⟨σ, ε⟩ | ∃ Br ∈ B.branches, ⟨σ, ε⟩ ∈ AtomicBranch.aborting Br}

def AtomicBlock.diverging (B : ComputableNetworkPlusCal.AtomicBlock) :
    Set (LocalState V false × List (Behavior V)) :=
  {⟨σ, ε⟩ | ∃ Br ∈ B.branches, ⟨σ, ε⟩ ∈ AtomicBranch.diverging Br}

/-! # Threads

  A thread has no denotation of its own. Following the paper (§3.3, *Semantics of threads and
  processes*), a process state is a memory together with a **set of labels** — at most one per
  thread — and one process step picks an enabled label `l` from that set, runs the atomic block the
  label names, and replaces `l` by the label the block's terminal `goto` jumped to. So a thread
  contributes exactly two things: the labels it owns, and the block each of those labels names.
  Everything else is the process- and algorithm-level fixed points.

  `Thread.rx` is no exception. The paper (§4.1) defines its meaning to be *that of the atomic block*

  ```
  rxₚ : receive(mailboxₚ, tmpₚ) ; inboxₚ := Append(inboxₚ, tmpₚ) ; goto rxₚ
  ```

  "although without the temporary variable `tmpₚ` assigned to". That block is a single atomic block —
  guard, one assignment, terminal `goto` — so draining the channel into `inboxₚ` is one transition
  by construction rather than by stipulation, and the self-`goto` is what makes it loop. `tmpₚ` is
  never written: the value goes straight from the channel into `inboxₚ`, so it needs no name and the
  AST has no field for it. `rxₚ` does have a field — `Thread.rx`'s `label` — since the loop has to be
  schedulable by label and has to be able to name itself as its own `goto` target.
-/

/-- The labels a thread owns. A `.code` thread owns its blocks' labels; a `.rx` thread owns the
single label of its receiving loop. -/
def Thread.labels : ComputableNetworkPlusCal.Thread → List String
  | .code blocks => blocks.map (·.label)
  | .rx _ label _ _ => [label]

/-- The atomic block a receiving thread denotes, per the paper's §4.1: receive a message from `chan`,
append it to `inbox`, and jump back to `label` — its own label, which is what makes it a loop.
Written directly as an `AtomicBranch` rather than built from `Statement`s, because
`NetworkPlusCal.Statement` has no `receive` — that is the whole point of this pass — and because the
paper's `tmpₚ` is never assigned, so there is no statement sequence to express. -/
def Thread.rxBranch (chan : ComputableNetworkPlusCal.Ref) (label inbox : String) :
    Set (LocalState V false × List (Behavior V) × LocalState V true) :=
  {⟨σ, ε, σ'⟩ | ∃ M F cpath v vs old new p,
    List.Forall₂ (EvalStep M) chan.args cpath ∧
    F.lookup ⟨chan.name, cpath⟩ = .some (v :: vs) ∧
    M.lookup inbox = .some old ∧
    ExprSemantics.seqAppend old v = .some new ∧
    M.lookup selfName = .some p ∧
    σ = .running M F ∧
    σ' = .done (M.insert inbox new) (F.replace ⟨chan.name, cpath⟩ vs) label ∧
    ε = [.recv p ⟨chan.name, cpath⟩ v]
  }

/-- Where `Thread.rxBranch` goes wrong. An *empty* channel is not an abort — it blocks, which is
precisely a receiving thread waiting for a message. -/
def Thread.rxBranchAborting (chan : ComputableNetworkPlusCal.Ref) (inbox : String) :
    Set (LocalState V false × List (Behavior V)) :=
  -- an index expression of the channel reference has no value
  {⟨σ, ε⟩ | ∃ M F, GuardedPlusCal.Ref.pathAborts M chan ∧ σ = .running M F ∧ ε = []}
  -- the channel resolves to no FIFO at all
  ∪ {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep M) chan.args cpath ∧
      F.lookup ⟨chan.name, cpath⟩ = .none ∧ σ = .running M F ∧ ε = []}
  -- `inbox` is unbound, or does not hold a sequence
  ∪ {⟨σ, ε⟩ | ∃ M F, M.lookup inbox = .none ∧ σ = .running M F ∧ ε = []}
  ∪ {⟨σ, ε⟩ | ∃ M F cpath v vs old, List.Forall₂ (EvalStep M) chan.args cpath ∧
      F.lookup ⟨chan.name, cpath⟩ = .some (v :: vs) ∧ M.lookup inbox = .some old ∧
      ExprSemantics.seqAppend old v = .none ∧ σ = .running M F ∧ ε = []}

end NetworkPlusCal

end
