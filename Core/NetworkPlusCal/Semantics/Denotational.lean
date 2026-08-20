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
  into a `Thread.rx`. Sharing the state space is also what lets a refinement between the two
  languages be stated without first transporting across two isomorphic copies of the same types.
-/

namespace NetworkPlusCal

open ComputableTLAPlus (Memory ExprSemantics)
open GuardedPlusCal (Block Behavior Trace ChanKey FIFOs LocalState EvalStep selfName)

variable {V : Type} [ExprSemantics V]

/-! # Reduction of statements -/

def Statement.reducing : {b b' : Bool} → ComputableNetworkPlusCal.Statement b b' →
    Set (LocalState V × Trace V × LocalState V)
  | true, false, .with name _ bound e =>
    {⟨σ, ε, σ'⟩ | ∃ M F v,
      M ⊢ e ⇒ v ∧
      Finmap.lookup name M = none ∧
      σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ match bound with
        | true => σ' = ⟨M.insert name v, F, .none⟩
        | false => ∃ v', ExprSemantics.mem v' v ∧ σ' = ⟨M.insert name v', F, .none⟩
    }
  | true, false, .await e => test e ExprSemantics.tru
  | false, false, .skip => idle
  | false, true, .goto label =>
    {⟨σ, ε, σ'⟩ | ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .some label⟩ ∧ ε = 1}
  | false, false, .print e =>
    {⟨σ, ε, σ'⟩ | ∃ M F v p,
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ M ⊢ e ⇒ v ∧ M.lookup selfName = .some p ∧
      ε = Stream'.Seq.cons (.print p v) 1}
  | false, false, .assert e => test e ExprSemantics.tru
  | false, false, .send c e =>
    {⟨σ, ε, σ'⟩ | ∃ M F v cpath vs p,
      M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) c.args cpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some vs ∧ M.lookup selfName = .some p ∧
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F.insert ⟨c.name, cpath⟩ (vs.concat v), .none⟩ ∧
      ε = Stream'.Seq.cons (.send p ⟨c.name, cpath⟩ v) 1
    }
  -- TODO(multicast): no semantics yet, exactly as on the Guarded side. The two must be resolved
  -- together: a refinement between them is only provable once both say something.
  | false, false, .multicast _ _ => ∅
  | false, false, .assign r e =>
    {⟨σ, ε, σ'⟩ | ∃ M F M' v rpath,
      M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
      Memory.update M r.name rpath v = .some M' ∧
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M', F, .none⟩ ∧ ε = 1
    }
where
  /-- `test e v` is the identity transition restricted to states that evaluate `e` to `v`. -/
  test (e : ComputablePlusCal.Expression) (v : V) :
      Set (LocalState V × Trace V × LocalState V) :=
    {⟨σ, ε, σ'⟩ | ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ M ⊢ e ⇒ v ∧ ε = 1}

  /-- The identity transition, i.e. nothing is performed. -/
  idle : Set (LocalState V × Trace V × LocalState V) :=
    {⟨σ, ε, σ'⟩ | ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ε = 1}

def Statement.aborting : {b b' : Bool} → ComputableNetworkPlusCal.Statement b b' →
    Set (LocalState V × Trace V)
  | true, false, .with _ _ bound e =>
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F v, M ⊢ e ⇒ v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ match bound with
        | true => False
        | false => ¬ ExprSemantics.isSet v}
  | true, false, .await e =>
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F v, ¬ ExprSemantics.isBool v ∧ M ⊢ e ⇒ v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | false, false, .skip => ∅
  | false, true, .goto _ => ∅
  | false, false, .print e => {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | false, false, .assert e =>
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F v, v ≠ ExprSemantics.tru ∧ M ⊢ e ⇒ v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | false, false, .send c e =>
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F, GuardedPlusCal.Ref.pathAborts M c ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep M) c.args cpath ∧
        F.lookup ⟨c.name, cpath⟩ = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  -- TODO(multicast): see `Statement.reducing`'s `multicast` case.
  | false, false, .multicast _ _ => ∅
  | false, false, .assign r e =>
    {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F, GuardedPlusCal.Ref.pathAborts M r ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F v rpath,
        M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
        Memory.update M r.name rpath v = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}

/-- No statement can diverge — same as on the Guarded side. -/
def Statement.diverging : {b b' : Bool} → ComputableNetworkPlusCal.Statement b b' →
    Set (LocalState V × Trace V)
  | _, _, _ => ∅

/-! # Reduction of blocks and atomic branches

  `GuardedPlusCal.Block.reducing`/`.aborting`/`.diverging` are generic in the statement family, so
  they are applied here directly rather than restated.
-/

/-- A block of Network PlusCal statements, all of guard class `g`. -/
def Statement.blockReducing {g b : Bool} (B : Block (ComputableNetworkPlusCal.Statement g) b) :
    Set (LocalState V × Trace V × LocalState V) :=
  Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B

@[inherit_doc Statement.blockReducing]
def Statement.blockAborting {g b : Bool} (B : Block (ComputableNetworkPlusCal.Statement g) b) :
    Set (LocalState V × Trace V) :=
  Block.aborting (λ ⦃_⦄ ↦ Statement.aborting) (λ ⦃_⦄ ↦ Statement.reducing) B

@[inherit_doc Statement.blockReducing]
def Statement.blockDiverging {g b : Bool} (B : Block (ComputableNetworkPlusCal.Statement g) b) :
    Set (LocalState V × Trace V) :=
  Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) B

/-- A possibly-empty *list* of Network PlusCal statements — see `GuardedPlusCal.Block.listReducing`
for why the shape exists alongside `Block`. `Guarded2Network` prepends one of these (a branch's
consumption assignments) to an action block, and its refinement proof states the two factors
separately. -/
def Statement.listReducing {g : Bool} (A : List (ComputableNetworkPlusCal.Statement g false)) :
    Set (LocalState V × Trace V × LocalState V) :=
  Block.listReducing (λ ⦃_⦄ ↦ Statement.reducing) A

@[inherit_doc Statement.listReducing]
def Statement.listAborting {g : Bool} (A : List (ComputableNetworkPlusCal.Statement g false)) :
    Set (LocalState V × Trace V) :=
  Block.listAborting (λ ⦃_⦄ ↦ Statement.aborting) (λ ⦃_⦄ ↦ Statement.reducing) A

@[inherit_doc Statement.listReducing]
def Statement.listDiverging {g : Bool} (A : List (ComputableNetworkPlusCal.Statement g false)) :
    Set (LocalState V × Trace V) :=
  Block.listAborting (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) A

def AtomicBranch.reducing (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState V × Trace V × LocalState V) :=
  B.precondition.elim Relation.Idle Statement.blockReducing ∘ᵣ₂
    Statement.blockReducing B.action

def AtomicBranch.aborting (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState V × Trace V) :=
  match B.precondition with
  | .none => Statement.blockAborting B.action
  | .some B' =>
    Statement.blockAborting B' ∪ Statement.blockReducing B' ∘ᵣ₁ Statement.blockAborting B.action

def AtomicBranch.diverging (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState V × Trace V) :=
  match B.precondition with
  | .none => Statement.blockDiverging B.action
  | .some B' =>
    Statement.blockDiverging B' ∪ Statement.blockReducing B' ∘ᵣ₁ Statement.blockDiverging B.action

/-! # Reduction of atomic blocks

  A block picks one of its branches nondeterministically — reducing/aborting/diverging as *some*
  branch, chosen from `B.branches`. Only needed on the `NetworkPlusCal` side: the refinement
  relation's target type is what needs the flat state encoding uniformly, the source stays
  quantified throughout since it is only ever existentially bound, never required to match the
  target's type. `GuardedPlusCal` therefore has no `AtomicBlock` semantics at all. -/

def AtomicBlock.reducing (B : ComputableNetworkPlusCal.AtomicBlock) :
    Set (LocalState V × Trace V × LocalState V) :=
  {⟨σ, ε, σ'⟩ | ∃ Br ∈ B.branches, ⟨σ, ε, σ'⟩ ∈ AtomicBranch.reducing Br}

def AtomicBlock.aborting (B : ComputableNetworkPlusCal.AtomicBlock) :
    Set (LocalState V × Trace V) :=
  {⟨σ, ε⟩ | ∃ Br ∈ B.branches, ⟨σ, ε⟩ ∈ AtomicBranch.aborting Br}

def AtomicBlock.diverging (B : ComputableNetworkPlusCal.AtomicBlock) :
    Set (LocalState V × Trace V) :=
  {⟨σ, ε⟩ | ∃ Br ∈ B.branches, ⟨σ, ε⟩ ∈ AtomicBranch.diverging Br}

/-! # Threads

  A thread has no denotation of its own. A process state is a memory together with a **set of
  labels** — at most one per
  thread — and one process step picks an enabled label `l` from that set, runs the atomic block the
  label names, and replaces `l` by the label the block's terminal `goto` jumped to. So a thread
  contributes exactly two things: the labels it owns, and the block each of those labels names.
  Everything else is the process- and algorithm-level fixed points.

  `Thread.rx` is no exception: its meaning is that of the atomic block

  ```
  rxₚ : receive(mailboxₚ, tmpₚ) ; inboxₚ := Append(inboxₚ, tmpₚ) ; goto rxₚ
  ```

  without the temporary variable `tmpₚ` ever being assigned to. That block is a single atomic block —
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

/-- The atomic block a receiving thread denotes: receive a message from `chan`,
append it to `inbox`, and jump back to `label` — its own label, which is what makes it a loop.
Written directly as an `AtomicBranch` rather than built from `Statement`s, because
`NetworkPlusCal.Statement` has no `receive` — that is the whole point of this pass — and because the
paper's `tmpₚ` is never assigned, so there is no statement sequence to express.

The branch is **silent**: reception is not in `Behavior`'s alphabet (`GuardedPlusCal`'s
`Semantics/Denotational.lean`), precisely because this thread pops a channel at a moment the source
program need never reach. Moving a message from `chan` into `inbox` changes no observable; that the
two together hold what the source's channel holds is the refinement invariant's job. -/
def Thread.rxBranch (chan : ComputableNetworkPlusCal.Ref) (label inbox : String) :
    Set (LocalState V × Trace V × LocalState V) :=
  {⟨σ, ε, σ'⟩ | ∃ M F cpath v vs old new,
    List.Forall₂ (EvalStep M) chan.args cpath ∧
    F.lookup ⟨chan.name, cpath⟩ = .some (v :: vs) ∧
    M.lookup inbox = .some old ∧
    ExprSemantics.seqAppend old v = .some new ∧
    σ = ⟨M, F, .none⟩ ∧
    σ' = ⟨M.insert inbox new, F.insert ⟨chan.name, cpath⟩ vs, .some label⟩ ∧
    ε = 1
  }

/-- **A relay jumps back to its own label.** That is what makes a receiving thread a loop, and it is
read off the branch's shape — so a caller wanting it need not take the branch apart, which is the
only reason this is a lemma rather than a remark. -/
theorem Thread.rxBranch_label {chan : ComputableNetworkPlusCal.Ref}
    {label inbox l : String} {M M' : Memory V} {F F' : FIFOs V} {ε : Trace V}
    (h : (⟨⟨M, F, .none⟩, ε, ⟨M', F', .some l⟩⟩ : LocalState V × Trace V × LocalState V) ∈
      Thread.rxBranch chan label inbox) : l = label := by
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, hdone, -⟩ := h
  simpa only [LocalState.label_mk, Option.some.injEq] using congrArg LocalState.label hdone

/-- Where `Thread.rxBranch` goes wrong. An *empty* channel is not an abort — it blocks, which is
precisely a receiving thread waiting for a message. -/
def Thread.rxBranchAborting (chan : ComputableNetworkPlusCal.Ref) (inbox : String) :
    Set (LocalState V × Trace V) :=
  -- an index expression of the channel reference has no value
  {⟨σ, ε⟩ | ∃ M F, GuardedPlusCal.Ref.pathAborts M chan ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  -- the channel resolves to no FIFO at all
  ∪ {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep M) chan.args cpath ∧
      F.lookup ⟨chan.name, cpath⟩ = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  -- `inbox` is unbound, or does not hold a sequence
  ∪ {⟨σ, ε⟩ | ∃ M F, M.lookup inbox = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  ∪ {⟨σ, ε⟩ | ∃ M F cpath v vs old, List.Forall₂ (EvalStep M) chan.args cpath ∧
      F.lookup ⟨chan.name, cpath⟩ = .some (v :: vs) ∧ M.lookup inbox = .some old ∧
      ExprSemantics.seqAppend old v = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}

end NetworkPlusCal

end
