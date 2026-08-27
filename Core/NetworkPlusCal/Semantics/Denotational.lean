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

open ComputableTLAPlus (Memory ExprSemantics OperatorEnv Model)
open GuardedPlusCal (Block Behavior Trace ChanKey FIFOs LocalState EvalStep selfName)

variable {V : Type} [ExprSemantics V]

/-! # Reduction of statements -/

def Statement.reducing (Ξ : OperatorEnv) (Ω : Model V) :
    {b b' : Bool} → ComputableNetworkPlusCal.Statement b b' →
    Set (LocalState V × Trace V × LocalState V)
  | true, false, .with name _ bound e =>
    {⟨σ, ε, σ'⟩ | ∃ M F v,
      ExprSemantics.Eval Ξ Ω M e v ∧
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
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ExprSemantics.Eval Ξ Ω M e v ∧ M.lookup selfName = .some p ∧
      ε = Stream'.Seq.cons (.print p v) 1}
  | false, false, .assert e => test e ExprSemantics.tru
  | false, false, .send c e =>
    {⟨σ, ε, σ'⟩ | ∃ M F v cpath vs p,
      ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some vs ∧ M.lookup selfName = .some p ∧
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F.insert ⟨c.name, cpath⟩ (vs.concat v), .none⟩ ∧
      ε = Stream'.Seq.cons (.send p ⟨c.name, cpath⟩ v) 1
    }
  -- TODO(multicast): no semantics yet, exactly as on the Guarded side. The two must be resolved
  -- together: a refinement between them is only provable once both say something.
  | false, false, .multicast _ _ => ∅
  | false, false, .assign r e =>
    {⟨σ, ε, σ'⟩ | ∃ M F M' v rpath,
      ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
      Memory.update M r.name rpath v = .some M' ∧
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M', F, .none⟩ ∧ ε = 1
    }
where
  /-- `test e v` is the identity transition restricted to states that evaluate `e` to `v`. -/
  test (e : ComputablePlusCal.Expression) (v : V) :
      Set (LocalState V × Trace V × LocalState V) :=
    {⟨σ, ε, σ'⟩ | ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ExprSemantics.Eval Ξ Ω M e v ∧ ε = 1}

  /-- The identity transition, i.e. nothing is performed. -/
  idle : Set (LocalState V × Trace V × LocalState V) :=
    {⟨σ, ε, σ'⟩ | ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ε = 1}

def Statement.aborting (Ξ : OperatorEnv) (Ω : Model V) :
    {b b' : Bool} → ComputableNetworkPlusCal.Statement b b' →
    Set (LocalState V × Trace V)
  | true, false, .with _ _ bound e =>
    {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F v, ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ match bound with
        | true => False
        | false => ¬ ExprSemantics.isSet v}
  | true, false, .await e =>
    {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F v, ¬ ExprSemantics.isBool v ∧ ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | false, false, .skip => ∅
  | false, true, .goto _ => ∅
  | false, false, .print e => {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | false, false, .assert e =>
    {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F v, v ≠ ExprSemantics.tru ∧ ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | false, false, .send c e =>
    {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F, GuardedPlusCal.Ref.pathAborts Ξ Ω M c ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
        F.lookup ⟨c.name, cpath⟩ = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  -- TODO(multicast): see `Statement.reducing`'s `multicast` case.
  | false, false, .multicast _ _ => ∅
  | false, false, .assign r e =>
    {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F, GuardedPlusCal.Ref.pathAborts Ξ Ω M r ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F v rpath,
        ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
        Memory.update M r.name rpath v = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}

/-- No statement can diverge — same as on the Guarded side. -/
def Statement.diverging : {b b' : Bool} → ComputableNetworkPlusCal.Statement b b' →
    Set (LocalState V × Trace V)
  | _, _, _ => ∅

/-- The states from which a guard-class statement is *blocked* — same as on the Guarded side, minus
`receive` (this language has none): `await` on a boolean that is not `TRUE`, or `with x ∈ e` on a
(present but) empty set. The trace is `1`. -/
def Statement.blocking (Ξ : OperatorEnv) (Ω : Model V) :
    {b b' : Bool} → ComputableNetworkPlusCal.Statement b b' → Set (LocalState V × Trace V)
  | true, false, .with _ _ bound e =>
    {⟨σ, ε⟩ | ∃ M F v, ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
      match bound with
      | true => False
      | false => ExprSemantics.isSet v ∧ ¬ ∃ v', ExprSemantics.mem v' v}
  | true, false, .await e =>
    {⟨σ, ε⟩ | ∃ M F v, ExprSemantics.isBool v ∧ v ≠ ExprSemantics.tru ∧
      ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | _, _, _ => ∅

/-! # Reduction of blocks and atomic branches

  `GuardedPlusCal.Block.reducing`/`.aborting`/`.diverging` are generic in the statement family, so
  they are applied here directly rather than restated.
-/

/-- A block of Network PlusCal statements, all of guard class `g`. -/
def Statement.blockReducing (Ξ : OperatorEnv) (Ω : Model V) {g b : Bool}
    (B : Block (ComputableNetworkPlusCal.Statement g) b) :
    Set (LocalState V × Trace V × LocalState V) :=
  Block.reducing (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) B

@[inherit_doc Statement.blockReducing]
def Statement.blockAborting (Ξ : OperatorEnv) (Ω : Model V) {g b : Bool}
    (B : Block (ComputableNetworkPlusCal.Statement g) b) :
    Set (LocalState V × Trace V) :=
  Block.aborting (λ ⦃_⦄ ↦ Statement.aborting Ξ Ω)
    (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) B

@[inherit_doc Statement.blockReducing]
def Statement.blockDiverging (Ξ : OperatorEnv) (Ω : Model V) {g b : Bool}
    (B : Block (ComputableNetworkPlusCal.Statement g) b) :
    Set (LocalState V × Trace V) :=
  Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) B

@[inherit_doc Statement.blockReducing]
def Statement.blockBlocking (Ξ : OperatorEnv) (Ω : Model V) {g b : Bool}
    (B : Block (ComputableNetworkPlusCal.Statement g) b) :
    Set (LocalState V × Trace V) :=
  Block.aborting (λ ⦃_⦄ ↦ Statement.blocking Ξ Ω) (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) B

/-- A possibly-empty *list* of Network PlusCal statements — see `GuardedPlusCal.Block.listReducing`
for why the shape exists alongside `Block`. `Guarded2Network` prepends one of these (a branch's
consumption assignments) to an action block, and its refinement proof states the two factors
separately. -/
def Statement.listReducing (Ξ : OperatorEnv) (Ω : Model V) {g : Bool}
    (A : List (ComputableNetworkPlusCal.Statement g false)) :
    Set (LocalState V × Trace V × LocalState V) :=
  Block.listReducing (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) A

@[inherit_doc Statement.listReducing]
def Statement.listAborting (Ξ : OperatorEnv) (Ω : Model V) {g : Bool}
    (A : List (ComputableNetworkPlusCal.Statement g false)) :
    Set (LocalState V × Trace V) :=
  Block.listAborting (λ ⦃_⦄ ↦ Statement.aborting Ξ Ω)
    (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) A

@[inherit_doc Statement.listReducing]
def Statement.listDiverging (Ξ : OperatorEnv) (Ω : Model V) {g : Bool}
    (A : List (ComputableNetworkPlusCal.Statement g false)) :
    Set (LocalState V × Trace V) :=
  Block.listAborting (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) A

def AtomicBranch.reducing (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState V × Trace V × LocalState V) :=
  B.precondition.elim Relation.Idle (Statement.blockReducing Ξ Ω) ∘ᵣ₂
    Statement.blockReducing Ξ Ω B.action

def AtomicBranch.aborting (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState V × Trace V) :=
  match B.precondition with
  | .none => Statement.blockAborting Ξ Ω B.action
  | .some B' =>
    Statement.blockAborting Ξ Ω B' ∪
      Statement.blockReducing Ξ Ω B' ∘ᵣ₁ Statement.blockAborting Ξ Ω B.action

def AtomicBranch.diverging (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState V × Trace V) :=
  match B.precondition with
  | .none => Statement.blockDiverging Ξ Ω B.action
  | .some B' =>
    Statement.blockDiverging Ξ Ω B' ∪
      Statement.blockReducing Ξ Ω B' ∘ᵣ₁ Statement.blockDiverging Ξ Ω B.action

/-- The states from which an atomic branch is *blocked*: its precondition reduces to a state at
which some later guard blocks. A bare action blocks nowhere. -/
def AtomicBranch.blocking (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState V × Trace V) :=
  match B.precondition with
  | .none => Statement.blockBlocking Ξ Ω B.action
  | .some B' =>
    Statement.blockBlocking Ξ Ω B' ∪
      Statement.blockReducing Ξ Ω B' ∘ᵣ₁ Statement.blockBlocking Ξ Ω B.action

/-! # Reduction of atomic blocks

  A block picks one of its branches nondeterministically — reducing/aborting/diverging as *some*
  branch, chosen from `B.branches`. Only needed on the `NetworkPlusCal` side: the refinement
  relation's target type is what needs the flat state encoding uniformly, the source stays
  quantified throughout since it is only ever existentially bound, never required to match the
  target's type. `GuardedPlusCal` therefore has no `AtomicBlock` semantics at all. -/

def AtomicBlock.reducing (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableNetworkPlusCal.AtomicBlock) :
    Set (LocalState V × Trace V × LocalState V) :=
  {⟨σ, ε, σ'⟩ | ∃ Br ∈ B.branches, ⟨σ, ε, σ'⟩ ∈ AtomicBranch.reducing Ξ Ω Br}

def AtomicBlock.aborting (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableNetworkPlusCal.AtomicBlock) :
    Set (LocalState V × Trace V) :=
  {⟨σ, ε⟩ | ∃ Br ∈ B.branches, ⟨σ, ε⟩ ∈ AtomicBranch.aborting Ξ Ω Br}

def AtomicBlock.diverging (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableNetworkPlusCal.AtomicBlock) :
    Set (LocalState V × Trace V) :=
  {⟨σ, ε⟩ | ∃ Br ∈ B.branches, ⟨σ, ε⟩ ∈ AtomicBranch.diverging Ξ Ω Br}

/-- A block is *blocked* iff **every** one of its branches is: `either` is angelic, so it proceeds
on any branch that can and blocks only when none can — the intersection over `B.branches`, where
`reducing`/`aborting`/`diverging` take the union. -/
def AtomicBlock.blocking (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableNetworkPlusCal.AtomicBlock) :
    Set (LocalState V × Trace V) :=
  {x | ∀ Br ∈ B.branches, x ∈ AtomicBranch.blocking Ξ Ω Br}

/-! # Threads

  A `.code` thread has no denotation of its own. A process state is a memory together with a **set
  of labels** — at most one per thread — and one process step picks an enabled label `l` from that
  set, runs the atomic block the label names, and replaces `l` by the label the block's terminal
  `goto` jumped to. So a `.code` thread contributes exactly two things: the labels it owns, and the
  block each of those labels names. Everything else is the process- and algorithm-level fixed points.

  `Thread.rx` is different. It owns no label, and its step consumes and produces none: it is a
  virtual thread whose meaning is the single step "read the head message off `mailboxₚ` and append
  it to `inboxₚ`", taken whenever `mailboxₚ` is non-empty and with no `tmpₚ` variable — the value
  goes straight from the channel into `inboxₚ`. It contributes one thing: `Thread.rxStep`, a
  label-free reducing step handed to the process layer through `CodeTable.relay`. `Thread.rx`'s
  `label` field names the Go loop the thread compiles to and has no part in this semantics. -/

/-- The labels a thread owns. A `.code` thread owns its blocks' labels; a `.rx` thread owns none —
its step is label-free. -/
def Thread.labels : ComputableNetworkPlusCal.Thread → List String
  | .code blocks => blocks.map (·.label)
  | .rx .. => []

/-- The one reducing step a receiving thread contributes: read the head message off `chan` and
append it to the `inbox` sequence, leaving every scheduled label untouched. Written directly rather
than built from `Statement`s, because `NetworkPlusCal.Statement` has no `receive` and the paper's
`tmpₚ` is never assigned.

The step is **silent**: reception is not in `Behavior`'s alphabet (`GuardedPlusCal`'s
`Semantics/Denotational.lean`). Moving a message from `chan` into `inbox` changes no observable; that
the two together hold what the source's channel holds is the refinement invariant's job. An *empty*
channel yields no step — a receiving thread then waits, which the blocking semantics records. -/
def Thread.rxStep (Ξ : OperatorEnv) (Ω : Model V) (chan : ComputableNetworkPlusCal.Ref)
    (inbox : String) :
    Set (LocalState V × Trace V × LocalState V) :=
  {⟨σ, ε, σ'⟩ | ∃ M F cpath v vs old new,
    List.Forall₂ (EvalStep Ξ Ω M) chan.args cpath ∧
    F.lookup ⟨chan.name, cpath⟩ = .some (v :: vs) ∧
    M.lookup inbox = .some old ∧
    ExprSemantics.seqAppend old v = .some new ∧
    σ = ⟨M, F, .none⟩ ∧
    σ' = ⟨M.insert inbox new, F.insert ⟨chan.name, cpath⟩ vs, .none⟩ ∧
    ε = 1
  }

end NetworkPlusCal

end
