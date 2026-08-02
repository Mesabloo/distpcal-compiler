module

public import Core.GuardedPlusCal.Syntax
public import Core.ComputableTLAPlus.Semantics.Interface
public import Extra.Rel
public import Extra.AList
public import Extra.List

@[expose] public section

/-!
  The denotational semantics of Guarded PlusCal, as three relations per syntactic form: `reducing`
  (a step to a successor state, emitting a list of observable behaviors), `aborting` (a state from
  which the form goes wrong), and `diverging` (a state from which it runs forever).

  They are plain definitions rather than `Reduce`/`Abort`/`Diverge` instances, so the
  `⟦·⟧*`/`⟦·⟧⊥`/`⟦·⟧∞` notations do not apply here. Those classes take their second argument as an
  `outParam`, and with the value type abstract it occurs *only* there — nothing in a `Statement` or
  an `AtomicBranch` mentions it — so Lean cannot order the synthesis of the `ExprSemantics`
  argument. Prior art carried no such argument, its value type being fixed. Nothing needs the
  classes: `VerifiedCompiler/Denotational/StrongRefinement.lean` takes the relations as plain
  `Set`s. The instances can be registered later, against the concrete TLA⁺ value type.

  Blocking and aborting are deliberately different: a statement with no `reducing` transition and no
  `aborting` state is a guard that is simply not enabled yet, which is what `await`, `receive` on an
  empty FIFO, and `with x ∈ {}` all are. That distinction is why `ExprSemantics` exposes `isBool`
  and `isSet` — without them a non-boolean guard would be indistinguishable from a false one.

  The expression layer underneath is abstract (`ComputableTLAPlus.ExprSemantics`), to be refined to
  the real TLA⁺ semantics later; see that file's module doc.

  Channels are kept out of the main memory, in a separate `FIFOs` map — the paper's `LState =
  (Var → Value) × (Var → Value*)`. An expression that reaches into a channel therefore has no
  meaning at all here rather than a wrong one, which is what lets the expression layer stay ignorant
  of channels entirely.

  This file stops at `AtomicBranch`. Threads, processes and algorithms are above it: a thread has no
  denotation of its own, only the labels it owns, and the process and algorithm layers are defined by
  fixed points over a step relation. See `Core/NetworkPlusCal/Semantics/Denotational.lean`'s
  `Thread.labels`.

  Where the paper's rules and this file differ, this file is the *stronger* of the two: the paper
  leaves several failure modes to well-formedness side conditions it assumes rather than states
  (`⟦receive(c,r)⟧⊥ = ∅` outright; `await` on a non-boolean and `with x ∈ e` on a non-set merely
  block). Those cases abort here. Deliberate — see `OPEN_QUESTIONS.md`.
-/

namespace GuardedPlusCal

open ComputableTLAPlus (Memory PathStep ExprSemantics)

variable {V : Type} [ExprSemantics V]

/-- The key identifying a single FIFO: the channel's name together with its resolved index path.
Prior art carried the whole channel reference; only the name and the evaluated indices are
observable, and this is also the shape a `Behavior.send` reports. -/
abbrev ChanKey (V : Type) : Type := String × List (PathStep V)

/-- The name a process instance's own identity is bound to, matching `Elaborator/PlusCal.lean`'s
`extend "self" .address`. -/
def selfName : String := "self"

/-- One of the possible observable behaviors exhibited by PlusCal statements. Every event carries the
process instance that emitted it — the value bound to `selfName` in its memory — so that program
order within one process is recoverable from a trace that interleaves several. Without it, two
`print`s from different processes would be indistinguishable from two `print`s of the same process,
and their relative order would stop being observable.

`send`/`recv` additionally carry the channel: two events on the same channel are not automatically
ordered by that alone — a `recv` can commute past a *later*, unrelated `send` on the same channel,
since a FIFO's queue keeps unrelated messages independent. Which `recv` matches which `send` is not
recorded here; it is read off a trace positionally (the `n`-th `send` on a channel is the `n`-th
`recv` on it, FIFO order), not tagged on the event itself. -/
inductive Behavior (V : Type) : Type
  | print (p v : V)
  | send (p : V) (c : ChanKey V) (v : V)
  | recv (p : V) (c : ChanKey V) (v : V)

/-- The global map containing FIFOs. Pushes go on the right, pops come off the left. -/
abbrev FIFOs (V : Type) : Type := AList λ _ : ChanKey V ↦ List V

/-- The local reduction state of an atomic block: the process's own memory and the channels. A
`done` state additionally carries the label the branch's terminal `goto` jumped to — the paper's
`LState⊥ = (Var → Value) × (Var → Value*)` and `LState⊤ = LState⊥ × Label`.

There is deliberately no third component for `with`-bound temporaries. Prior art carried one, using
`x ∉ tmp` as a side condition to stop an assignment targeting a block-local binder; that is a
syntactic property, and `WellFormedness/` checks it on the way in. Keeping it in the state would
oblige every lemma transcribed from the paper to translate between two state shapes for no
proof-side gain. -/
inductive LocalState (V : Type) : Bool → Type
  | running (M : Memory V) (F : FIFOs V) : LocalState V false
  | done (M : Memory V) (F : FIFOs V) (l : String) : LocalState V true

/-- Resolving one segment of a reference's access path against a memory: a field segment resolves to
itself, an index expression to whatever it evaluates to. -/
inductive EvalStep (M : Memory V) :
    (String ⊕ ComputablePlusCal.Expression) → PathStep V → Prop
  | field (f : String) : EvalStep M (.inl f) (.inl f)
  | index {e : ComputablePlusCal.Expression} {v : V} : ExprSemantics.Eval M e v → EvalStep M (.inr e) (.inr v)

/-- Some index expression in a reference's access path has no value. Field segments cannot fail, so
only the `.inr` ones are considered. -/
def Ref.pathAborts (M : Memory V) (r : ComputableGuardedPlusCal.Ref) : Prop :=
  ∃ e ∈ r.args.filterMap Sum.getRight?, M ⊢ e ↯

------------

/-! # Reduction of statements -/

def Statement.reducing : {b b' : Bool} → ComputableGuardedPlusCal.Statement b b' →
    Set (LocalState V false × List (Behavior V) × LocalState V b')
  | true, false, .with name _ bound e =>
    {⟨σ, ε, σ'⟩ | ∃ M F v,
      M ⊢ e ⇒ v ∧
      AList.lookup name M = none ∧
      σ = .running M F ∧ ε = [] ∧ match bound with
        -- `bound` is `true` for `=`, `false` for `∈` — the opposite polarity from prior art's
        -- `«=|∈»` field, see `Core/GuardedPlusCal/Syntax.lean`.
        | true => σ' = .running (M.insert name v) F
        | false => ∃ v', ExprSemantics.mem v' v ∧ σ' = .running (M.insert name v') F
    }
  | true, false, .await e => test e ExprSemantics.tru
  | true, false, .receive c r coe =>
    {⟨σ, ε, σ'⟩ | ∃ M F M' cpath rpath v v' vs p,
      List.Forall₂ (EvalStep M) c.args cpath ∧
      List.Forall₂ (EvalStep M) r.args rpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧
      ExprSemantics.coerce coe v v' ∧
      Memory.update M r.name rpath v' = .some M' ∧
      M.lookup selfName = .some p ∧
      σ = .running M F ∧ σ' = .running M' (F.replace ⟨c.name, cpath⟩ vs) ∧
      ε = [.recv p ⟨c.name, cpath⟩ v]
    }
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
  -- TODO(item 7): `multicast` has no semantics yet, so it currently neither steps nor aborts —
  -- deliberately deferred, not an oversight. Prior art left both its `reducing` and `aborting` cases
  -- `sorry`, and the shape wanted here (whether the recipient set must enumerate to a finite list,
  -- and what order the emitted `Behavior.send`s come in) is fixed by what the refinement proof
  -- needs. `∅` rather than `sorry` so the no-`sorry` check stays meaningful in the meantime.
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

def Statement.aborting : {b b' : Bool} → ComputableGuardedPlusCal.Statement b b' →
    Set (LocalState V false × List (Behavior V))
  | true, false, .with _ _ bound e =>
    -- the states that fail to evaluate `e`
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
    -- the states that evaluate `e` to a non-set when the binder is `∈`. An *empty* set is not an
    -- abort — it blocks.
    ∪ {⟨σ, ε⟩ | ∃ M F v, M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = [] ∧ match bound with
        | true => False
        | false => ¬ ExprSemantics.isSet v}
  | true, false, .await e =>
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F v, ¬ ExprSemantics.isBool v ∧ M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = []}
  | true, false, .receive c r coe =>
    -- the target is not a process variable at all, or is shadowed by a temporary
    {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = .running M F ∧ ε = []}
    -- an index expression of either reference has no value
    ∪ {⟨σ, ε⟩ | ∃ M F, σ = .running M F ∧ ε = [] ∧ Ref.pathAborts M c}
    ∪ {⟨σ, ε⟩ | ∃ M F, σ = .running M F ∧ ε = [] ∧ Ref.pathAborts M r}
    -- the channel resolves to no FIFO at all. Note an *empty* FIFO is not an abort — it blocks.
    ∪ {⟨σ, ε⟩ | ∃ M F cpath, σ = .running M F ∧ ε = [] ∧
        List.Forall₂ (EvalStep M) c.args cpath ∧ F.lookup ⟨c.name, cpath⟩ = .none}
    -- the dequeued value cannot be coerced to the target's type
    ∪ {⟨σ, ε⟩ | ∃ M F cpath v vs, σ = .running M F ∧ ε = [] ∧
        List.Forall₂ (EvalStep M) c.args cpath ∧
        F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧ ¬ ∃ v', ExprSemantics.coerce coe v v'}
    -- the target's path does not resolve inside the target's current value
    ∪ {⟨σ, ε⟩ | ∃ M F cpath rpath v v' vs, σ = .running M F ∧ ε = [] ∧
        List.Forall₂ (EvalStep M) c.args cpath ∧
        List.Forall₂ (EvalStep M) r.args rpath ∧
        F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧ ExprSemantics.coerce coe v v' ∧
        Memory.update M r.name rpath v' = .none}
  | false, false, .skip => ∅
  | false, true, .goto _ => ∅
  | false, false, .print e => {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
  | false, false, .assert e =>
    -- the states that fail to evaluate `e`
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
    -- the states that evaluate `e` to something other than `TRUE`
    ∪ {⟨σ, ε⟩ | ∃ M F v, v ≠ ExprSemantics.tru ∧ M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = []}
  | false, false, .send c e =>
    {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts M c ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep M) c.args cpath ∧
        F.lookup ⟨c.name, cpath⟩ = .none ∧ σ = .running M F ∧ ε = []}
  -- TODO(item 7): see `Statement.reducing`'s `multicast` case.
  | false, false, .multicast _ _ => ∅
  | false, false, .assign r e =>
    {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts M r ∧ σ = .running M F ∧ ε = []}
    ∪ {⟨σ, ε⟩ | ∃ M F v rpath,
        M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
        Memory.update M r.name rpath v = .none ∧ σ = .running M F ∧ ε = []}

/-- No statement can diverge: every constructor of `Statement` is a single step. Divergence only
enters at the block and process levels. -/
def Statement.diverging : {b b' : Bool} → ComputableGuardedPlusCal.Statement b b' →
    Set (LocalState V false × List (Behavior V))
  | _, _, _ => ∅

/-! # Reduction of blocks

  Generic over the index family and the state type: a block reduces by composing its elements'
  relations left to right, and aborts (or diverges) if any prefix reduces to a state from which the
  next element does. Nothing here mentions values, so these definitions are reused verbatim for
  `NetworkPlusCal`.
-/

def Block.reducing {α β : Bool → Type} {γ : Type} [Monoid γ] {b : Bool}
    (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (B : Block α b) : Set (β false × γ × β b) :=
  match _h : B.begin with
  | [] => f B.last
  | x :: xs => f x ∘ᵣ₂ Block.reducing f {B with begin := xs}
termination_by B.begin
decreasing_by
  · rw [_h]; decreasing_trivial

def Block.aborting {α β : Bool → Type} {γ : Type} [Monoid γ] {b : Bool}
    (f : ⦃b : Bool⦄ → α b → Set (β false × γ)) (g : ⦃b : Bool⦄ → α b → Set (β false × γ × β b))
    (B : Block α b) : Set (β false × γ) :=
  match _h : B.begin with
  | [] => f B.last
  | x :: xs => f x ∪ g x ∘ᵣ₁ Block.aborting f g {B with begin := xs}
termination_by B.begin
decreasing_by
  · rw [_h]; decreasing_trivial

def Block.diverging {α β : Bool → Type} {γ : Type} [Monoid γ] {b : Bool}
    (f : ⦃b : Bool⦄ → α b → Set (β false × γ)) (g : ⦃b : Bool⦄ → α b → Set (β false × γ × β b))
    (B : Block α b) : Set (β false × γ) :=
  match _h : B.begin with
  | [] => f B.last
  | x :: xs => f x ∪ g x ∘ᵣ₁ Block.diverging f g {B with begin := xs}
termination_by B.begin
decreasing_by
  · rw [_h]; decreasing_trivial

/-- A block of Guarded PlusCal statements, all of guard class `g`. -/
def Statement.blockReducing {g b : Bool} (B : Block (ComputableGuardedPlusCal.Statement g) b) :
    Set (LocalState V false × List (Behavior V) × LocalState V b) :=
  Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B

@[inherit_doc Statement.blockReducing]
def Statement.blockAborting {g b : Bool} (B : Block (ComputableGuardedPlusCal.Statement g) b) :
    Set (LocalState V false × List (Behavior V)) :=
  Block.aborting (λ ⦃_⦄ ↦ Statement.aborting) (λ ⦃_⦄ ↦ Statement.reducing) B

@[inherit_doc Statement.blockReducing]
def Statement.blockDiverging {g b : Bool} (B : Block (ComputableGuardedPlusCal.Statement g) b) :
    Set (LocalState V false × List (Behavior V)) :=
  Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) B

/-! # Reduction of atomic branches

  A branch is its precondition followed by its action. A branch with no precondition is the action
  alone, which is why the missing case composes with the identity relation rather than with `∅`.
-/

def AtomicBranch.reducing (B : ComputableGuardedPlusCal.AtomicBranch) :
    Set (LocalState V false × List (Behavior V) × LocalState V true) :=
  B.precondition.elim {⟨x, e, y⟩ | x = y ∧ e = 1} Statement.blockReducing ∘ᵣ₂
    Statement.blockReducing B.action

def AtomicBranch.aborting (B : ComputableGuardedPlusCal.AtomicBranch) :
    Set (LocalState V false × List (Behavior V)) :=
  match B.precondition with
  | .none => Statement.blockAborting B.action
  | .some B' =>
    Statement.blockAborting B' ∪ Statement.blockReducing B' ∘ᵣ₁ Statement.blockAborting B.action

def AtomicBranch.diverging (B : ComputableGuardedPlusCal.AtomicBranch) :
    Set (LocalState V false × List (Behavior V)) :=
  match B.precondition with
  | .none => Statement.blockDiverging B.action
  | .some B' =>
    Statement.blockDiverging B' ∪ Statement.blockReducing B' ∘ᵣ₁ Statement.blockDiverging B.action

end GuardedPlusCal

end
