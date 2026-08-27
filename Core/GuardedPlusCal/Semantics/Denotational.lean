module

public import Core.GuardedPlusCal.Syntax
public import Core.ComputableTLAPlus.Semantics.Interface
public import Extra.Rel
public import Extra.List
public import Extra.Seq

@[expose] public section

/-!
  The denotational semantics of Guarded PlusCal, as three relations per syntactic form: `reducing`
  (a step to a successor state, emitting a list of observable behaviors), `aborting` (a state from
  which the form goes wrong), and `diverging` (a state from which it runs forever).

  They are plain definitions rather than `Reduce`/`Abort`/`Diverge` instances, so the
  `⟦·⟧*`/`⟦·⟧⊥`/`⟦·⟧∞` notations do not apply here. Those classes take their second argument as an
  `outParam`, and with the value type abstract it occurs *only* there — nothing in a `Statement` or
  an `AtomicBranch` mentions it — so Lean cannot order the synthesis of the `ExprSemantics`
  argument. Nothing needs the classes: `StrongRefinement` takes the relations as plain `Set`s. The
  instances can be registered later, against the concrete TLA⁺ value type.

  Blocking and aborting are deliberately different: a statement with no `reducing` transition and no
  `aborting` state is a guard that is simply not enabled yet, which is what `await`, `receive` on an
  empty FIFO, and `with x ∈ {}` all are. That distinction is why `ExprSemantics` exposes `isBool`
  and `isSet` — without them a non-boolean guard would be indistinguishable from a false one.

  The expression layer underneath is abstract (`ComputableTLAPlus.ExprSemantics`), to be refined to
  the real TLA⁺ semantics later; see that file's module doc.

  Channels are kept out of the main memory, in a separate `FIFOs` map, so a local state is a
  variable memory beside a channel memory. An expression that reaches into a channel therefore has no
  meaning at all here rather than a wrong one, which is what lets the expression layer stay ignorant
  of channels entirely.

  This file stops at `AtomicBranch`. Threads, processes and algorithms are above it: a thread has no
  denotation of its own, only the labels it owns, and the process and algorithm layers are defined by
  fixed points over a step relation. See `Core/NetworkPlusCal/Semantics/Denotational.lean`'s
  `Thread.labels`.

  Failure modes a well-formedness side condition could assume away are stated instead: a `receive`
  with a bad channel, an `await` on a non-boolean and a `with x ∈ e` on a non-set all abort here
  rather than blocking or being ruled out by assumption.
-/

namespace GuardedPlusCal

open ComputableTLAPlus (Memory PathStep ExprSemantics OperatorEnv Model)

variable {V : Type} [ExprSemantics V] (Ξ : OperatorEnv) (Ω : Model V)

/-- The key identifying a single FIFO: the channel's name together with its resolved index path.
Only the name and the evaluated indices are observable, and this is also the shape a
`Behavior.send` reports. -/
abbrev ChanKey (V : Type) : Type := String × List (PathStep V)

/-- The name a process instance's own identity is bound to, matching `Elaborator/PlusCal.lean`'s
`extend "self" .address`. -/
def selfName : String := "self"

/-- One of the possible observable behaviors exhibited by PlusCal statements. Every event carries the
process instance that emitted it — the value bound to `selfName` in its memory — so that program
order within one process is recoverable from a trace that interleaves several. Without it, two
`print`s from different processes would be indistinguishable from two `print`s of the same process,
and their relative order would stop being observable.

`send` additionally carries the channel it pushes onto.

**Reception is not an event.** The alphabet is exactly `print` and `send`, and a `recv` event would
be unsound as an observation of the source program: `Guarded2Network` defers consumption to a `.rx`
thread that pops the channel ahead of the block that uses the value, so a block whose guard never
holds — `l: receive(ch, x) ; await FALSE ; goto l'` — pops a message in the target while the source
block never reduces at all and so never emits anything. No relation up to reordering repairs that:
the target event has no source counterpart to be reordered against. What ties the channel's contents
to the target's `inbox` is the refinement invariant `relatesTo`, per channel. -/
inductive Behavior (V : Type) : Type
  | print (p v : V)
  | send (p : V) (c : ChanKey V) (v : V)

/-- The trace alphabet: a possibly-infinite sequence of observable events. `Monoid (Seq α)` makes it
the ordered monoid traces are composed in.

Possibly-infinite and not `List`, even though no statement or block can emit an infinite trace —
`Statement.diverging` is `∅` and a block is finite, so divergence enters only at `Algebra`
(`Semantics/Process.lean`). A diverging algorithm that keeps sending emits forever, and a `List`
cannot hold what it emits: with a finite trace type `Algebra.diverging` could only contain
executions that fall silent after finitely many events, so every productive divergence would be
absent from the denotation outright.

The type is uniform across the statement, block and algorithm layers rather than finite below and
infinite above, so no layer boundary carries a `Seq.ofList` coercion. Finiteness of the reducing and
aborting traces is a derived property rather than a typing constraint: nothing downstream needs it,
and no proof relies on cancellativity (`Seq` has none — an infinite left factor absorbs its right
factor, `mul_eq_left_of_not_terminates`). -/
abbrev Trace (V : Type) : Type := Stream'.Seq (Behavior V)

/-- The global map containing FIFOs. Pushes go on the right, pops come off the left.

`Finmap` for the reason `Memory` is one (`Core/ComputableTLAPlus/Semantics/Interface.lean`): key
order is not observable, and letting it into the type turns commutation lemmas false. Updating a
channel is `insert` rather than `AList.replace` — every rule below establishes `F.lookup k = some _`
before writing `k`, so the two agree wherever either is reached, and `insert` is the one with a
usable `lookup` equation (`= some v`, not `v <$ lookup k F`). -/
abbrev FIFOs (V : Type) : Type := Finmap λ _ : ChanKey V ↦ List V

/-- The local reduction state of an atomic block: the process's own memory, the channels, and a
label field that is `none` while running and `some l` once a terminal `goto` has jumped to `l`.
`Statement b b'` already tracks terminality syntactically and the reduction relations pin the
label field's value (`none` on every source state, `some _` only on a `goto`'s target), so nothing
is gained by also carrying it at the type level — see `Statement.reducing` below.

There is deliberately no third component for `with`-bound temporaries. That an assignment does not
target a block-local binder is a syntactic property, checked by `WellFormedness`; keeping it in the
state would oblige every lemma to translate between two state shapes for no proof-side gain. -/
abbrev LocalState (V : Type) : Type := Memory V × FIFOs V × Option String

/-! Named projections. `LocalState` is a nested anonymous product, so its components are otherwise
reachable only as `σ.1`/`σ.2.1`/`σ.2.2` or by destructuring at every binding site. Named
projections let a proof `intro σₜ σₜ' ε σₛ` with no pattern at all and reach components by name,
destructuring only where it genuinely case-splits on the label. -/

/-- The memory component. -/
def LocalState.mem (σ : LocalState V) : Memory V := σ.1

/-- The FIFO component. -/
def LocalState.fifos (σ : LocalState V) : FIFOs V := σ.2.1

/-- The label component: `none` while running, `some l` once the block has jumped to `l`. -/
def LocalState.label (σ : LocalState V) : Option String := σ.2.2

omit [ExprSemantics V] in
@[simp] theorem LocalState.mem_mk (M : Memory V) (F : FIFOs V) (l : Option String) :
    LocalState.mem ⟨M, F, l⟩ = M := rfl

omit [ExprSemantics V] in
@[simp] theorem LocalState.fifos_mk (M : Memory V) (F : FIFOs V) (l : Option String) :
    LocalState.fifos ⟨M, F, l⟩ = F := rfl

omit [ExprSemantics V] in
@[simp] theorem LocalState.label_mk (M : Memory V) (F : FIFOs V) (l : Option String) :
    LocalState.label ⟨M, F, l⟩ = l := rfl

omit [ExprSemantics V] in
@[simp] theorem LocalState.mk_mem_fifos_label (σ : LocalState V) :
    (⟨σ.mem, σ.fifos, σ.label⟩ : LocalState V) = σ := rfl

/-- Resolving one segment of a reference's access path against a memory: a field segment resolves to
itself, an index expression to whatever it evaluates to. -/
inductive EvalStep (Ξ : OperatorEnv) (Ω : Model V) (M : Memory V) :
    (String ⊕ ComputablePlusCal.Expression) → PathStep V → Prop
  | field (f : String) : EvalStep Ξ Ω M (.inl f) (.inl f)
  | index {e : ComputablePlusCal.Expression} {v : V} :
      ExprSemantics.Eval Ξ Ω M e v → EvalStep Ξ Ω M (.inr e) (.inr v)

/-- Some index expression in a reference's access path has no value. Field segments cannot fail, so
only the `.inr` ones are considered. -/
def Ref.pathAborts (Ξ : OperatorEnv) (Ω : Model V) (M : Memory V)
    (r : ComputableGuardedPlusCal.Ref) : Prop :=
  ∃ e ∈ r.args.filterMap Sum.getRight?, ExprSemantics.Aborts Ξ Ω M e

/-! # Reduction of statements -/

def Statement.reducing (Ξ : OperatorEnv) (Ω : Model V) :
    {b b' : Bool} → ComputableGuardedPlusCal.Statement b b' →
    Set (LocalState V × Trace V × LocalState V)
  | true, false, .with name _ bound e =>
    {⟨σ, ε, σ'⟩ | ∃ M F v,
      ExprSemantics.Eval Ξ Ω M e v ∧
      Finmap.lookup name M = none ∧
      σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ match bound with
        -- `bound` is `true` for `=`, `false` for `∈`, the opposite polarity from the syntax's
        -- `«=|∈»` field.
        | true => σ' = ⟨M.insert name v, F, .none⟩
        | false => ∃ v', ExprSemantics.mem v' v ∧ σ' = ⟨M.insert name v', F, .none⟩
    }
  | true, false, .await e => test e ExprSemantics.tru
  | true, false, .receive c r coe =>
    {⟨σ, ε, σ'⟩ | ∃ M F M' cpath rpath v v' vs,
      List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
      List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧
      ExprSemantics.coerce coe v v' ∧
      Memory.update M r.name rpath v' = .some M' ∧
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M', F.insert ⟨c.name, cpath⟩ vs, .none⟩ ∧
      ε = 1
    }
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
  -- TODO(multicast): no semantics yet, so it neither steps nor aborts. The shape wanted here
  -- (whether the recipient set must enumerate to a finite list, and what order the emitted
  -- `Behavior.send`s come in) is fixed by what the refinement proof needs. `∅` rather than `sorry`,
  -- so the no-`sorry` check stays meaningful.
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
    {b b' : Bool} → ComputableGuardedPlusCal.Statement b b' →
    Set (LocalState V × Trace V)
  | true, false, .with _ _ bound e =>
    -- the states that fail to evaluate `e`
    {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    -- the states that evaluate `e` to a non-set when the binder is `∈`. An *empty* set is not an
    -- abort — it blocks.
    ∪ {⟨σ, ε⟩ | ∃ M F v, ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ match bound with
        | true => False
        | false => ¬ ExprSemantics.isSet v}
  | true, false, .await e =>
    {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F v, ¬ ExprSemantics.isBool v ∧ ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | true, false, .receive c r coe =>
    -- the target is not a process variable at all, or is shadowed by a temporary
    {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    -- an index expression of either reference has no value
    ∪ {⟨σ, ε⟩ | ∃ M F, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ Ref.pathAborts Ξ Ω M c}
    ∪ {⟨σ, ε⟩ | ∃ M F, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ Ref.pathAborts Ξ Ω M r}
    -- the channel resolves to no FIFO at all. Note an *empty* FIFO is not an abort — it blocks.
    ∪ {⟨σ, ε⟩ | ∃ M F cpath, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
        List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧ F.lookup ⟨c.name, cpath⟩ = .none}
    -- the dequeued value cannot be coerced to the target's type
    ∪ {⟨σ, ε⟩ | ∃ M F cpath v vs, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
        List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
        F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧ ¬ ∃ v', ExprSemantics.coerce coe v v'}
    -- the target's path does not resolve inside the target's current value
    ∪ {⟨σ, ε⟩ | ∃ M F cpath rpath v v' vs, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
        List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
        List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
        F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧ ExprSemantics.coerce coe v v' ∧
        Memory.update M r.name rpath v' = .none}
  | false, false, .skip => ∅
  | false, true, .goto _ => ∅
  | false, false, .print e => {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | false, false, .assert e =>
    -- the states that fail to evaluate `e`
    {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    -- the states that evaluate `e` to something other than `TRUE`
    ∪ {⟨σ, ε⟩ | ∃ M F v, v ≠ ExprSemantics.tru ∧ ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | false, false, .send c e =>
    {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts Ξ Ω M c ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
        F.lookup ⟨c.name, cpath⟩ = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  -- TODO(multicast): see `Statement.reducing`'s `multicast` case.
  | false, false, .multicast _ _ => ∅
  | false, false, .assign r e =>
    {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts Ξ Ω M r ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
    ∪ {⟨σ, ε⟩ | ∃ M F v rpath,
        ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
        Memory.update M r.name rpath v = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}

/-- No statement can diverge: every constructor of `Statement` is a single step. Divergence only
enters at the block and process levels. -/
def Statement.diverging : {b b' : Bool} → ComputableGuardedPlusCal.Statement b b' →
    Set (LocalState V × Trace V)
  | _, _, _ => ∅

/-- The states from which a guard-class statement is *blocked* — enabled by nothing yet, as opposed
to going wrong. Three cases: `await` on a boolean that is not `TRUE`, `with x ∈ e` on a (present but)
empty set, and `receive` on a channel that resolves to an empty FIFO. Every execution statement
blocks nowhere. The trace is `1`: a blocked guard emits nothing. -/
def Statement.blocking (Ξ : OperatorEnv) (Ω : Model V) :
    {b b' : Bool} → ComputableGuardedPlusCal.Statement b b' → Set (LocalState V × Trace V)
  | true, false, .with _ _ bound e =>
    {⟨σ, ε⟩ | ∃ M F v, ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
      match bound with
      | true => False
      | false => ExprSemantics.isSet v ∧ ¬ ∃ v', ExprSemantics.mem v' v}
  | true, false, .await e =>
    {⟨σ, ε⟩ | ∃ M F v, ExprSemantics.isBool v ∧ v ≠ ExprSemantics.tru ∧
      ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | true, false, .receive c _ _ =>
    {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some [] ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
  | _, _, _ => ∅

/-! # Reduction of blocks

  Generic over the index family and the state type: a block reduces by composing its elements'
  relations left to right, and aborts (or diverges) if any prefix reduces to a state from which the
  next element does. Nothing here mentions values, so these definitions are reused verbatim for
  `NetworkPlusCal`.
-/

/-- A possibly-empty *list* of statements as a relation. The one recursion in this section: a block
is this fold over its `begin`, composed with its `last`, and every equation about a block is a list
equation underneath.

A `Block` is non-empty by construction while a pass can hand back an empty run of statements
(`Guarded2Network`'s consumption assignments, for a branch that receives nothing), so the list form
has to exist in its own right — and being homogeneous in the guard index, it cannot express a block's
possibly-terminal `last`. That is the whole difference between the two.

`foldr`, not `foldl`: every proof about one of these is an induction on the list. -/
def Block.listReducing {α : Bool → Type} {β γ : Type} [Monoid γ]
    (f : ⦃b : Bool⦄ → α b → Set (β × γ × β)) (A : List (α false)) :
    Set (β × γ × β) :=
  A.foldr (f · ∘ᵣ₂ ·) Relation.Idle

/-- The list counterpart of `Block.aborting` — and of `Block.diverging` too. Those two are the same
function, so this one serves both, at whichever instantiation the caller passes
(`Block.diverging_prepend` is what states it under the diverging name). -/
def Block.listAborting {α : Bool → Type} {β γ : Type} [Monoid γ]
    (g : ⦃b : Bool⦄ → α b → Set (β × γ))
    (f : ⦃b : Bool⦄ → α b → Set (β × γ × β)) (A : List (α false)) :
    Set (β × γ) :=
  A.foldr (λ S sem ↦ g S ∪ f S ∘ᵣ₁ sem) ∅

/-- A block's `begin` run as a list, then its `last`. Not a recursion of its own: `Block.reducing`
and `Block.listReducing` computed the same fold before, differing only in that a block's last
statement may be terminal, and keeping two recursions meant every equation had to be proved twice
and bridged. -/
def Block.reducing {α : Bool → Type} {β γ : Type} [Monoid γ] {b : Bool}
    (f : ⦃b : Bool⦄ → α b → Set (β × γ × β)) (B : Block α b) : Set (β × γ × β) :=
  Block.listReducing f B.begin ∘ᵣ₂ f B.last

@[inherit_doc Block.reducing]
def Block.aborting {α : Bool → Type} {β γ : Type} [Monoid γ] {b : Bool}
    (f : ⦃b : Bool⦄ → α b → Set (β × γ)) (g : ⦃b : Bool⦄ → α b → Set (β × γ × β))
    (B : Block α b) : Set (β × γ) :=
  Block.listAborting f g B.begin ∪ Block.listReducing g B.begin ∘ᵣ₁ f B.last

@[inherit_doc Block.reducing]
def Block.diverging {α : Bool → Type} {β γ : Type} [Monoid γ] {b : Bool}
    (f : ⦃b : Bool⦄ → α b → Set (β × γ)) (g : ⦃b : Bool⦄ → α b → Set (β × γ × β))
    (B : Block α b) : Set (β × γ) :=
  Block.listAborting f g B.begin ∪ Block.listReducing g B.begin ∘ᵣ₁ f B.last

/-- A block of Guarded PlusCal statements, all of guard class `g`. -/
def Statement.blockReducing (Ξ : OperatorEnv) (Ω : Model V) {g b : Bool}
    (B : Block (ComputableGuardedPlusCal.Statement g) b) :
    Set (LocalState V × Trace V × LocalState V) :=
  Block.reducing (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) B

@[inherit_doc Statement.blockReducing]
def Statement.blockAborting (Ξ : OperatorEnv) (Ω : Model V) {g b : Bool}
    (B : Block (ComputableGuardedPlusCal.Statement g) b) :
    Set (LocalState V × Trace V) :=
  Block.aborting (λ ⦃_⦄ ↦ Statement.aborting Ξ Ω)
    (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) B

@[inherit_doc Statement.blockReducing]
def Statement.blockDiverging (Ξ : OperatorEnv) (Ω : Model V) {g b : Bool}
    (B : Block (ComputableGuardedPlusCal.Statement g) b) :
    Set (LocalState V × Trace V) :=
  Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) B

@[inherit_doc Statement.blockReducing]
def Statement.blockBlocking (Ξ : OperatorEnv) (Ω : Model V) {g b : Bool}
    (B : Block (ComputableGuardedPlusCal.Statement g) b) :
    Set (LocalState V × Trace V) :=
  Block.aborting (λ ⦃_⦄ ↦ Statement.blocking Ξ Ω) (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) B

/-! # Reduction of atomic branches

  A branch is its precondition followed by its action. A branch with no precondition is the action
  alone, which is why the missing case composes with the identity relation rather than with `∅`.
-/

def AtomicBranch.reducing (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableGuardedPlusCal.AtomicBranch) :
    Set (LocalState V × Trace V × LocalState V) :=
  B.precondition.elim Relation.Idle (Statement.blockReducing Ξ Ω) ∘ᵣ₂
    Statement.blockReducing Ξ Ω B.action

def AtomicBranch.aborting (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableGuardedPlusCal.AtomicBranch) :
    Set (LocalState V × Trace V) :=
  match B.precondition with
  | .none => Statement.blockAborting Ξ Ω B.action
  | .some B' =>
    Statement.blockAborting Ξ Ω B' ∪
      Statement.blockReducing Ξ Ω B' ∘ᵣ₁ Statement.blockAborting Ξ Ω B.action

def AtomicBranch.diverging (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableGuardedPlusCal.AtomicBranch) :
    Set (LocalState V × Trace V) :=
  match B.precondition with
  | .none => Statement.blockDiverging Ξ Ω B.action
  | .some B' =>
    Statement.blockDiverging Ξ Ω B' ∪
      Statement.blockReducing Ξ Ω B' ∘ᵣ₁ Statement.blockDiverging Ξ Ω B.action

/-- The states from which an atomic branch is *blocked*: its precondition reduces to a state at
which some later guard blocks. A branch with no precondition — a bare action — blocks nowhere, since
an execution statement never blocks. -/
def AtomicBranch.blocking (Ξ : OperatorEnv) (Ω : Model V)
    (B : ComputableGuardedPlusCal.AtomicBranch) :
    Set (LocalState V × Trace V) :=
  match B.precondition with
  | .none => Statement.blockBlocking Ξ Ω B.action
  | .some B' =>
    Statement.blockBlocking Ξ Ω B' ∪
      Statement.blockReducing Ξ Ω B' ∘ᵣ₁ Statement.blockBlocking Ξ Ω B.action

end GuardedPlusCal

end
