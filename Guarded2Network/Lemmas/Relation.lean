module

public import Guarded2Network.Lemmas.Seq
public import Core.NetworkPlusCal.Semantics.Lemmas
public import Core.NetworkPlusCal.Semantics.Process

@[expose] public section

/-!
  The refinement invariant relating a `GuardedPlusCal` local state to the `NetworkPlusCal` state
  the pass compiles it into, and the named API every later lemma reaches it through.

  **What it says.** Everything is equal except the one channel the process receives from and the
  `inbox` the pass introduced for it. There, the target has already drained some prefix of the
  channel into `inbox`, so the source's FIFO is the target's `inbox` followed by the target's FIFO —
  `F₁[c] = inbox ++ F₂[c]`. That single equation is what carries reception across the pass: since
  reception is not an observable event (see `Behavior` in `Core/GuardedPlusCal/Semantics/
  Denotational.lean`), nothing in the trace records where a message went, and this invariant is the
  only place saying it went nowhere else.

  **One channel, not a channel per shape.** `WellFormedness/Restrictions.lean`'s
  `checkReceiveChannels` establishes that a process receives from exactly one channel, so `mbox`
  carries one `Ref` — `none` for a process that never receives, in which case the two states are
  equal outright. The channel is a `Ref` (name plus an already-resolvable index path) rather than
  prior art's raw `Expression`, so the two syntactic cases prior art had to split on (`c` and
  `c[self]`, with a `mailbox_shape` lemma to case on them) collapse into one: `EvalStep` resolves
  `Ref.args` uniformly, whether the list is empty or not.

  **Why an API and not a raw ∧-chain.** Prior art destructures this predicate inline at every use
  and navigates it positionally (`conv at sim => enter [2, 2, 2, 2]`). Each projection below is one
  of those coordinates, named. A `conv … enter` into a conjunction is a `rw [show … from rfl]` in
  disguise: it silently depends on the order the conjuncts happen to be written in, and every
  reordering of this definition would break proofs that never mention it.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Memory)
open GuardedPlusCal (AlgState ChanKey EvalStep FIFOs LocalState' ProcState)

variable {V : Type} [ExprSemantics V]

/-- The channel a process receives from, paired with the `inbox` variable `Guarded2Network` gave it
— `none` when the process contains no `receive` at all and so got neither. -/
abbrev Mailbox : Type := Option (ComputableGuardedPlusCal.Ref × String)

/-- Relates a `GuardedPlusCal` state to the `NetworkPlusCal` state refining it. Both languages
share one state space (`Core/NetworkPlusCal/Semantics/Denotational.lean`), so this is a relation on
one type; the `ₛ`/`ₜ` naming is what keeps the two roles apart.

**Two roles, two treatments.** At every channel *other* than this process's own, the source's queue
is the target's with `pref k` in front — some other instance's `inbox`, which this process cannot
observe. That prefix is a *parameter* rather than an existential on purpose: the algorithm level
needs those keys to come back unchanged after a block runs, and "the same `pref` on both sides" is
the only way to say so. An existential would let the conclusion re-witness, and the fact would be
true but unstatable. (Prior art wrote this clause as plain equality, i.e. `pref k = []`; that is
false as soon as a second instance receives, which is the bug this parameter fixes.)

At this process's *own* channel the prefix is its `inbox`, tied to the target's memory by
`isSeq sv vs` and existential — because it is the one prefix the process itself changes, a `receive`
shrinking it. Keeping it out of `pref` is what leaves the relation closed under `receive`, so the
block layer's refinement stays a single-relation `StrongRefinement`.

A `send` is insensitive to either — it appends at the *back*, behind whatever prefix is in front. -/
def relatesTo (mbox : Mailbox) (pref : ChanKey V → List V) : Rel (LocalState' V) (LocalState' V) :=
  λ σₛ σₜ ↦
    σₛ.label = σₜ.label ∧
    match mbox with
    | .none =>
      σₛ.mem = σₜ.mem ∧
      ∀ k : ChanKey V, σₛ.fifos.lookup k = (pref k ++ ·) <$> σₜ.fifos.lookup k
    | .some (c, inbox) =>
      (∀ x ≠ inbox, σₛ.mem.lookup x = σₜ.mem.lookup x) ∧
      ∃ cpath sv vs,
        List.Forall₂ (EvalStep σₛ.mem) c.args cpath ∧
        σₜ.mem.lookup inbox = .some sv ∧ ExprSemantics.isSeq sv vs ∧
        (∀ k ≠ (⟨c.name, cpath⟩ : ChanKey V),
          σₛ.fifos.lookup k = (pref k ++ ·) <$> σₜ.fifos.lookup k) ∧
        σₛ.fifos.lookup ⟨c.name, cpath⟩ = (vs ++ ·) <$> σₜ.fifos.lookup ⟨c.name, cpath⟩

@[inherit_doc relatesTo]
scoped notation:60 σₛ:60 " ∼[" mbox:0 ", " pref:0 "] " σₜ:60 =>
  Guarded2Network.relatesTo mbox pref σₛ σₜ

/-! ## Introduction -/

/-- A process with no `receive` has a memory equal to the source's. Its channels still carry the
prefixes *other* instances have drained, which is why the FIFO hypothesis is not equality. -/
theorem relatesTo.none_intro {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (hl : σₛ.label = σₜ.label) (hm : σₛ.mem = σₜ.mem)
    (hf : ∀ k : ChanKey V, σₛ.fifos.lookup k = (pref k ++ ·) <$> σₜ.fifos.lookup k) :
    σₛ ∼[.none, pref] σₜ :=
  ⟨hl, hm, hf⟩

/-- The receiving case, one hypothesis per conjunct — the introduction form every construction site
uses instead of assembling the nested anonymous constructor by hand. -/
theorem relatesTo.chan_intro {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    {c : ComputableGuardedPlusCal.Ref}
    {inbox : String} {cpath : List (ComputableTLAPlus.PathStep V)} {sv : V} {vs : List V}
    (hl : σₛ.label = σₜ.label)
    (hm : ∀ x ≠ inbox, σₛ.mem.lookup x = σₜ.mem.lookup x)
    (hpath : List.Forall₂ (EvalStep σₛ.mem) c.args cpath)
    (hinbox : σₜ.mem.lookup inbox = .some sv) (hseq : ExprSemantics.isSeq sv vs)
    (hoff : ∀ k ≠ (⟨c.name, cpath⟩ : ChanKey V),
      σₛ.fifos.lookup k = (pref k ++ ·) <$> σₜ.fifos.lookup k)
    (hsplit : σₛ.fifos.lookup ⟨c.name, cpath⟩ = (vs ++ ·) <$> σₜ.fifos.lookup ⟨c.name, cpath⟩) :
    σₛ ∼[.some (c, inbox), pref] σₜ :=
  ⟨hl, hm, cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩

/-! ## Projections

  One per conjunct, in definition order. `label_eq` is the only one that holds in both cases, which
  is why it sits outside the `match` in the definition: a block-level lemma needs it without knowing
  whether the process receives at all.
-/

/-- Source and target agree on which label the block ended at — in both cases of `mbox`. -/
theorem relatesTo.label_eq {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[mbox, pref] σₜ) : σₛ.label = σₜ.label := h.1

/-- With no mailbox, the memories are equal. -/
theorem relatesTo.mem_eq {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[.none, pref] σₜ) : σₛ.mem = σₜ.mem := h.2.1

/-- With no mailbox there is no own channel to except, so every key carries `pref`. -/
theorem relatesTo.none_fifo_split {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[.none, pref] σₜ) (k : ChanKey V) :
    σₛ.fifos.lookup k = (pref k ++ ·) <$> σₜ.fifos.lookup k := h.2.2 k

/-- Memory agreement in both cases at once: away from the generated `inbox` — of which there is none
when the process never receives — the memories agree. This is what lets a simulation over an
arbitrary `mbox` stop case-splitting on the mailbox to read the memory half. -/
theorem relatesTo.mem_agree' {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[mbox, pref] σₜ) :
    ∀ x, (∀ c inbox, mbox = .some (c, inbox) → x ≠ inbox) →
      σₛ.mem.lookup x = σₜ.mem.lookup x := by
  match mbox with
  | .none => exact λ x _ ↦ by rw [h.mem_eq]
  | .some (c, inbox) => exact λ x hx ↦ h.2.1 x (hx c inbox rfl)

/-- **The equation the whole proof turns on**, read uniformly: at every key the source's queue is
the target's behind *some* prefix — this process's own `inbox` at its own channel, `pref k` at every
other. Reception has no trace event, so this is the only statement that a message the target moved
out of a channel is still accounted for.

The prefix is existential because which of the two clauses applies depends on the key, and no
statement below `receive` cares which. Where a proof needs the prefix pinned it takes the clause it
wants directly, through `inbox_seq`. -/
theorem relatesTo.fifo_prefix {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[mbox, pref] σₜ) (k : ChanKey V) :
    ∃ ws, σₛ.fifos.lookup k = (ws ++ ·) <$> σₜ.fifos.lookup k := by
  match mbox with
  | .none => exact ⟨pref k, h.none_fifo_split k⟩
  | .some (c, inbox) =>
    obtain ⟨cpath, sv, vs, -, -, -, hoff, hsplit⟩ := h.2.2
    by_cases hk : k = ⟨c.name, cpath⟩
    · subst hk
      exact ⟨vs, hsplit⟩
    · exact ⟨pref k, hoff k hk⟩

/-! ## Transport

  A statement-level simulation ends by rebuilding the relation over the state its step produced. Each
  kind of change is invisible to some part of the relation, and saying which part once — here, rather
  than per constructor — is what lets those proofs stop case-splitting on `mbox`.
-/

/-- **Transporting the FIFO half.** A change that keeps every key's prefix working keeps the
relation: the hypothesis is stated over an arbitrary prefix so that one instance of it serves both
FIFO clauses — `pref k` away from this process's channel, its `inbox` at it. -/
theorem relatesTo.fifo_congr {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[mbox, pref] σₜ) {F₁ F₂ : FIFOs V}
    (hf : ∀ (k : ChanKey V) (ws : List V),
      σₛ.fifos.lookup k = (ws ++ ·) <$> σₜ.fifos.lookup k →
      F₁.lookup k = (ws ++ ·) <$> F₂.lookup k) (l : Option String) :
    (⟨σₛ.mem, F₁, l⟩ : LocalState' V) ∼[mbox, pref] ⟨σₜ.mem, F₂, l⟩ := by
  refine ⟨rfl, ?_⟩
  match mbox with
  | .none => exact ⟨h.mem_eq, λ k ↦ hf k (pref k) (h.none_fifo_split k)⟩
  | .some (c, inbox) =>
    obtain ⟨cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩ := h.2.2
    exact ⟨h.2.1, cpath, sv, vs, hpath, hinbox, hseq,
      λ k hk ↦ hf k (pref k) (hoff k hk), hf _ vs hsplit⟩

/-- Moving both states to the same label. The label sits outside the `match` precisely so that this
holds without knowing whether the process receives, and the statements that neither write memory nor
push a queue are exactly this lemma. -/
theorem relatesTo.label_congr {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[mbox, pref] σₜ) (l : Option String) :
    (⟨σₛ.mem, σₛ.fifos, l⟩ : LocalState' V) ∼[mbox, pref] ⟨σₜ.mem, σₜ.fifos, l⟩ :=
  h.fifo_congr (λ _ _ hk ↦ hk) l

/-- The queue a `send` writes to exists in the source exactly when it exists in the target, and
holds the target's contents behind whatever this key's prefix is. Supplies `fifo_push`'s `ws`. -/
theorem relatesTo.fifo_lookup {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[mbox, pref] σₜ) {k : ChanKey V} {vs : List V}
    (hlk : σₜ.fifos.lookup k = .some vs) : ∃ ws, σₛ.fifos.lookup k = .some (ws ++ vs) := by
  obtain ⟨ws, hws⟩ := h.fifo_prefix k
  rw [hlk] at hws
  exact ⟨ws, hws⟩

/-- And the aborting direction: a queue missing in the target is missing in the source, which is
what carries `send`'s "no such channel" abort across the pass. -/
theorem relatesTo.fifo_lookup_none {mbox : Mailbox} {pref : ChanKey V → List V}
    {σₛ σₜ : LocalState' V} (h : σₛ ∼[mbox, pref] σₜ) {k : ChanKey V}
    (hlk : σₜ.fifos.lookup k = .none) : σₛ.fifos.lookup k = .none := by
  obtain ⟨ws, hws⟩ := h.fifo_prefix k
  rwa [hlk] at hws

/-- A `send`, and the reason the prefix costs nothing: it appends at the *back* of a queue, behind
whatever has been drained off the front, so the same value lands after the same prefix on both
sides. The key sent to needs no comparison with this process's own channel — the prefix `ws` is
whichever of the two clauses applies, and the two lookups pin it. -/
theorem relatesTo.fifo_push {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[mbox, pref] σₜ) {k : ChanKey V} {ws vs : List V}
    (hlk : σₜ.fifos.lookup k = .some vs) (hlk₁ : σₛ.fifos.lookup k = .some (ws ++ vs)) (v : V)
    (l : Option String) :
    (⟨σₛ.mem, σₛ.fifos.insert k ((ws ++ vs).concat v), l⟩ : LocalState' V) ∼[mbox, pref]
      ⟨σₜ.mem, σₜ.fifos.insert k (vs.concat v), l⟩ := by
  refine h.fifo_congr (λ k' us hus ↦ ?_) l
  by_cases hk : k' = k
  · subst hk
    simp only [hlk, hlk₁, Option.map_eq_map, Option.map_some, Option.some.injEq] at hus
    obtain rfl : us = ws := (List.append_cancel_right hus).symm
    simp only [Finmap.lookup_insert, Option.map_eq_map, Option.map_some, List.concat_eq_append,
      List.append_assoc]
  · rw [Finmap.lookup_insert_of_ne _ hk, Finmap.lookup_insert_of_ne _ hk]
    exact hus

section Chan

variable {σₛ σₜ : LocalState' V} {c : ComputableGuardedPlusCal.Ref} {inbox : String}
  {pref : ChanKey V → List V}

/-- The memories agree on every name but `inbox` — the pass introduces exactly one variable, and
`freshName` is what makes "every name but that one" a statement about the source program's names at
all. -/
theorem relatesTo.mem_agree (h : σₛ ∼[.some (c, inbox), pref] σₜ) :
    ∀ x ≠ inbox, σₛ.mem.lookup x = σₜ.mem.lookup x := h.2.1

/-- This process's own channel, in one package: where it resolves to, what its `inbox` holds, and
the two FIFO clauses — `pref` away from that key, the `inbox` at it. Everything below is stated
against the same `cpath` this produces, so a proof destructures it once and reuses the witnesses. -/
theorem relatesTo.inbox_seq (h : σₛ ∼[.some (c, inbox), pref] σₜ) :
    ∃ cpath sv vs,
      List.Forall₂ (EvalStep σₛ.mem) c.args cpath ∧
      σₜ.mem.lookup inbox = .some sv ∧ ExprSemantics.isSeq sv vs ∧
      (∀ k ≠ (⟨c.name, cpath⟩ : ChanKey V),
        σₛ.fifos.lookup k = (pref k ++ ·) <$> σₜ.fifos.lookup k) ∧
      σₛ.fifos.lookup ⟨c.name, cpath⟩ =
        (vs ++ ·) <$> σₜ.fifos.lookup ⟨c.name, cpath⟩ := h.2.2

/-- The split at this process's own channel, read off a resolved path already in hand.
`EvalStep.path_inj` is what makes "this process's channel" well defined. -/
theorem relatesTo.inbox_contents (h : σₛ ∼[.some (c, inbox), pref] σₜ)
    {cpath : List (ComputableTLAPlus.PathStep V)} {sv : V}
    (hpath : List.Forall₂ (EvalStep σₛ.mem) c.args cpath)
    (hinbox : σₜ.mem.lookup inbox = .some sv) :
    ∃ vs, ExprSemantics.isSeq sv vs ∧
      σₛ.fifos.lookup ⟨c.name, cpath⟩ = (vs ++ ·) <$> σₜ.fifos.lookup ⟨c.name, cpath⟩ := by
  obtain ⟨cpath', sv', vs, hpath', hinbox', hseq', -, hsplit'⟩ := h.inbox_seq
  obtain rfl := EvalStep.path_inj hpath' hpath
  rw [hinbox] at hinbox'
  obtain rfl := Option.some.inj hinbox'
  exact ⟨vs, hseq', hsplit'⟩

end Chan

/-! # The algorithm level

  `relatesTo` relates one atomic block's local state. `≋` relates a whole `AlgState`: every process
  instance's own state, plus the one FIFO map they all share.

  **What the shared FIFO map costs.** Each instance has drained a prefix of *its own* channel into
  *its own* `inbox`, so the source's FIFO map is the target's with each instance's inbox prepended
  to that instance's key — one prepend per key, provided no two instances share a key. They do not:
  a process set must index its channel by `self` (`WellFormednessError.mailboxNotIndexedBySelf`),
  which is exactly what makes `keys_inj` below hold rather than being an extra hypothesis dragged
  through the proof. Without it the source queue at a shared key would have to be some interleaving
  of several inboxes with nothing fixing the order, and no relation of this shape could be written
  at all.

  **Why the witnesses are a function, not an existential per instance.** `InboxState` bundles the
  key an instance receives on with what its inbox currently holds. Quantifying `ib : ι → Option
  (InboxState V)` once, outside the per-instance clauses, is what lets the FIFO clauses talk about
  *all* keys at once — an existential inside each instance's clause would give each instance its own
  witness with nothing relating them, and the map-level statement could not be phrased.

  **Labels.** The target has the source's threads plus one `.rx` thread per channel, so its label set
  is the source's together with those threads' labels — `rx p`, supplied per instance by whatever
  builds this relation from a compiled algorithm. The disjointness clause is what says the `.rx`
  labels are genuinely new, which `freshName` guarantees at the syntax level.
-/

/-- What one instance's `inbox` accounts for: the FIFO key it receives on, and the values it has
already taken off that FIFO but not yet consumed. -/
structure InboxState (V : Type) : Type where
  /-- The resolved key of the channel this instance receives on. -/
  key : ChanKey V
  /-- What the instance's `inbox` currently holds, in FIFO order. -/
  contents : List V

/-- One process instance's state, related. `ib` is `none` exactly when `mb` is: an instance with no
`receive` got no `inbox`, and its memory is equal to the source's rather than equal-off-`inbox`. -/
def procRelatesTo (mb : Mailbox) (rx : Set String) (ib : Option (InboxState V)) :
    Rel (ProcState V) (ProcState V) :=
  λ ⟨M₁, L₁⟩ ⟨M₂, L₂⟩ ↦
    L₂ = L₁ ∪ rx ∧ Disjoint L₁ rx ∧
    match mb, ib with
    | .none, .none => M₁ = M₂
    | .some (c, inbox), .some ib =>
      (∀ x ≠ inbox, M₁.lookup x = M₂.lookup x) ∧
      (∃ sv, M₂.lookup inbox = .some sv ∧ ExprSemantics.isSeq sv ib.contents) ∧
      (∃ cpath, List.Forall₂ (EvalStep M₁) c.args cpath ∧ ib.key = ⟨c.name, cpath⟩)
    | _, _ => False

/-- Memory agreement at one instance, in both cases of the mailbox at once — `relatesTo.mem_agree'`
one level up, and stated the same way so that a caller need not know whether the process receives.

What the algorithm level reads through it is `selfName`: a process only steps in a memory binding its
own identity (`CodeTable.procReducing`), the target's does, and the source's agrees with it there
because the pass's generated `inbox` is not `self`. -/
theorem procRelatesTo.mem_agree' {mb : Mailbox} {rx : Set String} {ib : Option (InboxState V)}
    {M₁ M₂ : Memory V} {L₁ L₂ : Set String}
    (h : procRelatesTo mb rx ib ⟨M₁, L₁⟩ ⟨M₂, L₂⟩) :
    ∀ x, (∀ c inbox, mb = .some (c, inbox) → x ≠ inbox) → M₁.lookup x = M₂.lookup x := by
  obtain ⟨-, -, hmatch⟩ := h
  match mb, ib with
  | .none, .none => exact λ x _ ↦ by rw [hmatch]
  | .some (c, inbox), .some _ => exact λ x hx ↦ hmatch.1 x (hx c inbox rfl)
  | .none, .some _ => exact hmatch.elim
  | .some _, .none => exact hmatch.elim

/-- The algorithm-level lift of `relatesTo`: same instances, each instance's state related, and one
FIFO map split per key.

The split is carried by a `pref` function — the same one `relatesTo` takes — with two clauses tying
it to `ib`: at a key some instance receives on it is that instance's inbox, and where nobody
receives it is empty. That is what makes picking a process hand `relatesTo` its `pref` directly,
with no bridge: `relatesTo` reads `pref` at every key *but* the picked process's own, where it uses
its own `inbox` instead — which is exactly the clause `ib` already pins.

**Both sides are `Instances.Functional`**, and that is not bookkeeping. `ib` gives one `InboxState`
per instance, so an algorithm state holding two states for one instance would account both against
one inbox; the instance's step then updates that accounting while the second state, which did not
move, is left related against the old one. The per-step obligation is *false* at such a state, not
merely unprovable. Carried here rather than as a reachability side condition, so that the framework's
own `Terminating`/`star` laws propagate it with everything else — `relatesTo` being both pre- and
post-relation, a clause of it is exactly an invariant. -/
def algRelatesTo {ι : Type} (mb : ι → Mailbox) (rx : ι → Set String) :
    Rel (AlgState ι V) (AlgState ι V) :=
  λ ⟨Ps, F₁⟩ ⟨Qs, F₂⟩ ↦
    ∃ (ib : ι → Option (InboxState V)) (pref : ChanKey V → List V),
      -- one state per instance, on both sides
      Ps.Functional ∧ Qs.Functional ∧
      -- the same instances on both sides, pairwise related
      (∀ p σ, ⟨p, σ⟩ ∈ Ps → ∃ σ', ⟨p, σ'⟩ ∈ Qs ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ') ∧
      (∀ p σ', ⟨p, σ'⟩ ∈ Qs → ∃ σ, ⟨p, σ⟩ ∈ Ps ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ') ∧
      -- an index that names no instance of this state accounts for nothing: without this the
      -- witness could invent an inbox for an absent instance and the FIFO clauses below would
      -- demand a split no state satisfies
      (∀ p, (∀ σ, ⟨p, σ⟩ ∉ Ps) → ib p = .none) ∧
      -- no two instances receive on the same key
      (∀ p q x y, ib p = .some x → ib q = .some y → x.key = y.key → p = q) ∧
      -- a key someone receives on carries that instance's inbox
      (∀ p x, ib p = .some x → pref x.key = x.contents) ∧
      -- a key nobody receives on carries nothing
      (∀ k : ChanKey V, (∀ p x, ib p = .some x → x.key ≠ k) → pref k = []) ∧
      -- and that accounts for the whole FIFO map, in one equation
      (∀ k : ChanKey V, F₁.lookup k = (pref k ++ ·) <$> F₂.lookup k)

@[inherit_doc algRelatesTo]
scoped notation:60 Sₛ:60 " ≋[" mb:0 ", " rx:0 "] " Sₜ:60 => Guarded2Network.algRelatesTo mb rx Sₛ Sₜ

namespace algRelatesTo

variable {ι : Type} {mb : ι → Mailbox} {rx : ι → Set String} {Sₛ Sₜ : AlgState ι V}

/-- Each side holds one state per instance. -/
theorem functional (h : Sₛ ≋[mb, rx] Sₜ) : Sₛ.1.Functional ∧ Sₜ.1.Functional := by
  obtain ⟨-, -, hfs, hft, -, -, -, -, -, -, -⟩ := h
  exact ⟨hfs, hft⟩

/-- Every source instance has a related target instance. -/
theorem forward (h : Sₛ ≋[mb, rx] Sₜ) :
    ∃ ib : ι → Option (InboxState V), ∀ p σ, ⟨p, σ⟩ ∈ Sₛ.1 →
      ∃ σ', ⟨p, σ'⟩ ∈ Sₜ.1 ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ' := by
  obtain ⟨ib, -, -, -, hfwd, -, -, -, -, -, -⟩ := h
  exact ⟨ib, hfwd⟩

/-- Every target instance has a related source instance — the direction that rules out the target
inventing an instance the source never had. -/
theorem backward (h : Sₛ ≋[mb, rx] Sₜ) :
    ∃ ib : ι → Option (InboxState V), ∀ p σ', ⟨p, σ'⟩ ∈ Sₜ.1 →
      ∃ σ, ⟨p, σ⟩ ∈ Sₛ.1 ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ' := by
  obtain ⟨ib, -, -, -, -, hbwd, -, -, -, -, -⟩ := h
  exact ⟨ib, hbwd⟩

/-- The whole FIFO map, in one statement: every key is the target's queue with `pref` in front, and
`pref` is the inbox of the one instance receiving on that key, or empty. The `ib` witness is shared
with `forward`/`backward`, which is what makes this composable with them rather than a separate
fact. -/
theorem fifos (h : Sₛ ≋[mb, rx] Sₜ) :
    ∃ (ib : ι → Option (InboxState V)) (pref : ChanKey V → List V),
      (∀ p q x y, ib p = .some x → ib q = .some y → x.key = y.key → p = q) ∧
      (∀ p x, ib p = .some x → pref x.key = x.contents) ∧
      (∀ k : ChanKey V, (∀ p x, ib p = .some x → x.key ≠ k) → pref k = []) ∧
      (∀ k : ChanKey V, Sₛ.2.lookup k = (pref k ++ ·) <$> Sₜ.2.lookup k) := by
  obtain ⟨ib, pref, -, -, -, -, -, hinj, hkey, hoff, hfifo⟩ := h
  exact ⟨ib, pref, hinj, hkey, hoff, hfifo⟩

/-- The introduction form: one hypothesis per clause, against a single choice of witnesses. -/
theorem intro {ib : ι → Option (InboxState V)} {pref : ChanKey V → List V}
    (hfs : Sₛ.1.Functional) (hft : Sₜ.1.Functional)
    (hfwd : ∀ p σ, ⟨p, σ⟩ ∈ Sₛ.1 → ∃ σ', ⟨p, σ'⟩ ∈ Sₜ.1 ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ')
    (hbwd : ∀ p σ', ⟨p, σ'⟩ ∈ Sₜ.1 → ∃ σ, ⟨p, σ⟩ ∈ Sₛ.1 ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ')
    (habsent : ∀ p, (∀ σ, ⟨p, σ⟩ ∉ Sₛ.1) → ib p = .none)
    (hinj : ∀ p q x y, ib p = .some x → ib q = .some y → x.key = y.key → p = q)
    (hkey : ∀ p x, ib p = .some x → pref x.key = x.contents)
    (hoff : ∀ k : ChanKey V, (∀ p x, ib p = .some x → x.key ≠ k) → pref k = [])
    (hfifo : ∀ k : ChanKey V, Sₛ.2.lookup k = (pref k ++ ·) <$> Sₜ.2.lookup k) :
    Sₛ ≋[mb, rx] Sₜ :=
  ⟨ib, pref, hfs, hft, hfwd, hbwd, habsent, hinj, hkey, hoff, hfifo⟩

/-- An instance whose process contains no `receive` has no inbox to account for — so the mailbox
being `none` (a syntactic fact about the compiled process) forces the witness to be `none` too, and
none of the FIFO clauses mention that instance. Needs the instance to be present, which is what
`forward` supplies. -/
theorem inbox_none {ib : ι → Option (InboxState V)} {p : ι} {σ σ' : ProcState V}
    (hmb : mb p = .none) (h : procRelatesTo (mb p) (rx p) (ib p) σ σ') : ib p = .none := by
  obtain ⟨M₁, L₁⟩ := σ
  obtain ⟨M₂, L₂⟩ := σ'
  obtain ⟨-, -, hmatch⟩ := h
  rw [hmb] at hmatch
  match hib : ib p with
  | .none => rfl
  | .some _ => rw [hib] at hmatch; contradiction

end algRelatesTo

end Guarded2Network

end
