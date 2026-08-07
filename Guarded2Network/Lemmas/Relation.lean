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
one type; the `ₛ`/`ₜ` naming is what keeps the two roles apart. -/
def relatesTo (mbox : Mailbox) : Rel (LocalState' V) (LocalState' V) :=
  λ σₛ σₜ ↦
    σₛ.label = σₜ.label ∧
    match mbox with
    | .none => σₛ.mem = σₜ.mem ∧ σₛ.fifos = σₜ.fifos
    | .some (c, inbox) =>
      (∀ x ≠ inbox, σₛ.mem.lookup x = σₜ.mem.lookup x) ∧
      ∃ cpath sv vs,
        List.Forall₂ (EvalStep σₛ.mem) c.args cpath ∧
        σₜ.mem.lookup inbox = .some sv ∧ ExprSemantics.isSeq sv vs ∧
        (∀ k ≠ (⟨c.name, cpath⟩ : ChanKey V), σₛ.fifos.lookup k = σₜ.fifos.lookup k) ∧
        σₛ.fifos.lookup ⟨c.name, cpath⟩ = (vs ++ ·) <$> σₜ.fifos.lookup ⟨c.name, cpath⟩

@[inherit_doc relatesTo]
scoped notation:60 σₛ:60 " ∼[" mbox:0 "] " σₜ:60 => Guarded2Network.relatesTo mbox σₛ σₜ

/-! ## Introduction -/

/-- A process with no `receive` compiles to one whose states are equal to the source's. -/
theorem relatesTo.none_intro {σₛ σₜ : LocalState' V} (hl : σₛ.label = σₜ.label)
    (hm : σₛ.mem = σₜ.mem) (hf : σₛ.fifos = σₜ.fifos) : σₛ ∼[.none] σₜ :=
  ⟨hl, hm, hf⟩

/-- The receiving case, one hypothesis per conjunct — the introduction form every construction site
uses instead of assembling the nested anonymous constructor by hand. -/
theorem relatesTo.chan_intro {σₛ σₜ : LocalState' V} {c : ComputableGuardedPlusCal.Ref}
    {inbox : String} {cpath : List (ComputableTLAPlus.PathStep V)} {sv : V} {vs : List V}
    (hl : σₛ.label = σₜ.label)
    (hm : ∀ x ≠ inbox, σₛ.mem.lookup x = σₜ.mem.lookup x)
    (hpath : List.Forall₂ (EvalStep σₛ.mem) c.args cpath)
    (hinbox : σₜ.mem.lookup inbox = .some sv) (hseq : ExprSemantics.isSeq sv vs)
    (hoff : ∀ k ≠ (⟨c.name, cpath⟩ : ChanKey V), σₛ.fifos.lookup k = σₜ.fifos.lookup k)
    (hsplit : σₛ.fifos.lookup ⟨c.name, cpath⟩ = (vs ++ ·) <$> σₜ.fifos.lookup ⟨c.name, cpath⟩) :
    σₛ ∼[.some (c, inbox)] σₜ :=
  ⟨hl, hm, cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩

/-! ## Projections

  One per conjunct, in definition order. `label_eq` is the only one that holds in both cases, which
  is why it sits outside the `match` in the definition: a block-level lemma needs it without knowing
  whether the process receives at all.
-/

/-- Source and target agree on which label the block ended at — in both cases of `mbox`. -/
theorem relatesTo.label_eq {mbox : Mailbox} {σₛ σₜ : LocalState' V} (h : σₛ ∼[mbox] σₜ) :
    σₛ.label = σₜ.label := h.1

/-- With no mailbox, the memories are equal. -/
theorem relatesTo.mem_eq {σₛ σₜ : LocalState' V} (h : σₛ ∼[.none] σₜ) : σₛ.mem = σₜ.mem := h.2.1

/-- With no mailbox, the FIFOs are equal. -/
theorem relatesTo.fifos_eq {σₛ σₜ : LocalState' V} (h : σₛ ∼[.none] σₜ) :
    σₛ.fifos = σₜ.fifos := h.2.2

section Chan

variable {σₛ σₜ : LocalState' V} {c : ComputableGuardedPlusCal.Ref} {inbox : String}

/-- The memories agree on every name but `inbox` — the pass introduces exactly one variable, and
`freshName` is what makes "every name but that one" a statement about the source program's names at
all. -/
theorem relatesTo.mem_agree (h : σₛ ∼[.some (c, inbox)] σₜ) :
    ∀ x ≠ inbox, σₛ.mem.lookup x = σₜ.mem.lookup x := h.2.1

/-- The target's `inbox` holds a sequence value, and `vs` is what it holds. Everything below is
stated against the same `cpath`/`vs` this produces, so a proof destructures this once and reuses
the witnesses. -/
theorem relatesTo.inbox_seq (h : σₛ ∼[.some (c, inbox)] σₜ) :
    ∃ cpath sv vs,
      List.Forall₂ (EvalStep σₛ.mem) c.args cpath ∧
      σₜ.mem.lookup inbox = .some sv ∧ ExprSemantics.isSeq sv vs ∧
      (∀ k ≠ (⟨c.name, cpath⟩ : ChanKey V), σₛ.fifos.lookup k = σₜ.fifos.lookup k) ∧
      σₛ.fifos.lookup ⟨c.name, cpath⟩ = (vs ++ ·) <$> σₜ.fifos.lookup ⟨c.name, cpath⟩ := h.2.2

/-- Every FIFO other than the received-from one is untouched. Needs only the resolved path, not
what `inbox` holds — `EvalStep.path_inj` is what makes "the received-from one" well defined. -/
theorem relatesTo.fifo_agree_off (h : σₛ ∼[.some (c, inbox)] σₜ)
    {cpath : List (ComputableTLAPlus.PathStep V)}
    (hpath : List.Forall₂ (EvalStep σₛ.mem) c.args cpath) :
    ∀ k ≠ (⟨c.name, cpath⟩ : ChanKey V), σₛ.fifos.lookup k = σₜ.fifos.lookup k := by
  obtain ⟨cpath', -, -, hpath', -, -, hoff', -⟩ := h.inbox_seq
  obtain rfl := EvalStep.path_inj hpath' hpath
  exact hoff'

/-- The equation the whole proof turns on: the source's channel is the target's `inbox` followed by
the target's channel. Reception has no trace event, so this is the only statement that a message
the target moved out of the channel is still accounted for. -/
theorem relatesTo.fifo_split (h : σₛ ∼[.some (c, inbox)] σₜ)
    {cpath : List (ComputableTLAPlus.PathStep V)} {sv : V} {vs : List V}
    (hpath : List.Forall₂ (EvalStep σₛ.mem) c.args cpath)
    (hinbox : σₜ.mem.lookup inbox = .some sv) (hseq : ExprSemantics.isSeq sv vs) :
    σₛ.fifos.lookup ⟨c.name, cpath⟩ = (vs ++ ·) <$> σₜ.fifos.lookup ⟨c.name, cpath⟩ := by
  obtain ⟨cpath', sv', vs', hpath', hinbox', hseq', -, hsplit'⟩ := h.inbox_seq
  obtain rfl := EvalStep.path_inj hpath' hpath
  rw [hinbox] at hinbox'
  obtain rfl := Option.some.inj hinbox'
  obtain rfl := ExprSemantics.isSeq_inj hseq' hseq
  exact hsplit'

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

/-- The algorithm-level lift of `relatesTo`: same instances, each instance's state related, and one
FIFO map split per key. -/
def algRelatesTo {ι : Type} (mb : ι → Mailbox) (rx : ι → Set String) :
    Rel (AlgState ι V) (AlgState ι V) :=
  λ ⟨Ps, F₁⟩ ⟨Qs, F₂⟩ ↦
    ∃ ib : ι → Option (InboxState V),
      -- the same instances on both sides, pairwise related
      (∀ p σ, ⟨p, σ⟩ ∈ Ps → ∃ σ', ⟨p, σ'⟩ ∈ Qs ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ') ∧
      (∀ p σ', ⟨p, σ'⟩ ∈ Qs → ∃ σ, ⟨p, σ⟩ ∈ Ps ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ') ∧
      -- an index that names no instance of this state accounts for nothing: without this the
      -- witness could invent an inbox for an absent instance and the FIFO clauses below would
      -- demand a split no state satisfies
      (∀ p, (∀ σ, ⟨p, σ⟩ ∉ Ps) → ib p = .none) ∧
      -- no two instances receive on the same key
      (∀ p q x y, ib p = .some x → ib q = .some y → x.key = y.key → p = q) ∧
      -- a key nobody receives on is untouched
      (∀ k : ChanKey V, (∀ p x, ib p = .some x → x.key ≠ k) → F₁.lookup k = F₂.lookup k) ∧
      -- and a key someone receives on has that instance's inbox in front of it
      (∀ p x, ib p = .some x → F₁.lookup x.key = (x.contents ++ ·) <$> F₂.lookup x.key)

@[inherit_doc algRelatesTo]
scoped notation:60 Sₛ:60 " ≋[" mb:0 ", " rx:0 "] " Sₜ:60 => Guarded2Network.algRelatesTo mb rx Sₛ Sₜ

namespace algRelatesTo

variable {ι : Type} {mb : ι → Mailbox} {rx : ι → Set String} {Sₛ Sₜ : AlgState ι V}

/-- Every source instance has a related target instance. -/
theorem forward (h : Sₛ ≋[mb, rx] Sₜ) :
    ∃ ib : ι → Option (InboxState V), ∀ p σ, ⟨p, σ⟩ ∈ Sₛ.1 →
      ∃ σ', ⟨p, σ'⟩ ∈ Sₜ.1 ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ' := by
  obtain ⟨ib, hfwd, -, -, -, -, -⟩ := h
  exact ⟨ib, hfwd⟩

/-- Every target instance has a related source instance — the direction that rules out the target
inventing an instance the source never had. -/
theorem backward (h : Sₛ ≋[mb, rx] Sₜ) :
    ∃ ib : ι → Option (InboxState V), ∀ p σ', ⟨p, σ'⟩ ∈ Sₜ.1 →
      ∃ σ, ⟨p, σ⟩ ∈ Sₛ.1 ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ' := by
  obtain ⟨ib, -, hbwd, -, -, -, -⟩ := h
  exact ⟨ib, hbwd⟩

/-- The whole FIFO map, in one statement: every key is the target's queue with the inbox of the one
instance receiving on it (if any) in front. The `ib` witness is shared with `forward`/`backward`,
which is what makes this composable with them rather than a separate fact. -/
theorem fifos (h : Sₛ ≋[mb, rx] Sₜ) :
    ∃ ib : ι → Option (InboxState V),
      (∀ p q x y, ib p = .some x → ib q = .some y → x.key = y.key → p = q) ∧
      (∀ k : ChanKey V, (∀ p x, ib p = .some x → x.key ≠ k) → Sₛ.2.lookup k = Sₜ.2.lookup k) ∧
      (∀ p x, ib p = .some x → Sₛ.2.lookup x.key = (x.contents ++ ·) <$> Sₜ.2.lookup x.key) := by
  obtain ⟨ib, -, -, -, hinj, hoff, hsplit⟩ := h
  exact ⟨ib, hinj, hoff, hsplit⟩

/-- The introduction form: one hypothesis per clause, against a single choice of witnesses. -/
theorem intro {ib : ι → Option (InboxState V)}
    (hfwd : ∀ p σ, ⟨p, σ⟩ ∈ Sₛ.1 → ∃ σ', ⟨p, σ'⟩ ∈ Sₜ.1 ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ')
    (hbwd : ∀ p σ', ⟨p, σ'⟩ ∈ Sₜ.1 → ∃ σ, ⟨p, σ⟩ ∈ Sₛ.1 ∧ procRelatesTo (mb p) (rx p) (ib p) σ σ')
    (habsent : ∀ p, (∀ σ, ⟨p, σ⟩ ∉ Sₛ.1) → ib p = .none)
    (hinj : ∀ p q x y, ib p = .some x → ib q = .some y → x.key = y.key → p = q)
    (hoff : ∀ k : ChanKey V, (∀ p x, ib p = .some x → x.key ≠ k) → Sₛ.2.lookup k = Sₜ.2.lookup k)
    (hsplit : ∀ p x, ib p = .some x → Sₛ.2.lookup x.key = (x.contents ++ ·) <$> Sₜ.2.lookup x.key) :
    Sₛ ≋[mb, rx] Sₜ :=
  ⟨ib, hfwd, hbwd, habsent, hinj, hoff, hsplit⟩

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
