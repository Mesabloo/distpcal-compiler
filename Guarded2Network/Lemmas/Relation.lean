module

public import Guarded2Network.Lemmas.Seq
public import Core.NetworkPlusCal.Semantics.Lemmas

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
open GuardedPlusCal (ChanKey EvalStep FIFOs LocalState')

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

end Guarded2Network

end
