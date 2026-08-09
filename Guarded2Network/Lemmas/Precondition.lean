module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Reorder

@[expose] public section

/-!
  What `processPrecondition` does to a branch's guard block.

  The pass compiles a `receive` into an `await` on the inbox's length plus two *consumption
  assignments*, and it does not emit those assignments where the `receive` was: they are prepended
  to the branch's action block (`stepBranch`), so they run after every remaining guard. Each such
  guard is rewritten on the way past — that is `substGuards`, and
  `Guarded2Network/Lemmas/Reorder.lean` says the two moves cancel.

  This file is the other half: what one `receive` becomes, in the *adjacent* ordering where its two
  assignments sit immediately after its `await`. The reorder lemma turns the adjacent ordering into
  the emitted one, so the walk over the block never has to reason about both at once.

  **Index versus substitution.** In the emitted ordering the k-th `receive`'s guard is
  `Len(inbox) > k`, because no assignment has run yet and the inbox still holds every pending
  message. In the adjacent ordering the k preceding pairs have already run, the inbox has been
  tailed k times, and the guard is `Len(inbox) > 0`. The two say the same thing, and saying so is
  what `lenGt_substGuards` below is for.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Expression Memory PathStep)
open GuardedPlusCal (ChanKey EvalStep FIFOs LocalState LocalState' Trace)

variable {V : Type} [ExprSemantics V] [SeqBuiltins V]

/-! ## The pass's own `inbox` syntax, named

  `stepStatement` builds these as `let`s inside its `receive` case. Naming them here is what lets a
  lemma be stated against the pass rather than against a transcription of it — the same reason
  `Lemmas/Reorder.lean` names `consumptions`.
-/

/-- The variable node every sequence expression the pass emits is built over. -/
def inboxVar (inbox : String) (τ : ComputableTLAPlus.Typ) : ComputablePlusCal.Expression :=
  .var inbox (.seq τ) .binder

/-- The reference the tailed sequence is assigned back through. No index path: `inbox` is a plain
process-local variable. -/
def inboxRef (inbox : String) (τ : ComputableTLAPlus.Typ) : ComputableGuardedPlusCal.Ref :=
  { name := inbox, args := [], baseType := .seq τ }

@[inherit_doc inboxRef]
theorem inboxRef_name {inbox : String} {τ : ComputableTLAPlus.Typ} :
    (inboxRef inbox τ).name = inbox :=
  rfl

/-- The two entries one `receive` appends to `newInstrs`: bind the coerced head, then drop it. -/
def receiveInstrs (r : ComputableGuardedPlusCal.Ref) (coe : TypedTLAPlus.Coercion) (inbox : String)
    (τ : ComputableTLAPlus.Typ) (pos : SourceSpan) :
    List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan) :=
  [(r, coe.applyComputable (head τ (inboxVar inbox τ)), pos), (inboxRef inbox τ, tail τ (inboxVar inbox τ), pos)]

/-- What a `receive` needs of the names around it, in the same shape `Lemmas/Statement.lean`'s
`Fresh` uses. Three conditions, each earned by construction in a real compilation: the pass's
`inbox` is generated with a `$` separator so no source reference can mention it, and
`WellFormedness/Restrictions.lean` keeps a channel's index path clear of what the branch writes. -/
def ReceiveFresh (c r : ComputableGuardedPlusCal.Ref) (inbox : String) : Prop :=
  inbox ∉ GuardedPlusCal.Ref.freeVars c ∧ inbox ∉ GuardedPlusCal.Ref.freeVars r ∧
    r.name ∉ GuardedPlusCal.Ref.freeVars c

/-! ## The two compiled pieces, characterized once

  Both the `receive` lemmas below and the guard reorder further down take these apart, in both
  directions. Stating each once as an `↔` is what keeps either from re-deriving the other's shape.
-/

/-- The compiled guard's step: it changes nothing, emits nothing, and is enabled exactly when the
inbox holds more than `n` elements. -/
theorem await_lenGt_iff {inbox : String} {τ : ComputableTLAPlus.Typ} {n : Nat} {M : Memory V}
    {F : FIFOs V} {sv : V} {vs : List V} {σ' : LocalState' V} {ε : Trace V}
    (hlk : M.lookup inbox = .some sv) (hseq : ExprSemantics.isSeq sv vs) :
    (⟨(M, F, .none), ε, σ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
        NetworkPlusCal.Statement.reducing' (.await (lenGt τ (inboxVar inbox τ) n)) ↔
      σ' = (M, F, .none) ∧ ε = 1 ∧ n < vs.length := by
  obtain ⟨b, hb, -, hiff⟩ := eval_lenGt_inbox (τ := τ) (n := n) hlk hseq
  iff_rintro h ⟨rfl, rfl, hlen⟩
  · obtain ⟨M₀, F₀, l₀⟩ := σ'
    obtain ⟨_, -, ⟨M', F', hM, hσ', htru, rfl⟩, hpost, rfl⟩ := h
    injection hM with hM hF
    subst hM; subst hF; subst hσ'
    injection hpost with hM' hF'
    subst hM'; subst hF'
    obtain rfl := ExprSemantics.evalUnique hb htru
    exact ⟨rfl, rfl, hiff.mp rfl⟩
  · obtain rfl := hiff.mpr hlen
    exact ⟨.running M F, rfl,
      NetworkPlusCal.Statement.reducing.await.intro ⟨M, F, rfl, rfl, hb, rfl⟩, rfl, rfl⟩

/-- One `receive`'s two consumption assignments, as a single step: the inbox must hold at least one
element, the coerced head lands under the reference, and the tail is written back. Note what the pair
does *not* need — nothing about `r`'s index path relative to `inbox`, since both orderings evaluate
the assignments at exactly the same two memories. Only `r.name ≠ inbox` matters, and only so that the
first assignment leaves the inbox for the second to read. -/
theorem consumption_pair_iff {r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ : ComputableTLAPlus.Typ} (hne : r.name ≠ inbox)
    {σ σ' : LocalState' V} {ε : Trace V} :
    (⟨σ, ε, σ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
        NetworkPlusCal.Statement.reducing'
            (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
          NetworkPlusCal.Statement.reducing'
            (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))) ↔
      ∃ M F M' sv t v v' vs rpath,
        σ = (M, F, .none) ∧ σ' = (M'.insert inbox t, F, .none) ∧ ε = 1 ∧
        M.lookup inbox = .some sv ∧ ExprSemantics.isSeq sv (v :: vs) ∧
        ExprSemantics.isSeq t vs ∧ ExprSemantics.coerce coe v v' ∧ Ref.EvalArgs M r rpath ∧
        ComputableTLAPlus.Memory.update M r.name rpath v' = .some M' := by
  iff_rintro ⟨⟨Mₘ, Fₘ, lₘ⟩, ε₁, ε₂, hR, hI, rfl⟩
    ⟨M, F, M', sv, t, v, v', vs, rpath, rfl, rfl, rfl, hsv, hseq, ht, hcoe, hrpath, hupd⟩
  · obtain ⟨M₁, F₁, l₁⟩ := σ
    obtain ⟨M₂, F₂, l₂⟩ := σ'
    obtain ⟨_, rfl, ⟨M, F, M', v', rpath, hv', hrpath, hupd, hM, hσ', rfl⟩, hpost, rfl⟩ := hR
    injection hM with hM hF
    subst hM; subst hF; subst hσ'
    injection hpost with hM' hF'
    subst hM'; subst hF'
    obtain ⟨_, -, ⟨M, F, M₄, t, ipath, htail, hipath, hupdI, hM, hσ', rfl⟩, hpost, rfl⟩ := hI
    injection hM with hM hF
    subst hM; subst hF; subst hσ'
    injection hpost with hM' hF'
    subst hM'; subst hF'
    cases hipath
    rw [inboxRef_name] at hupdI
    obtain rfl := ComputableTLAPlus.Memory.update_nil hupdI
    -- the head's own evaluation is what says the inbox holds a sequence at all
    obtain ⟨v, hv, hcoe⟩ := ExprSemantics.evalCoerce.mp hv'
    obtain ⟨sv, vs, hsvEval, hseq⟩ := SeqBuiltins.evalHead.mp hv
    have hsv : M₁.lookup inbox = .some sv := ExprSemantics.evalVar.mp hsvEval
    have hsv' : M'.lookup inbox = .some sv :=
      (Memory.lookup_update_ne hupd (Ne.symm hne)).trans hsv
    exact ⟨M₁, F₁, M', sv, t, v, v', vs, rpath, rfl, rfl, by simp, hsv, hseq,
      (eval_tail_inbox hsv' hseq).mp htail, hcoe, hrpath, hupd⟩
  · have hsv' : M'.lookup inbox = .some sv :=
      (Memory.lookup_update_ne hupd (Ne.symm hne)).trans hsv
    refine ⟨(M', F, .none), 1, 1, ⟨.running M' F, rfl,
      NetworkPlusCal.Statement.reducing.assign.intro
        ⟨M, F, M', v', rpath, ExprSemantics.evalCoerce.mpr
          ⟨v, (eval_head_inbox hsv hseq).mpr rfl, hcoe⟩, hrpath, hupd, rfl, rfl, rfl⟩,
      rfl, rfl⟩, ⟨.running (M'.insert inbox t) F, rfl,
      NetworkPlusCal.Statement.reducing.assign.intro
        ⟨M', F, M'.insert inbox t, t, [], (eval_tail_inbox hsv' hseq).mpr ht, .nil, ?_,
          rfl, rfl, rfl⟩,
      rfl, rfl⟩, by simp⟩
    rw [inboxRef_name]
    exact ComputableTLAPlus.Memory.update_eq_some_iff.mpr
      ⟨sv, t, hsv', ExprSemantics.updatePath_nil, rfl⟩

/-! ## One `receive`, in the adjacent ordering -/

/-- The terminating half. A target run of `await Len(inbox) > 0` followed by the two consumption
assignments is matched by the source's `receive`, or — when the invariant permits an `inbox` holding
messages over a channel the source has no FIFO for at all — by the source aborting.

Every hypothesis of the source's `receive` comes from somewhere specific: the channel's resolved
path and the head value from `relatesTo`'s split `F₁[c] = inbox ++ F₂[c]`, the coercion from
`evalCoerce` run backwards on the assignment's right-hand side, and the reference's own path and
update transferred across the `inbox`-difference by `Ref.EvalArgs.congr_of_fresh` and
`Memory.update_transfer`. -/
theorem receive_reducing_sim {c r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ : ComputableTLAPlus.Typ}
    (fresh : ReceiveFresh c r inbox) {σₛ σₜ σₜ' : LocalState' V} {ε : Trace V}
    (sim : σₛ ∼[.some (c, inbox)] σₜ)
    (step : (⟨σₜ, ε, σₜ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
      NetworkPlusCal.Statement.reducing' (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₂
      NetworkPlusCal.Statement.reducing'
        (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
      NetworkPlusCal.Statement.reducing' (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ)))) :
    ε = 1 ∧
      ((∃ σₛ', σₛ' ∼[.some (c, inbox)] σₜ' ∧
        (⟨σₛ, 1, σₛ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
          GuardedPlusCal.Statement.reducing' (.receive c r coe)) ∨
      (⟨σₛ, 1⟩ : LocalState' V × Trace V) ∈
        GuardedPlusCal.Statement.aborting' (.receive c r coe)) := by
  obtain ⟨hfc, hfr, hfw⟩ := fresh
  have hrname : r.name ≠ inbox := Ne.symm (ne_name_of_fresh hfr)
  obtain ⟨cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩ := sim.inbox_seq
  have hagree := sim.mem_agree
  have hlabel := sim.label_eq
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  obtain ⟨M₂, F₂, l₂⟩ := σₜ
  obtain ⟨M₄, F₄, l₄⟩ := σₜ'
  simp only [LocalState'.mem_mk, LocalState'.fifos_mk, LocalState'.label_mk]
    at hpath hinbox hoff hsplit hagree hlabel
  -- the target's three steps
  obtain ⟨⟨Mₘ, Fₘ, lₘ⟩, ε₁, ε₂, hawait, ⟨⟨Mₙ, Fₙ, lₙ⟩, ε₃, ε₄, hassignR, hassignI, rfl⟩, rfl⟩ := step
  obtain ⟨_, rfl, ⟨M, F, hM, hσ', htru, rfl⟩, hpost, rfl⟩ := hawait
  injection hM with hM hF
  subst hM; subst hF; subst hσ'
  injection hpost with hM' hF'
  subst hM'; subst hF'
  obtain ⟨_, -, ⟨M, F, M₃, v', rpath, hv', hrpath, hupd, hM, hσ', rfl⟩, hpost, rfl⟩ := hassignR
  injection hM with hM hF
  subst hM; subst hF; subst hσ'
  injection hpost with hM' hF'
  subst hM'; subst hF'
  obtain ⟨_, -, ⟨M, F, M₄', t, ipath, ht, hipath, hupdI, hM, hσ', rfl⟩, hpost, rfl⟩ := hassignI
  injection hM with hM hF
  subst hM; subst hF; subst hσ'
  injection hpost with hM' hF'
  subst hM'; subst hF'
  refine ⟨by simp, ?_⟩
  -- the guard says the inbox is non-empty, so the drained prefix has a head
  obtain ⟨b, hb, -, hiff⟩ := eval_lenGt_inbox (τ := τ) (n := 0) hinbox hseq
  obtain rfl := ExprSemantics.evalUnique hb htru
  obtain ⟨v, vs', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (hiff.mp rfl))
  -- that head is what the source's `receive` dequeues, coerced
  obtain ⟨w, hw, hcoe⟩ := ExprSemantics.evalCoerce.mp hv'
  obtain rfl := ((eval_head_inbox hinbox hseq).mp hw).symm
  -- the second assignment only rebinds `inbox`, which the first one left alone
  have hinbox₃ : M₃.lookup inbox = some sv :=
    (Memory.lookup_update_ne hupd (Ne.symm hrname)).trans hinbox
  have ht' : ExprSemantics.isSeq t vs' := (eval_tail_inbox hinbox₃ hseq).mp ht
  -- `inbox` is a plain variable, so its reference has no index path to resolve
  cases hipath
  rw [inboxRef_name] at hupdI
  obtain rfl := ComputableTLAPlus.Memory.update_nil hupdI
  cases hlk : F₂.lookup ((c.name, cpath) : ChanKey V) with
  | none =>
    -- the invariant permits an `inbox` holding messages over a channel the source has no FIFO for
    -- at all; there the source aborts rather than matching
    refine .inr ⟨hlabel, GuardedPlusCal.Statement.aborting.receive.intro
      (.inl (.inl (.inr ⟨M₁, F₁, cpath, rfl, rfl, hpath, ?_⟩)))⟩
    rw [hsplit, hlk]
    rfl
  | some ws =>
    have hlk₁ : F₁.lookup ((c.name, cpath) : ChanKey V) = .some (v :: (vs' ++ ws)) := by
      rw [hsplit, hlk]
      rfl
    obtain ⟨M₁', hupd₁, hagree₁⟩ :=
      Memory.update_transfer (λ y hy ↦ (hagree y hy).symm) hrname hupd
    refine .inl ⟨⟨M₁', F₁.insert (c.name, cpath) (vs' ++ ws), .none⟩,
      relatesTo.chan_intro (cpath := cpath) rfl ?_ ?_ (Finmap.lookup_insert _) ht' ?_ ?_,
      ⟨.running M₁' (F₁.insert (c.name, cpath) (vs' ++ ws)), hlabel,
        GuardedPlusCal.Statement.reducing.receive.intro
          ⟨M₁, F₁, M₁', cpath, rpath, v, v', vs' ++ ws, hpath,
            (Ref.EvalArgs.congr_of_fresh hagree hfr).mpr hrpath, hlk₁, hcoe, hupd₁,
            rfl, rfl, rfl⟩,
        rfl, rfl⟩⟩
    · intro y hy
      simp only [LocalState'.mem_mk]
      rw [Finmap.lookup_insert_of_ne _ hy]
      exact (hagree₁ y hy).symm
    · exact (Ref.EvalArgs.congr_of_fresh
        (λ y hy ↦ (Memory.lookup_update_ne hupd₁ hy).symm) hfw).mp hpath
    · intro k hk
      simp only [LocalState'.fifos_mk]
      rw [Finmap.lookup_insert_of_ne _ hk]
      exact hoff k hk
    · simp only [LocalState'.fifos_mk]
      rw [Finmap.lookup_insert _, hlk]
      rfl

/-- The aborting half. Every way the compiled group can go wrong is a way the source's `receive`
can, and the source's abort emits nothing — so no trace obligation survives.

Most of the target's abort clauses are unreachable rather than matched, and it is worth saying which
and why. The `await` cannot abort at all: `eval_lenGt_inbox` gives its guard *both* a value and
boolean-ness, which is exactly the pair `Statement.aborting`'s `await` case rules out. Neither can
the second assignment: `inbox` is bound (the first assignment writes some other name), `Tail` has a
value (`isSeq_tail`), the reference has no index path to resolve, and an empty-path update cannot
fail. What is left is the first assignment's four clauses, which map onto four of the `receive`'s
six. -/
theorem receive_aborting_sim {c r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ : ComputableTLAPlus.Typ}
    (fresh : ReceiveFresh c r inbox) {σₛ σₜ : LocalState' V} {ε : Trace V}
    (sim : σₛ ∼[.some (c, inbox)] σₜ)
    (step : (⟨σₜ, ε⟩ : LocalState' V × Trace V) ∈
      NetworkPlusCal.Statement.aborting' (.await (lenGt τ (inboxVar inbox τ) 0)) ∪
      NetworkPlusCal.Statement.reducing' (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₁
        (NetworkPlusCal.Statement.aborting'
            (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∪
          NetworkPlusCal.Statement.reducing'
              (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₁
            NetworkPlusCal.Statement.aborting'
              (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))))) :
    (⟨σₛ, 1⟩ : LocalState' V × Trace V) ∈
      GuardedPlusCal.Statement.aborting' (.receive c r coe) := by
  obtain ⟨hfc, hfr, hfw⟩ := fresh
  have hrname : r.name ≠ inbox := Ne.symm (ne_name_of_fresh hfr)
  obtain ⟨cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩ := sim.inbox_seq
  have hagree := sim.mem_agree
  have hlabel := sim.label_eq
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  obtain ⟨M₂, F₂, l₂⟩ := σₜ
  simp only [LocalState'.mem_mk, LocalState'.fifos_mk, LocalState'.label_mk]
    at hpath hinbox hoff hsplit hagree hlabel
  obtain ⟨b, hb, hbool, hiff⟩ := eval_lenGt_inbox (τ := τ) (n := 0) hinbox hseq
  rcases step with ⟨-, hab⟩ | ⟨⟨Mₘ, Fₘ, lₘ⟩, ε₁, ε₂, hred, hrest, -⟩
  · -- the guard has a value and is a boolean, so neither `await` abort clause is reachable
    rcases hab with ⟨M, F, habort, hM, -⟩ | ⟨M, F, w, hw, hwv, hM, -⟩
    · injection hM with hM _
      subst hM
      have hex : ∃ u, M₂ ⊢ lenGt τ (inboxVar inbox τ) 0 ⇒ u := ⟨b, hb⟩
      absurd hex
      exact habort
    · injection hM with hM _
      subst hM
      obtain rfl := ExprSemantics.evalUnique hb hwv
      absurd hbool
      exact hw
  · -- the guard held, so the drained prefix has a head
    obtain ⟨_, rfl, ⟨M, F, hM, hσ', htru, -⟩, hpost, -⟩ := hred
    injection hM with hM hF
    subst hM; subst hF; subst hσ'
    injection hpost with hM' hF'
    subst hM'; subst hF'
    obtain rfl := ExprSemantics.evalUnique hb htru
    obtain ⟨v, vs', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (hiff.mp rfl))
    -- the source's queue may be absent altogether, and then the source aborts on the channel itself
    have habsent : F₂.lookup ((c.name, cpath) : ChanKey V) = .none →
        (⟨(M₁, F₁, l₁), (1 : Trace V)⟩ : LocalState' V × Trace V) ∈
          GuardedPlusCal.Statement.aborting' (.receive c r coe) := by
      intro hlk
      refine ⟨hlabel, GuardedPlusCal.Statement.aborting.receive.intro
        (.inl (.inl (.inr ⟨M₁, F₁, cpath, rfl, rfl, hpath, ?_⟩)))⟩
      rw [hsplit, hlk]
      rfl
    rcases hrest with hab | ⟨⟨Mₙ, Fₙ, lₙ⟩, ε₃, ε₄, hredR, habI, -⟩
    · obtain ⟨-, hab⟩ := hab
      obtain ⟨M, F, hM, -, hd⟩ := NetworkPlusCal.Statement.aborting.assign.iff.mp hab
      injection hM with hM hF
      subst hM; subst hF
      rcases hd with hname | habort | hrp | ⟨v', rpath, hv', hrpath, hupd⟩
      · -- the assignment's target is unbound in the target, so it is in the source too
        refine ⟨hlabel, GuardedPlusCal.Statement.aborting.receive.intro
          (.inl (.inl (.inl (.inl (.inl ⟨M₁, F₁, ?_, rfl, rfl⟩)))))⟩
        rw [← Finmap.lookup_eq_none, hagree r.name hrname, Finmap.lookup_eq_none]
        exact hname
      · -- `Head` has a value, so what fails is the coercion
        cases hlk : F₂.lookup ((c.name, cpath) : ChanKey V) with
        | none => exact habsent hlk
        | some ws =>
          refine ⟨hlabel, GuardedPlusCal.Statement.aborting.receive.intro
            (.inl (.inr ⟨M₁, F₁, cpath, v, vs' ++ ws, rfl, rfl, hpath, ?_, ?_⟩))⟩
          · rw [hsplit, hlk]
            rfl
          · rintro ⟨v', hv'⟩
            exact habort ⟨v', ExprSemantics.evalCoerce.mpr
              ⟨v, (eval_head_inbox hinbox hseq).mpr rfl, hv'⟩⟩
      · -- the assignment's reference does not resolve, and it reads no name the two memories differ on
        exact ⟨hlabel, GuardedPlusCal.Statement.aborting.receive.intro
          (.inl (.inl (.inl (.inr ⟨M₁, F₁, rfl, rfl, (pathAborts_congr hagree hfr).mpr hrp⟩))))⟩
      · -- the update itself fails, at a value the source computes the same way
        obtain ⟨w, hw, hcoe⟩ := ExprSemantics.evalCoerce.mp hv'
        obtain rfl := ((eval_head_inbox hinbox hseq).mp hw).symm
        cases hlk : F₂.lookup ((c.name, cpath) : ChanKey V) with
        | none => exact habsent hlk
        | some ws =>
          refine ⟨hlabel, GuardedPlusCal.Statement.aborting.receive.intro
            (.inr ⟨M₁, F₁, cpath, rpath, v, v', vs' ++ ws, rfl, rfl, hpath,
              (Ref.EvalArgs.congr_of_fresh hagree hfr).mpr hrpath, ?_, hcoe, ?_⟩)⟩
          · rw [hsplit, hlk]
            rfl
          · exact Memory.update_none_transfer (hagree r.name hrname) hupd
    · -- the second assignment cannot abort: `inbox` is bound, `Tail` has a value, and an empty-path
      -- update cannot fail
      obtain ⟨_, -, ⟨M, F, M₃, v', rpath, -, -, hupd, hM, hσ', -⟩, hpost, -⟩ := hredR
      injection hM with hM hF
      subst hM; subst hF; subst hσ'
      injection hpost with hM' hF'
      subst hM'; subst hF'
      have hinbox₃ : M₃.lookup inbox = .some sv :=
        (Memory.lookup_update_ne hupd (Ne.symm hrname)).trans hinbox
      obtain ⟨-, habI⟩ := habI
      obtain ⟨M, F, hM, -, hd⟩ := NetworkPlusCal.Statement.aborting.assign.iff.mp habI
      injection hM with hM hF
      subst hM; subst hF
      obtain ⟨t, ht'⟩ := ExprSemantics.isSeq_tail hseq
      rcases hd with hname | habort | hrp | ⟨u, ipath, -, hipath, hupdI⟩
      · rw [inboxRef_name, ← Finmap.lookup_eq_none, hinbox₃] at hname
        contradiction
      · have hex : ∃ u, M₃ ⊢ tail τ (inboxVar inbox τ) ⇒ u :=
          ⟨t, (eval_tail_inbox hinbox₃ hseq).mpr ht'⟩
        absurd hex
        exact habort
      · obtain ⟨_, hmem, -⟩ := GuardedPlusCal.Ref.pathAborts_iff.mp hrp
        absurd hmem
        exact List.not_mem_nil
      · cases hipath
        rw [inboxRef_name, ComputableTLAPlus.Memory.update_eq_none_iff] at hupdI
        have := hupdI sv hinbox₃
        rw [ExprSemantics.updatePath_nil] at this
        contradiction

/-- **The `receive` elimination**, in the framework's own terms: one source `receive` refines the
group it compiles to — the inbox-length guard, then the two consumption assignments — at this pass's
trace relation. Still the adjacent ordering; `reorder_assigns_guard` is what moves the assignments to
where the pass actually emits them.

`terminating` is `receive_reducing_sim`, `aborting` is `receive_aborting_sim` with the `≼[Rτ]`
obligation trivial (an abort emits nothing, and the empty trace is a prefix of everything), and
`diverging` is vacuous: no statement diverges, so the target composite is empty and the framework
supplies that component itself. -/
theorem receive_refines {c r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ : ComputableTLAPlus.Typ} (fresh : ReceiveFresh c r inbox) :
    StrongRefinement (relatesTo (V := V) (.some (c, inbox))) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.reducing' (.receive c r coe))
      (GuardedPlusCal.Statement.aborting' (.receive c r coe))
      (GuardedPlusCal.Statement.diverging' (.receive c r coe))
      (NetworkPlusCal.Statement.reducing' (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing'
          (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing' (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))))
      (NetworkPlusCal.Statement.aborting' (.await (lenGt τ (inboxVar inbox τ) 0)) ∪
        NetworkPlusCal.Statement.reducing' (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₁
          (NetworkPlusCal.Statement.aborting'
              (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∪
            NetworkPlusCal.Statement.reducing'
                (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₁
              NetworkPlusCal.Statement.aborting'
                (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ)))))
      ∅ := by
  refine StrongRefinement.ofNonDiverging _ ?_ ?_
  · intro σₜ σₜ' ε σₛ sim step
    obtain ⟨rfl, hmatch | habort⟩ := receive_reducing_sim fresh sim step
    · obtain ⟨σₛ', hrel, hstep⟩ := hmatch
      refines_match σₛ', 1
      · exact hrel
      · trace_rel
      · exact hstep
    · refines_abort 1
      · trace_pfx
      · exact habort
  · intro σₜ ε σₛ sim step
    refines_abort 1
    · exact one_scPrefix ε
    · exact receive_aborting_sim fresh sim step

/-! ## The compiled guards' own reorder

  `Lemmas/Reorder.lean` moves an assignment past a guard by *substituting* into it. That covers every
  guard the source wrote, but not the ones the pass invented: `stepStatement` emits the k-th
  `receive`'s guard as `Len(inbox) > k` rather than as a substituted `Len(Tail…(inbox)) > 0`, so no
  substitution relates the two orderings there. The equation below is that relation, proved
  semantically instead — a consumption pair commutes past a compiled guard by bumping its index.
-/

/-- Moving one consumption pair past a compiled guard costs the guard one on its index: before the
pair the inbox is one element longer, so `Len(inbox) > n` afterwards is `Len(inbox) > n + 1` before.

An equation, with only `r.name ≠ inbox` assumed. Both sides evaluate the two assignments at exactly
the same pair of memories — only the guard moves — and either side can run at all only if the pair
can, which is what forces the inbox to hold a sequence and makes the `Len` law apply. -/
theorem reorder_consumption_lenGt {r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ : ComputableTLAPlus.Typ} {n : Nat} (hne : r.name ≠ inbox) :
    (NetworkPlusCal.Statement.reducing' (V := V)
          (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing'
          (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ)))) ∘ᵣ₂
      NetworkPlusCal.Statement.reducing' (.await (lenGt τ (inboxVar inbox τ) n)) =
    NetworkPlusCal.Statement.reducing' (V := V) (.await (lenGt τ (inboxVar inbox τ) (n + 1))) ∘ᵣ₂
      (NetworkPlusCal.Statement.reducing'
          (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing'
          (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ)))) := by
  ext ⟨σ, ε, σ'⟩
  iff_rintro ⟨σₘ, ε₁, ε₂, hpair, hguard, rfl⟩ ⟨σₘ, ε₁, ε₂, hguard, hpair, rfl⟩
  · obtain ⟨M, F, M', sv, t, v, v', vs, rpath, rfl, rfl, rfl, hsv, hseq, ht, hcoe, hrpath, hupd⟩ :=
      (consumption_pair_iff hne).mp hpair
    obtain ⟨rfl, rfl, hlen⟩ := (await_lenGt_iff (Finmap.lookup_insert _) ht).mp hguard
    refine ⟨(M, F, .none), 1, 1, (await_lenGt_iff hsv hseq).mpr ⟨rfl, rfl, ?_⟩,
      (consumption_pair_iff hne).mpr
        ⟨M, F, M', sv, t, v, v', vs, rpath, rfl, rfl, rfl, hsv, hseq, ht, hcoe, hrpath, hupd⟩,
      by simp⟩
    rw [List.length_cons]
    omega
  · obtain ⟨M, F, M', sv, t, v, v', vs, rpath, rfl, rfl, rfl, hsv, hseq, ht, hcoe, hrpath, hupd⟩ :=
      (consumption_pair_iff hne).mp hpair
    -- the guard changes nothing, so it starts where the pair does
    obtain ⟨Ma, Fa, la⟩ := σ
    obtain ⟨_, rfl, ⟨Mb, Fb, hMb, hσ'', htru, rfl⟩, hpost, -⟩ := hguard
    injection hMb with hMb hFb
    subst hMb; subst hFb; subst hσ''
    injection hpost with hpM hpF
    subst hpM; subst hpF
    obtain ⟨b, hb, -, hiff⟩ := eval_lenGt_inbox (τ := τ) (n := n + 1) hsv hseq
    obtain rfl := ExprSemantics.evalUnique hb htru
    have hlen := hiff.mp rfl
    refine ⟨(M'.insert inbox t, Fa, .none), 1, 1, hpair,
      (await_lenGt_iff (Finmap.lookup_insert _) ht).mpr ⟨rfl, rfl, ?_⟩, by simp⟩
    rw [List.length_cons] at hlen
    omega

end Guarded2Network

end
