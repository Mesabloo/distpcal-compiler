module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Monad
public import Guarded2Network.Lemmas.Reorder
public import WellFormedness.WellScoped.GuardedPlusCal
import all Guarded2Network.PlusCal
meta import Std.Tactic.Do
import Extra.Do

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
  tailed k times, and the guard is `Len(inbox) > 0`. The two say the same thing, but no
  *substitution* relates them — this pass emits no offset for `substGuards` to grow — so the bridge
  is the semantic `reorder_consumption_lenGt` below instead.

  The last section is the walk itself: `Walk`, the specification of what `processPrecondition`
  leaves behind, and the `mvcgen` proof that the pass meets it.
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
can, which is what forces the inbox to hold a sequence and makes the `Len` law apply.

The pair's element type `τ` and the guard's `τ'` are independent: each compiled guard carries the
element type of *its own* channel, and the pending pairs carry theirs. Nothing in the proof couples
them — the type annotation rides along inside the expressions and never reaches the memory. -/
theorem reorder_consumption_lenGt {r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ τ' : ComputableTLAPlus.Typ} {n : Nat} (hne : r.name ≠ inbox) :
    (NetworkPlusCal.Statement.reducing' (V := V)
          (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing'
          (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ)))) ∘ᵣ₂
      NetworkPlusCal.Statement.reducing' (.await (lenGt τ' (inboxVar inbox τ') n)) =
    NetworkPlusCal.Statement.reducing' (V := V) (.await (lenGt τ' (inboxVar inbox τ') (n + 1))) ∘ᵣ₂
      (NetworkPlusCal.Statement.reducing'
          (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing'
          (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ)))) := by
  ext ⟨σ, ε, σ'⟩
  iff_rintro ⟨σₘ, ε₁, ε₂, hpair, hguard, rfl⟩ ⟨σₘ, ε₁, ε₂, hguard, hpair, rfl⟩
  · obtain ⟨M, F, M', sv, t, v, v', vs, rpath, rfl, rfl, rfl, hsv, hseq, ht, hcoe, hrpath, hupd⟩ :=
      (consumption_pair_iff hne).mp hpair
    obtain ⟨rfl, rfl, hlen⟩ := (await_lenGt_iff (Finmap.lookup_insert _) ht).mp hguard
    refine ⟨_, _, _, (await_lenGt_iff hsv hseq).mpr ⟨rfl, rfl, ?_⟩, hpair, ?_⟩
    · rw [List.length_cons]
      omega
    · rw [mul_one]
  · obtain ⟨M, F, M', sv, t, v, v', vs, rpath, rfl, rfl, rfl, hsv, hseq, ht, hcoe, hrpath, hupd⟩ :=
      (consumption_pair_iff hne).mp hpair
    -- the guard changes nothing, so it starts where the pair does
    obtain ⟨Ma, Fa, la⟩ := σ
    obtain ⟨_, rfl, ⟨Mb, Fb, hMb, hσ'', htru, rfl⟩, hpost, -⟩ := hguard
    injection hMb with hMb hFb
    subst hMb; subst hFb; subst hσ''
    injection hpost with hpM hpF
    subst hpM; subst hpF
    obtain ⟨b, hb, -, hiff⟩ := eval_lenGt_inbox (τ := τ') (n := n + 1) hsv hseq
    obtain rfl := ExprSemantics.evalUnique hb htru
    have hlen := hiff.mp rfl
    refine ⟨_, _, _, hpair, (await_lenGt_iff (Finmap.lookup_insert _) ht).mpr ⟨rfl, rfl, ?_⟩, ?_⟩
    · rw [List.length_cons] at hlen
      omega
    · rw [mul_one]

/-- **A compiled guard can only abort where its own consumption pair already does.** `Len(inbox) > n`
has a value whenever `inbox` holds a sequence (`eval_lenGt_inbox`), so for it to abort the inbox must
not be readable as one — and then `Head(inbox)` has no value either (`SeqBuiltins.evalHead`), which
is one of the four ways `assign` fails.

This is what spares the aborting reorder a second semantic argument: whatever a guard could have done
before the pair ran is already covered by the pair's own first step, so the guard is simply dropped.

The pair's element type `τ` and the guard's `τ'` stay independent here for the reason they do in
`reorder_consumption_lenGt`: `evalVar` ignores the annotation, so both expressions read the same
memory cell. -/
theorem await_lenGt_aborting_le {r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ τ' : ComputableTLAPlus.Typ} {n : Nat} :
    NetworkPlusCal.Statement.aborting' (V := V) (.await (lenGt τ' (inboxVar inbox τ') n)) ≤
      NetworkPlusCal.Statement.aborting' (V := V)
        (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) := by
  rintro ⟨⟨M, F, l⟩, ε⟩ ⟨rfl, hguard⟩
  obtain ⟨M₀, F₀, hM, rfl, hd⟩ := NetworkPlusCal.Statement.aborting.await.iff.mp hguard
  injection hM with hM hF
  subst hM; subst hF
  refine ⟨rfl, NetworkPlusCal.Statement.aborting.assign.iff.mpr
    ⟨_, _, rfl, rfl, .inr (.inl ?_)⟩⟩
  rintro ⟨v', hv'⟩
  obtain ⟨v, hv, -⟩ := ExprSemantics.evalCoerce.mp hv'
  obtain ⟨s, vs, hs, hseq⟩ := SeqBuiltins.evalHead.mp hv
  obtain ⟨b, hb, hbool, -⟩ :=
    eval_lenGt_inbox (τ := τ') (n := n) (ExprSemantics.evalVar.mp hs) hseq
  rcases hd with habort | ⟨w, hw, hnb⟩
  · exact habort ⟨b, hb⟩
  · obtain rfl := ExprSemantics.evalUnique hw hb
    exact hnb hbool

/-- **One consumption pair past a compiled guard, for the runs that fail.**
`reorder_consumption_lenGt`'s aborting twin, and — unlike it — not an equation and not an argument
about indices at all. The guard is a no-op on the runs where it fires, so every failing run of
`guard ; pair` is a failing run of `pair` alone; that the guard's own index drops from `n + 1` to `n`
on the far side is then free, because the far side is never reached. -/
theorem reorder_consumption_lenGt_abort {r : ComputableGuardedPlusCal.Ref}
    {coe : TypedTLAPlus.Coercion} {inbox : String} {τ τ' : ComputableTLAPlus.Typ} {n : Nat} :
    NetworkPlusCal.Statement.aborting' (V := V) (.await (lenGt τ' (inboxVar inbox τ') (n + 1))) ∪
        NetworkPlusCal.Statement.reducing' (.await (lenGt τ' (inboxVar inbox τ') (n + 1))) ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting'
            [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
              .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] ≤
      NetworkPlusCal.Statement.listAborting' (V := V)
          [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
            .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] ∪
        NetworkPlusCal.Statement.listReducing'
            [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
              .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] ∘ᵣ₁
          NetworkPlusCal.Statement.aborting' (.await (lenGt τ' (inboxVar inbox τ') n)) := by
  refine le_trans (Set.union_subset ?_ ?_) Set.subset_union_left
  · rw [NetworkPlusCal.Statement.listAborting'_cons]
    exact le_trans await_lenGt_aborting_le Set.subset_union_left
  · exact Relation.lcomp₁.le_of_left_le_idle NetworkPlusCal.Statement.reducing'_await_le_idle

/-! ## Every pending assignment moved past a compiled guard at once

  `reorder_consumption_lenGt` moves one pair. What the walk actually meets is the whole accumulator:
  `stepStatement` emits the k-th `receive`'s guard as `Len(inbox) > k` in a program where the k
  earlier pairs have not run yet, and the refinement wants it where they have — at `Len(inbox) > 0`,
  the index `receive_refines` proves. Moving k pairs across costs the guard k.

  That needs to know the accumulator *is* k pairs, which no type records, hence the predicate below.
-/

/-- What `ReceiveState.newInstrs` holds after `k` receives: exactly `k` consumption pairs over this
`inbox`, in the order they were appended. Each pair's own channel element type and source span are
its own — only the shared `inbox` and the target reference being distinct from it matter. -/
inductive ConsumptionPairs (inbox : String) :
    Nat → List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan) → Prop
  | nil : ConsumptionPairs inbox 0 []
  | snoc {k A r coe τ pos} (h : ConsumptionPairs inbox k A) (hne : r.name ≠ inbox) :
      ConsumptionPairs inbox (k + 1) (A ++ receiveInstrs r coe inbox τ pos)

@[inherit_doc consumptions]
theorem consumptions_append
    {A B : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)} :
    consumptions (A ++ B) = consumptions A ++ consumptions B :=
  List.map_append

@[inherit_doc receiveInstrs]
theorem consumptions_receiveInstrs {r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ : ComputableTLAPlus.Typ} {pos : SourceSpan} :
    consumptions (receiveInstrs r coe inbox τ pos) =
      [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
        .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] :=
  rfl

/-- **The whole accumulator past one compiled guard.** `k` pending consumption pairs commute past
`Len(inbox) > n`, leaving `Len(inbox) > n + k` in front of them — each pair drops one element from
the inbox, so a guard that ran before them all was asking for `k` more.

The induction generalizes `n`: each step hands the next one a guard whose index has already been
bumped. -/
theorem reorder_pairs_lenGt {inbox : String} {τ' : ComputableTLAPlus.Typ} {k : Nat}
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    (h : ConsumptionPairs inbox k A) {n : Nat} :
    NetworkPlusCal.Statement.listReducing' (V := V) (consumptions A) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing' (.await (lenGt τ' (inboxVar inbox τ') n)) =
      NetworkPlusCal.Statement.reducing' (V := V)
          (.await (lenGt τ' (inboxVar inbox τ') (n + k))) ∘ᵣ₂
        NetworkPlusCal.Statement.listReducing' (consumptions A) := by
  induction h generalizing n with
  | nil =>
    rw [consumptions_nil, NetworkPlusCal.Statement.listReducing'_nil, Nat.add_zero,
      Relation.lcomp₂.left_id_eq, Relation.lcomp₂.right_id_eq]
  | snoc _ hne IH =>
    rw [consumptions_append, NetworkPlusCal.Statement.listReducing'_append,
      consumptions_receiveInstrs, NetworkPlusCal.Statement.listReducing'_cons,
      NetworkPlusCal.Statement.listReducing'_cons, NetworkPlusCal.Statement.listReducing'_nil,
      Relation.lcomp₂.right_id_eq, ← Relation.lcomp₂.assoc,
      reorder_consumption_lenGt hne, Relation.lcomp₂.assoc, IH, ← Relation.lcomp₂.assoc,
      Nat.add_assoc, Nat.add_comm 1]

/-- **The whole accumulator past one compiled guard, for the runs that fail.**
`reorder_pairs_lenGt`'s aborting twin, and the same induction — `Relation.lcomp₁.commute_step` takes
the reducing equation the other half already proved, the induction hypothesis one pair further in,
and `reorder_consumption_lenGt_abort` for the pair itself, and does the algebra once.

The index bookkeeping is the same too: the guard arrives asking for `n + (k + 1)` and the step hands
its successor `n + 1`, which is why `n` is generalized. -/
theorem reorder_pairs_lenGt_abort {inbox : String} {τ' : ComputableTLAPlus.Typ} {k : Nat}
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    (h : ConsumptionPairs inbox k A) {n : Nat} :
    NetworkPlusCal.Statement.aborting' (V := V)
          (.await (lenGt τ' (inboxVar inbox τ') (n + k))) ∪
        NetworkPlusCal.Statement.reducing' (.await (lenGt τ' (inboxVar inbox τ') (n + k))) ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting' (consumptions A) ≤
      NetworkPlusCal.Statement.listAborting' (V := V) (consumptions A) ∪
        NetworkPlusCal.Statement.listReducing' (consumptions A) ∘ᵣ₁
          NetworkPlusCal.Statement.aborting' (.await (lenGt τ' (inboxVar inbox τ') n)) := by
  induction h generalizing n with
  | nil =>
    rw [consumptions_nil, NetworkPlusCal.Statement.listAborting'_nil,
      NetworkPlusCal.Statement.listReducing'_nil, Relation.lcomp₁.right_empty_eq_empty,
      Relation.lcomp₁.left_id_eq, Set.union_empty, Set.empty_union, Nat.add_zero]
  | snoc pairs _ IH =>
    rw [consumptions_append, NetworkPlusCal.Statement.listAborting'_append,
      NetworkPlusCal.Statement.listReducing'_append, Relation.lcomp₁.union_lcomp₂,
      consumptions_receiveInstrs, ← Nat.add_assoc, Nat.add_right_comm]
    exact Relation.lcomp₁.commute_step (reorder_pairs_lenGt pairs).symm IH le_rfl
      reorder_consumption_lenGt_abort

/-! ## The walk over a precondition block

  `processPrecondition` maps `stepStatement` over the block's statements, threading a `ReceiveState`
  through: how many `receive`s have been compiled, what they left pending, which channels were read.
  `Walk` below is what a refinement proof reads back off that walk — which target statement each
  source guard became, and what the accumulator held at the moment it did.

  It is the walk's *specification*, not a second implementation of it: `mapM_stepStatement_walk` is
  what ties it to the pass, and it says only what the semantic proof consumes. Reaching the pass's
  own `stepStatement`/`processPrecondition` at all is what `import all` above is for — the pass
  keeps them private, and this file is allowed past that rather than the pass widening its API.
-/

/-- What `processPrecondition`'s walk relates: the guards it read, the guards it emitted, and the
accumulator before and after. Each constructor is one `stepStatement` case.

Two things are worth reading off the shape. A `with`/`await` leaves the state alone but is rewritten
by everything accumulated *so far* — `st.newInstrs`, not the final list, which is what makes the
reorder lemmas apply one accumulated assignment at a time. A `receive` emits a guard indexed by
`st.i`, the count of receives *before* it, and appends its own consumption pair for every later
guard to be rewritten by. -/
private inductive Walk (chans : Guarded2NetworkChans) (inbox : String) :
    ReceiveState → List (ComputableGuardedPlusCal.Statement true false) →
      List (ComputableNetworkPlusCal.Statement true false) → ReceiveState → Prop
  | nil {st : ReceiveState} : Walk chans inbox st [] [] st
  | «with» {st st' : ReceiveState} {Ss res} {x ann bound e} :
      Walk chans inbox st Ss res st' →
      Walk chans inbox st (.with x ann bound e :: Ss)
        (substGuards st.newInstrs (.with x ann bound e) :: res) st'
  | await {st st' : ReceiveState} {Ss res} {e} :
      Walk chans inbox st Ss res st' →
      Walk chans inbox st (.await e :: Ss) (substGuards st.newInstrs (.await e) :: res) st'
  | receive {st st' : ReceiveState} {Ss res} {c r coe τ pos}
      (hτ : chans.lookup c.name = .some τ) :
      Walk chans inbox
        { i := st.i + 1, newInstrs := st.newInstrs ++ receiveInstrs r coe inbox τ pos,
          rxs := st.rxs.concat (c, τ) } Ss res st' →
      Walk chans inbox st (.receive c r coe :: Ss)
        (.await (lenGt τ (inboxVar inbox τ) st.i) :: res) st'

/-- Walks compose end to end. `Walk` is built head-first, but the `mapM` spec below accumulates
prefix-first, so every step of that spec extends a walk by one statement on the right — this is what
lets it. -/
private theorem Walk.append {chans : Guarded2NetworkChans} {inbox : String}
    {st₁ st₂ st₃ : ReceiveState} {Ss₁ Ss₂ res₁ res₂}
    (h₁ : Walk chans inbox st₁ Ss₁ res₁ st₂) (h₂ : Walk chans inbox st₂ Ss₂ res₂ st₃) :
    Walk chans inbox st₁ (Ss₁ ++ Ss₂) (res₁ ++ res₂) st₃ := by
  induction h₁ with
  | nil => exact h₂
  | «with» _ IH => exact .with (IH h₂)
  | await _ IH => exact .await (IH h₂)
  | receive hτ _ IH => exact .receive hτ (IH h₂)

/-- One guard in, one guard out. This is what says the block the pass rebuilds out of
`dropLast`/`getLast!` is non-empty, so that those two put it back together again. -/
private theorem Walk.length_eq {chans : Guarded2NetworkChans} {inbox : String}
    {st st' : ReceiveState} {Ss res} (h : Walk chans inbox st Ss res st') :
    res.length = Ss.length := by
  induction h with
  | nil => rfl
  | «with» _ IH | await _ IH | receive _ _ IH => rw [List.length_cons, List.length_cons, IH]

open Std.Do in
/-- One statement of the walk, as the Hoare triple `Spec.mapM_list`'s step obligation asks for:
whatever `stepStatement` returns extends the walk so far by exactly one entry. -/
private theorem stepStatement_walk {chans : Guarded2NetworkChans} {inbox : String}
    (S : ComputableGuardedPlusCal.Statement true false) {st : ReceiveState}
    {pref : List (ComputableGuardedPlusCal.Statement true false)}
    {bs : List (ComputableNetworkPlusCal.Statement true false)} :
    ⦃fun stf ↦ ⌜Walk chans inbox st pref bs stf⌝⦄
      (stepStatement (m := G2NM) chans inbox S)
    ⦃⇓? T stf' => ⌜Walk chans inbox st (pref ++ [S]) (bs ++ [T]) stf'⌝⦄ := by
  -- `mvcgen` leaves the invariant inaccessible; `next` is what names it without a `rename_i`
  cases S <;> simp only [stepStatement] <;> mvcgen
  next hwalk => exact hwalk.append (.with .nil)
  next hwalk => exact hwalk.append (.await .nil)
  next hwalk _ hτ => exact hwalk.append (.receive hτ .nil)

open Std.Do in
/-- **The walk's specification.** A precondition block's guards, mapped through `stepStatement` in
the pass's own monad, are exactly a `Walk` — which is what every later lemma about
`processPrecondition` inducts on.

`Spec.mapM_list` (`Extra/Do.lean`) is what makes this a loop-invariant proof rather than a manual
induction through `ExceptT`/`StateT`: the invariant is "the prefix walked so far is a `Walk`", the
one obligation per element is `stepStatement_walk`, and `G2NM.of_wp_run_eq` turns the resulting
triple back into a fact about the run the compilation hypothesis actually mentions. -/
private theorem mapM_stepStatement_walk {chans : Guarded2NetworkChans} {inbox : String}
    {Ss : List (ComputableGuardedPlusCal.Statement true false)}
    {results : List (ComputableNetworkPlusCal.Statement true false)}
    {st st' : ReceiveState} {n n' : Nat}
    (h : (((Ss.mapM (stepStatement (m := G2NM) chans inbox)).run st).run.run n) =
      (.ok (results, st'), n')) :
    Walk chans inbox st Ss results st' := by
  refine G2NM.of_wp_run_eq h (Walk chans inbox st Ss) ?_
  refine (λ _ ↦ Spec.mapM_list
    (inv := ((⇓? p stf => ⌜Walk chans inbox st p.1.prefix p.2 stf⌝) :
      Invariant Ss (List (ComputableNetworkPlusCal.Statement true false))
        (.arg ReceiveState (.except G2NError (.arg Nat .pure)))))
    (λ _ cur _ _ _ ↦ stepStatement_walk cur) st n Walk.nil)

open Std.Do in
/-- The walk as a spec `mvcgen` can use, at the initial state `processPrecondition` starts it from.

`Spec.mapM_list` gives a `Triple` for `Ss.mapM …` in `StateT ReceiveState G2NM`; the pass writes
`(Ss.mapM …).run {}`, which reduces to that program *applied* to `{}`. Applying the triple at `{}`
is all this is, and it is what lets `mvcgen` step through `processPrecondition` instead of stalling
on an applied `mapM` it has no spec for. -/
@[spec] private theorem mapM_stepStatement_spec {chans : Guarded2NetworkChans} {inbox : String}
    {Ss : List (ComputableGuardedPlusCal.Statement true false)} :
    ⦃⌜True⌝⦄
      ((Ss.mapM (stepStatement (m := G2NM) chans inbox)).run {})
    ⦃⇓? p n' => ⌜Walk chans inbox {} Ss p.1 p.2⌝⦄ :=
  λ n _ ↦ Spec.mapM_list
    (inv := ((λ p stf ↦ ⌜Walk chans inbox {} p.1.prefix p.2 stf⌝, ExceptConds.true) :
      Invariant Ss (List (ComputableNetworkPlusCal.Statement true false))
        (.arg ReceiveState (.except G2NError (.arg Nat .pure)))))
    (λ _ cur _ _ _ ↦ stepStatement_walk cur) {} n Walk.nil

/-- A branch with no precondition compiles to no guards, no consumption assignments and no
receives — and cannot fail doing it. -/
private theorem processPrecondition_none {chans : Guarded2NetworkChans} {inbox : String}
    {n : Nat} :
    ((processPrecondition (m := G2NM) chans inbox .none).run.run n) = (.ok (.none, [], []), n) :=
  rfl

/-- A branch that has a precondition compiles to one. Needed because the result's *shape* is what
`processPrecondition_walk` takes as given, while a caller stepping through `stepBranch` only knows
that the run succeeded. -/
private theorem processPrecondition_isSome {chans : Guarded2NetworkChans} {inbox : String}
    {B : GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement true) false}
    {o : Option (GuardedPlusCal.Block (ComputableNetworkPlusCal.Statement true) false)}
    {assigns : List (ComputableNetworkPlusCal.Statement false false)}
    {rxs : List (ComputableGuardedPlusCal.Ref × ComputableTLAPlus.Typ)} {n n' : Nat}
    (h : ((processPrecondition (m := G2NM) chans inbox (.some B)).run.run n) =
      (.ok (o, assigns, rxs), n')) :
    ∃ B', o = .some B' := by
  obtain ⟨⟨results, st⟩, n₁, -, hpure⟩ := G2NM.run_bind_eq_ok h
  have hp : ((Except.ok (Option.some { begin := results.dropLast, last := results.getLast! },
        consumptions st.newInstrs, st.rxs) : Except G2NError _), n₁) =
      (Except.ok (o, assigns, rxs), n') := hpure
  simp only [Prod.mk.injEq, Except.ok.injEq] at hp
  exact ⟨_, hp.1.1.symm⟩

/-- **What `processPrecondition` leaves behind.** The rewritten precondition block is the walk's
output, the assignments prepended to the action block are the walk's accumulator, and the channels
reported are the walk's `rxs` — all three read off one `Walk`, from the initial state `{}`.

The block is stated as `begin.concat last`, the same flattening the pass itself walks, because that
is the form `Block.reducing` reduces to; putting `dropLast`/`getLast!` back together is
`List.dropLast_concat_getLast!`, and `Walk.length_eq` is what earns its non-emptiness side
condition. -/
private theorem processPrecondition_walk {chans : Guarded2NetworkChans} {inbox : String}
    {B : GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement true) false}
    {B' : GuardedPlusCal.Block (ComputableNetworkPlusCal.Statement true) false}
    {assigns : List (ComputableNetworkPlusCal.Statement false false)}
    {rxs : List (ComputableGuardedPlusCal.Ref × ComputableTLAPlus.Typ)} {n n' : Nat}
    (h : ((processPrecondition (m := G2NM) chans inbox (.some B)).run.run n) =
      (.ok (.some B', assigns, rxs), n')) :
    ∃ st, Walk chans inbox {} (B.begin.concat B.last) (B'.begin.concat B'.last) st ∧
      assigns = consumptions st.newInstrs ∧ rxs = st.rxs := by
  obtain ⟨⟨results, st⟩, n₁, hrun, hpure⟩ := G2NM.run_bind_eq_ok h
  have hwalk := mapM_stepStatement_walk hrun
  have hp : ((Except.ok (Option.some { begin := results.dropLast, last := results.getLast! },
        consumptions st.newInstrs, st.rxs) : Except G2NError _), n₁) =
      (Except.ok (.some B', assigns, rxs), n') := hpure
  simp only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at hp
  obtain ⟨⟨rfl, rfl, rfl⟩, -⟩ := hp
  have hne : results ≠ [] := by
    rw [← List.length_pos_iff, hwalk.length_eq, List.length_concat]
    omega
  refine ⟨st, ?_, rfl, rfl⟩
  rwa [List.dropLast_concat_getLast! hne]

/-! ## From the emitted ordering to the adjacent one

  The target the pass produces runs every compiled guard and *then* every consumption assignment.
  `receive_refines` is proved in the ordering where each `receive`'s two assignments sit immediately
  after its own guard. Getting from one to the other is pure equational work — no refinement
  reasoning, no `relatesTo` — and it is why the mid-walk state never has to be related to anything:
  the two orderings are the *same relation*, and only its endpoints are ever quantified.

  Each step of the walk pushes the pending accumulator `⟦consumptions st.newInstrs⟧` one statement to
  the left. Past a guard the source wrote, that is `reorder_assigns_guard'` — substitution. Past a
  guard the pass invented, it is `reorder_pairs_lenGt` — the index bumps by the number of pending
  pairs, which is `st.i`, which is what `ConsumptionPairs` is carried along to know.
-/

omit [SeqBuiltins V] in
/-- The pending accumulator moved past one source-written guard, with the rest of the block along
for the ride. `reorder_assigns_guard'` with its two operands re-associated, which is all the walk's
`with`/`await` case is. -/
theorem reorder_pending_guard
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {S : ComputableNetworkPlusCal.Statement true false}
    {adj : Set (LocalState' V × Trace V × LocalState' V)}
    (fresh : ∀ a ∈ A, GuardFresh a.1 a.2.1 S) :
    NetworkPlusCal.Statement.listReducing' (V := V) (consumptions A) ∘ᵣ₂
        (NetworkPlusCal.Statement.reducing' S ∘ᵣ₂ adj) =
      NetworkPlusCal.Statement.reducing' (substGuards A S) ∘ᵣ₂
        (NetworkPlusCal.Statement.listReducing' (consumptions A) ∘ᵣ₂ adj) := by
  rw [Relation.lcomp₂.assoc, reorder_assigns_guard' fresh, ← Relation.lcomp₂.assoc]

/-- The pending accumulator moved past one *compiled* guard and absorbed into the pair that guard's
`receive` contributes. The guard's index picks up `k`, the number of pairs already pending, and the
new pair joins them — which is exactly the state `stepStatement` hands its successor. -/
theorem reorder_pending_receive {inbox : String} {τ : ComputableTLAPlus.Typ} {k : Nat}
    {r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion} {pos : SourceSpan}
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {adj : Set (LocalState' V × Trace V × LocalState' V)}
    (pairs : ConsumptionPairs inbox k A) :
    NetworkPlusCal.Statement.listReducing' (V := V) (consumptions A) ∘ᵣ₂
        (NetworkPlusCal.Statement.reducing' (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₂
          NetworkPlusCal.Statement.listReducing'
            [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
              .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] ∘ᵣ₂ adj) =
      NetworkPlusCal.Statement.reducing' (V := V) (.await (lenGt τ (inboxVar inbox τ) k)) ∘ᵣ₂
        (NetworkPlusCal.Statement.listReducing'
          (consumptions (A ++ receiveInstrs r coe inbox τ pos)) ∘ᵣ₂ adj) := by
  rw [Relation.lcomp₂.assoc, reorder_pairs_lenGt pairs, ← Relation.lcomp₂.assoc,
    Relation.lcomp₂.assoc
      (R₁ := NetworkPlusCal.Statement.listReducing' (V := V) (consumptions A)),
    ← consumptions_receiveInstrs (r := r) (coe := coe) (pos := pos),
    ← NetworkPlusCal.Statement.listReducing'_append, ← consumptions_append, Nat.zero_add]

/-- One `receive`'s adjacent target: its inbox-length guard, then the two consumption assignments
it contributes. Named because it appears four times — twice in `Adjacent`, twice in the refinement
below — and because it is `receive_refines`'s target. -/
def receiveGroup (r : ComputableGuardedPlusCal.Ref) (coe : TypedTLAPlus.Coercion) (inbox : String)
    (τ : ComputableTLAPlus.Typ) : Set (LocalState' V × Trace V × LocalState' V) :=
  NetworkPlusCal.Statement.reducing' (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₂
    NetworkPlusCal.Statement.listReducing'
      [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
        .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))]

@[inherit_doc receiveGroup]
def receiveGroupAborting (r : ComputableGuardedPlusCal.Ref) (coe : TypedTLAPlus.Coercion)
    (inbox : String) (τ : ComputableTLAPlus.Typ) : Set (LocalState' V × Trace V) :=
  NetworkPlusCal.Statement.aborting' (.await (lenGt τ (inboxVar inbox τ) 0)) ∪
    NetworkPlusCal.Statement.reducing' (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₁
      NetworkPlusCal.Statement.listAborting'
        [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
          .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))]

/-- `receive_refines` at the two named groups, with the trailing `Relation.Idle`/`∅` the list forms
carry discharged. Nothing new — the same theorem, in the shape `Adjacent` states. -/
theorem receiveGroup_refines {c r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ : ComputableTLAPlus.Typ} (fresh : ReceiveFresh c r inbox) :
    StrongRefinement (relatesTo (V := V) (.some (c, inbox))) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.reducing' (.receive c r coe))
      (GuardedPlusCal.Statement.aborting' (.receive c r coe))
      (GuardedPlusCal.Statement.diverging' (.receive c r coe))
      (receiveGroup r coe inbox τ) (receiveGroupAborting r coe inbox τ) ∅ := by
  rw [receiveGroup, receiveGroupAborting, NetworkPlusCal.Statement.listReducing'_cons,
    NetworkPlusCal.Statement.listReducing'_cons, NetworkPlusCal.Statement.listReducing'_nil,
    Relation.lcomp₂.right_id_eq, NetworkPlusCal.Statement.listAborting'_cons,
    NetworkPlusCal.Statement.listAborting'_cons, NetworkPlusCal.Statement.listAborting'_nil,
    Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]
  exact receive_refines fresh

/-- **What the walk needs of the source block, in source terms.** No `with` in the block binds a
name that a consumption pair generated by one of the block's `receive`s would read.

Stated over `receiveInstrs` rather than over the accumulator itself because the accumulator only
exists once the walk has run; `AccFresh` below is the running form, and this is what re-establishes
it each time a `receive` grows the accumulator.

A syntactic freshness condition, so it stays a hypothesis — discharging it needs well-scopedness and
the passes before this one. `WellScopedIn` requires a `with`'s bound name to be absent from the
enclosing scope, and everything a pair reads — the inbox, and the `Head`/`Tail` operator names that
`Expression.freeVars` counts like any other variable — is in that scope. -/
def PairsFresh (inbox : String) (Ss : List (ComputableGuardedPlusCal.Statement true false)) : Prop :=
  ∀ x ann bound e, GuardedPlusCal.Statement.with x ann bound e ∈ Ss →
    ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss →
        ∀ τ pos, ∀ a ∈ receiveInstrs r coe inbox τ pos,
          x ∉ GuardedPlusCal.Ref.freeVars a.1 ∧ Expression.FreshIn x a.2.1

/-- Fewer statements can only make the condition easier: it quantifies over pairs drawn from the
list on both sides. What lets the walk hand each step the condition for the suffix it is looking
at. -/
theorem PairsFresh.mono {inbox : String}
    {Ss Ss' : List (ComputableGuardedPlusCal.Statement true false)} (sub : Ss' ⊆ Ss)
    (h : PairsFresh inbox Ss) : PairsFresh inbox Ss' :=
  λ x ann bound e hw c r coe hr ↦ h x ann bound e (sub hw) c r coe (sub hr)

/-- `PairsFresh`'s running form: the accumulator built so far is fresh for every `with` still to
come. This is what `stepStatement_spec`'s precondition asks for, and what the loop invariant has to
carry — it shrinks as the suffix shrinks and has to be re-established when a `receive` extends the
accumulator. -/
private def AccFresh (inbox : String) (st : ReceiveState)
    (suff : List (ComputableGuardedPlusCal.Statement true false)) : Prop :=
  ∀ a ∈ st.newInstrs, ∀ x ann bound e,
    GuardedPlusCal.Statement.with x ann bound e ∈ suff →
      x ∉ GuardedPlusCal.Ref.freeVars a.1 ∧ Expression.FreshIn x a.2.1

/-- **The walk's loop invariant.** What holds of `stepStatement`'s state once the prefix `pref` of a
precondition has been compiled to `results`: the accumulator is exactly `st.i` consumption pairs, and
`pref` already refines the emitted guards followed by those pending pairs.

Carrying the refinement *here* is the whole design. Each pair is moved past the guards that follow it
by the very step that produces it, so no two orderings of a whole block ever have to be related — the
`Head`/`Tail` bookkeeping stays local to one step. -/
private def WalkInv (c₀ : ComputableGuardedPlusCal.Ref) (inbox : String)
    (pref : List (ComputableGuardedPlusCal.Statement true false))
    (results : List (ComputableNetworkPlusCal.Statement true false))
    (st : ReceiveState) : Prop :=
  ConsumptionPairs inbox st.i st.newInstrs ∧ results.length = pref.length ∧
    StrongRefinement (relatesTo (V := V) (.some (c₀, inbox))) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.listReducing' pref)
      (GuardedPlusCal.Statement.listAborting' pref)
      ∅
      (NetworkPlusCal.Statement.listReducing' results ∘ᵣ₂
        NetworkPlusCal.Statement.listReducing' (consumptions st.newInstrs))
      (NetworkPlusCal.Statement.listAborting' results ∪
        NetworkPlusCal.Statement.listReducing' results ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting' (consumptions st.newInstrs))
      ∅

/-- The invariant holds at the start: nothing walked, nothing emitted, nothing pending. -/
private theorem WalkInv.nil {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} :
    WalkInv (V := V) c₀ inbox [] [] {} := by
  refine ⟨.nil, rfl, ?_⟩
  -- `simp only`, not `rw`: `({} : ReceiveState).newInstrs` is a projection out of a structure
  -- literal, and `rw`'s syntactic match never gets past it to `consumptions_nil`
  simp only [GuardedPlusCal.Statement.listReducing'_nil, GuardedPlusCal.Statement.listAborting'_nil,
    consumptions_nil, NetworkPlusCal.Statement.listReducing'_nil,
    NetworkPlusCal.Statement.listAborting'_nil, Relation.lcomp₂.left_id_eq,
    Relation.lcomp₁.right_empty_eq_empty, Set.union_self]
  exact StrongRefinement.ofNonDiverging _ (StrongRefinement.Terminating.Id _)
    (StrongRefinement.Aborting.Empty _)

open Std.Do in
/-- **One step of the walk, as a local refinement.** `stepStatement` extends the invariant by one
source statement: whatever it emits, together with whatever it appends to the accumulator, refines
the source statement composed onto the prefix.

The freshness side condition sits in the precondition rather than in the signature because it is
about the *accumulator*, which only exists at run time — the same reason prior art threads
well-scopedness through its own loop invariant instead of assuming it up front. -/
private theorem stepStatement_spec {chans : Guarded2NetworkChans}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
    (S : ComputableGuardedPlusCal.Statement true false)
    {pref : List (ComputableGuardedPlusCal.Statement true false)}
    {results : List (ComputableNetworkPlusCal.Statement true false)}
    {suff : List (ComputableGuardedPlusCal.Statement true false)}
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      S = GuardedPlusCal.Statement.receive c r coe → c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : Fresh (.some (c₀, inbox)) S) (pfresh : PairsFresh inbox (S :: suff)) :
    ⦃λ st ↦ ⌜WalkInv (V := V) c₀ inbox pref results st ∧ AccFresh inbox st (S :: suff)⌝⦄
      (stepStatement (m := G2NM) chans inbox S)
    ⦃⇓? T st' => ⌜WalkInv (V := V) c₀ inbox (pref ++ [S]) (results ++ [T]) st' ∧
      AccFresh inbox st' suff⌝⦄ := by
  -- one line, and every `wp` is gone: three goals, one per guard constructor, each a plain
  -- `WalkInv` obligation with the incoming invariant in context
  mintro ⟨inv, gf⟩
  cases S <;> simp only [stepStatement] <;> mvcgen
  case vc1.with name ann bound e st n hinv =>
    obtain ⟨⟨pairs, hlen, ref⟩, gf'⟩ := hinv
    refine ⟨⟨pairs, by simp [hlen], ?_⟩, λ a ha x _ _ _ hm ↦ gf' a ha x _ _ _ (List.mem_cons_of_mem _ hm)⟩
    have hfresh : ∀ a ∈ st.newInstrs,
        GuardFresh a.1 a.2.1 (NetworkPlusCal.Statement.with name ann bound e) := by
      intro a ha x _ _ _ heq
      injection heq with hx _ _ _
      subst hx
      exact gf' a ha _ _ _ _ List.mem_cons_self
    simp only [GuardedPlusCal.Statement.listReducing'_append,
      GuardedPlusCal.Statement.listAborting'_append,
      NetworkPlusCal.Statement.listReducing'_append,
      NetworkPlusCal.Statement.listAborting'_append,
      GuardedPlusCal.Statement.listReducing'_cons, GuardedPlusCal.Statement.listReducing'_nil,
      GuardedPlusCal.Statement.listAborting'_cons, GuardedPlusCal.Statement.listAborting'_nil,
      NetworkPlusCal.Statement.listReducing'_cons, NetworkPlusCal.Statement.listReducing'_nil,
      NetworkPlusCal.Statement.listAborting'_cons, NetworkPlusCal.Statement.listAborting'_nil,
      Relation.lcomp₂.right_id_eq, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty,
      Relation.lcomp₁.union_lcomp₂]
    rw [← Relation.lcomp₂.assoc, ← reorder_assigns_guard' hfresh, Relation.lcomp₂.assoc,
      with_reducing'_eq]
    have hcomp := StrongRefinement.Comp _ ref
      (guard_refines (GuardedPlusCal.Statement.with name ann bound e)
        (λ _ _ _ h ↦ nomatch h) gfresh)
    simp only [GuardedPlusCal.Statement.diverging'_eq_empty,
      Relation.lcomp₁.right_empty_eq_empty, Set.union_self] at hcomp
    refine StrongRefinement.Mono le_rfl le_rfl le_rfl le_rfl ?_ le_rfl hcomp
    rw [Relation.lcomp₁.union_lcomp₂, ← with_aborting'_eq]
    exact Set.union_le_union le_rfl
      (Relation.lcomp₁.mono le_rfl (reorder_assigns_guard_abort' hfresh))
  case vc1.await e st n hinv =>
    obtain ⟨⟨pairs, hlen, ref⟩, gf'⟩ := hinv
    refine ⟨⟨pairs, by simp [hlen], ?_⟩, λ a ha x _ _ _ hm ↦ gf' a ha x _ _ _ (List.mem_cons_of_mem _ hm)⟩
    -- an `await` binds nothing, so its freshness against the accumulator is unconditional
    have hfresh : ∀ a ∈ st.newInstrs,
        GuardFresh a.1 a.2.1 (NetworkPlusCal.Statement.await e) := λ _ _ ↦ GuardFresh.await
    simp only [GuardedPlusCal.Statement.listReducing'_append,
      GuardedPlusCal.Statement.listAborting'_append,
      NetworkPlusCal.Statement.listReducing'_append,
      NetworkPlusCal.Statement.listAborting'_append,
      GuardedPlusCal.Statement.listReducing'_cons, GuardedPlusCal.Statement.listReducing'_nil,
      GuardedPlusCal.Statement.listAborting'_cons, GuardedPlusCal.Statement.listAborting'_nil,
      NetworkPlusCal.Statement.listReducing'_cons, NetworkPlusCal.Statement.listReducing'_nil,
      NetworkPlusCal.Statement.listAborting'_cons, NetworkPlusCal.Statement.listAborting'_nil,
      Relation.lcomp₂.right_id_eq, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty,
      Relation.lcomp₁.union_lcomp₂]
    rw [← Relation.lcomp₂.assoc, ← reorder_assigns_guard' hfresh, Relation.lcomp₂.assoc,
      await_reducing'_eq]
    have hcomp := StrongRefinement.Comp _ ref
      (guard_refines (GuardedPlusCal.Statement.await e) (λ _ _ _ h ↦ nomatch h) gfresh)
    simp only [GuardedPlusCal.Statement.diverging'_eq_empty,
      Relation.lcomp₁.right_empty_eq_empty, Set.union_self] at hcomp
    refine StrongRefinement.Mono le_rfl le_rfl le_rfl le_rfl ?_ le_rfl hcomp
    rw [Relation.lcomp₁.union_lcomp₂, ← await_aborting'_eq]
    exact Set.union_le_union le_rfl
      (Relation.lcomp₁.mono le_rfl (reorder_assigns_guard_abort' hfresh))
  case vc2.receive.h_2 c r coe st n hinv τ hτ =>
    obtain ⟨⟨pairs, hlen, ref⟩, gf'⟩ := hinv
    obtain ⟨rfl, hfr⟩ := rfresh c r coe rfl
    refine ⟨⟨pairs.snoc (ne_name_of_fresh hfr.2.1).symm, by simp [hlen], ?_⟩, ?_⟩
    case' refine_2 =>
      intro a ha x ann bound e hm
      rcases List.mem_append.mp ha with h' | h'
      · exact gf' a h' x ann bound e (List.mem_cons_of_mem _ hm)
      · exact pfresh x ann bound e (List.mem_cons_of_mem _ hm) c r coe List.mem_cons_self _ _ a h'
    simp only [GuardedPlusCal.Statement.listReducing'_append,
      GuardedPlusCal.Statement.listAborting'_append,
      NetworkPlusCal.Statement.listReducing'_append,
      NetworkPlusCal.Statement.listAborting'_append,
      GuardedPlusCal.Statement.listReducing'_cons, GuardedPlusCal.Statement.listReducing'_nil,
      GuardedPlusCal.Statement.listAborting'_cons, GuardedPlusCal.Statement.listAborting'_nil,
      NetworkPlusCal.Statement.listReducing'_cons, NetworkPlusCal.Statement.listReducing'_nil,
      NetworkPlusCal.Statement.listAborting'_cons, NetworkPlusCal.Statement.listAborting'_nil,
      Relation.lcomp₂.right_id_eq, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty,
      Relation.lcomp₁.union_lcomp₂, consumptions_append, consumptions_cons, consumptions_nil]
    -- the walk emits this guard at `st.i`; both reorder lemmas state that index as `0 + st.i`
    have hQ := reorder_pairs_lenGt (V := V) (τ' := τ) pairs (n := 0)
    have hQa := reorder_pairs_lenGt_abort (V := V) (τ' := τ) pairs (n := 0)
    rw [Nat.zero_add] at hQ hQa
    have hcomp := StrongRefinement.Comp _ ref
      (receiveGroup_refines (V := V) (coe := coe) (τ := τ) hfr)
    simp only [GuardedPlusCal.Statement.diverging'_eq_empty,
      Relation.lcomp₁.right_empty_eq_empty, Set.union_self, receiveGroup, receiveGroupAborting,
      NetworkPlusCal.Statement.listReducing'_cons, NetworkPlusCal.Statement.listReducing'_nil,
      NetworkPlusCal.Statement.listAborting'_cons, NetworkPlusCal.Statement.listAborting'_nil,
      Relation.lcomp₂.right_id_eq, Set.union_empty] at hcomp
    refine StrongRefinement.Mono le_rfl le_rfl le_rfl ?_ ?_ le_rfl hcomp
    · refine le_of_eq ?_
      -- `@@` is `registerSource`, invisible to defeq but not to `rw`'s syntactic match
      simp only [registerSource, inboxVar, ← Relation.lcomp₂.assoc] at hQ ⊢
      rw [Relation.lcomp₂.assoc (R₁ := (NetworkPlusCal.Statement.await
          (lenGt τ (.var inbox (.seq τ) .binder) st.i)).reducing'),
        ← hQ, ← Relation.lcomp₂.assoc]
      rfl
    · simp only [registerSource, inboxVar, inboxRef] at hQ hQa ⊢
      rw [Relation.lcomp₁.union_lcomp₂]
      exact Set.union_le_union le_rfl (Relation.lcomp₁.mono le_rfl
        (Relation.lcomp₁.commute_step hQ.symm hQa le_rfl le_rfl))

open Std.Do in
/-- **The whole walk.** `Spec.mapM_list` at the invariant `stepStatement_spec` maintains: the prefix
compiled so far refines what was emitted for it followed by whatever is still pending, and the
accumulator stays fresh for the statements yet to come.

Both conjuncts are needed and neither can be dropped — the refinement is the point, and `AccFresh`
is what the next step's precondition asks for. It shrinks with the suffix on a guard and is
re-established from `PairsFresh` when a `receive` grows the accumulator. -/
private theorem mapM_stepStatement_refines {chans : Guarded2NetworkChans}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
    {Ss : List (ComputableGuardedPlusCal.Statement true false)}
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss → c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : ∀ S ∈ Ss, Fresh (.some (c₀, inbox)) S) (pfresh : PairsFresh inbox Ss) :
    ⦃λ stf ↦ ⌜WalkInv (V := V) c₀ inbox [] [] stf ∧ AccFresh inbox stf Ss⌝⦄
      Ss.mapM (stepStatement (m := G2NM) chans inbox)
    ⦃⇓? bs stf' => ⌜WalkInv (V := V) c₀ inbox Ss bs stf' ∧ AccFresh inbox stf' []⌝⦄ :=
  Spec.mapM_list
    (inv := ((λ q stf ↦ ⌜WalkInv (V := V) c₀ inbox q.1.prefix q.2 stf ∧
        AccFresh inbox stf q.1.suffix⌝, ExceptConds.true) :
      Invariant Ss (List (ComputableNetworkPlusCal.Statement true false))
        (.arg ReceiveState (.except G2NError (.arg Nat .pure)))))
    (λ pref cur suff h bs ↦
      stepStatement_spec (V := V) (c₀ := c₀) cur
        (λ c r coe heq ↦ rfresh c r coe (heq ▸ h ▸ List.mem_append_right _ List.mem_cons_self))
        (gfresh cur (h ▸ List.mem_append_right _ List.mem_cons_self))
        (pfresh.mono (h ▸ List.subset_append_right _ _)))

open Std.Do in
/-- `mapM_stepStatement_refines` at the initial state, which is the form `processPrecondition`'s own
body presents: it writes `(… .mapM …).run {}`, and `StateT.run x s` reduces to `x s`, so the
toolchain's `[spec] StateT.run` never fires and `mvcgen` cannot descend on its own.

Registered `@[spec]` so the block-level proof never has to look inside the walk. -/
@[spec] private theorem mapM_stepStatement_refines_run {chans : Guarded2NetworkChans}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
    {Ss : List (ComputableGuardedPlusCal.Statement true false)}
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss → c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : ∀ S ∈ Ss, Fresh (.some (c₀, inbox)) S) (pfresh : PairsFresh inbox Ss) :
    ⦃⌜True⌝⦄
      ((Ss.mapM (stepStatement (m := G2NM) chans inbox)).run {})
    ⦃⇓? p n' => ⌜WalkInv (V := V) c₀ inbox Ss p.1 p.2 ∧ AccFresh inbox p.2 []⌝⦄ :=
  λ n _ ↦ mapM_stepStatement_refines (V := V) rfresh gfresh pfresh {} n
    ⟨WalkInv.nil, λ _ ha ↦ nomatch ha⟩

/-- The adjacent ordering of a precondition block's target, as a relation. One constructor per
source guard, mirroring `Walk`, but recording *meaning* rather than syntax: the adjacent form
interleaves guard-class and action-class statements, so it is not a list of statements in either
class and has to be a relation.

The `receive` case is `receive_refines`'s target — which is the point of the whole detour. -/
inductive Adjacent (chans : Guarded2NetworkChans) (inbox : String) :
    List (ComputableGuardedPlusCal.Statement true false) →
      Set (LocalState' V × Trace V × LocalState' V) → Set (LocalState' V × Trace V) → Prop
  | nil : Adjacent chans inbox [] Relation.Idle ∅
  | «with» {x ann bound e Ss adj adj'} : Adjacent chans inbox Ss adj adj' →
      Adjacent chans inbox (.with x ann bound e :: Ss)
        (NetworkPlusCal.Statement.reducing' (.with x ann bound e) ∘ᵣ₂ adj)
        (NetworkPlusCal.Statement.aborting' (.with x ann bound e) ∪
          NetworkPlusCal.Statement.reducing' (.with x ann bound e) ∘ᵣ₁ adj')
  | await {e Ss adj adj'} : Adjacent chans inbox Ss adj adj' →
      Adjacent chans inbox (.await e :: Ss)
        (NetworkPlusCal.Statement.reducing' (.await e) ∘ᵣ₂ adj)
        (NetworkPlusCal.Statement.aborting' (.await e) ∪
          NetworkPlusCal.Statement.reducing' (.await e) ∘ᵣ₁ adj')
  | receive {c r coe τ Ss adj adj'} (hτ : chans.lookup c.name = .some τ) :
      Adjacent chans inbox Ss adj adj' →
      Adjacent chans inbox (.receive c r coe :: Ss)
        (receiveGroup (V := V) r coe inbox τ ∘ᵣ₂ adj)
        (receiveGroupAborting (V := V) r coe inbox τ ∪ receiveGroup r coe inbox τ ∘ᵣ₁ adj')

omit [SeqBuiltins V] in
/-- Every walk has an adjacent ordering: the walk is what certifies each `receive`'s channel
resolves, which is the only thing `Adjacent` cannot supply for itself. -/
private theorem Walk.adjacent {chans : Guarded2NetworkChans} {inbox : String}
    {st st' : ReceiveState} {Ss res} (h : Walk chans inbox st Ss res st') :
    ∃ adj adj', Adjacent (V := V) chans inbox Ss adj adj' := by
  induction h with
  | nil => exact ⟨_, _, .nil⟩
  | «with» _ IH =>
    obtain ⟨_, _, IH⟩ := IH
    exact ⟨_, _, .with IH⟩
  | await _ IH =>
    obtain ⟨_, _, IH⟩ := IH
    exact ⟨_, _, .await IH⟩
  | receive hτ _ IH =>
    obtain ⟨_, _, IH⟩ := IH
    exact ⟨_, _, .receive hτ IH⟩

/-- The accumulator only ever grows on the right. Needed so that a freshness condition stated once
about the *final* accumulator covers every intermediate one. -/
private theorem Walk.newInstrs_prefix {chans : Guarded2NetworkChans} {inbox : String}
    {st st' : ReceiveState} {Ss res} (h : Walk chans inbox st Ss res st') :
    st.newInstrs <+: st'.newInstrs := by
  induction h with
  | nil => exact List.prefix_rfl
  | «with» _ IH | await _ IH => exact IH
  | receive _ _ IH => exact List.IsPrefix.trans (List.prefix_append _ _) IH

/-- **The two orderings are the same relation.** Reading the equation right to left: the pass's
output — every compiled guard, then every consumption assignment — is the adjacent ordering with
whatever was already pending still in front of it. At the top of a block nothing is pending, so it
says the emitted target *is* the adjacent one.

Both freshness hypotheses are conditions on the source program, and both concern the pass's own
generated names rather than anything a user wrote: no `with` in the block may bind a name a pending
consumption assignment reads, and no `receive` may target the `inbox` itself. -/
private theorem Walk.reorder {chans : Guarded2NetworkChans} {inbox : String}
    {st st' : ReceiveState} {Ss res} {adj : Set (LocalState' V × Trace V × LocalState' V)}
    {adj' : Set (LocalState' V × Trace V)}
    (walk : Walk chans inbox st Ss res st') (adjacent : Adjacent chans inbox Ss adj adj')
    (pairs : ConsumptionPairs inbox st.i st.newInstrs)
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss → r.name ≠ inbox)
    (gfresh : ∀ a ∈ st'.newInstrs, ∀ x ann bound e,
      GuardedPlusCal.Statement.with x ann bound e ∈ Ss →
        x ∉ GuardedPlusCal.Ref.freeVars a.1 ∧ Expression.FreshIn x a.2.1) :
    NetworkPlusCal.Statement.listReducing' (V := V) (consumptions st.newInstrs) ∘ᵣ₂ adj =
      NetworkPlusCal.Statement.listReducing' res ∘ᵣ₂
        NetworkPlusCal.Statement.listReducing' (consumptions st'.newInstrs) := by
  induction walk generalizing adj adj' with
  | nil =>
    cases adjacent
    rw [NetworkPlusCal.Statement.listReducing'_nil, Relation.lcomp₂.left_id_eq,
      Relation.lcomp₂.right_id_eq]
  | «with» walk IH =>
    cases adjacent with
    | «with» adjacent =>
      rw [NetworkPlusCal.Statement.listReducing'_cons, reorder_pending_guard ?fresh,
        IH adjacent pairs (λ c r coe h ↦ rfresh c r coe (List.mem_cons_of_mem _ h))
          (λ a ha x ann bound e h ↦ gfresh a ha x ann bound e (List.mem_cons_of_mem _ h)),
        Relation.lcomp₂.assoc]
      case fresh =>
        intro a ha _ _ _ _ hS
        cases hS
        exact gfresh a (walk.newInstrs_prefix.subset ha) _ _ _ _ List.mem_cons_self
  | await _ IH =>
    cases adjacent with
    | await adjacent =>
      rw [NetworkPlusCal.Statement.listReducing'_cons,
        reorder_pending_guard (λ _ _ ↦ GuardFresh.await),
        IH adjacent pairs (λ c r coe h ↦ rfresh c r coe (List.mem_cons_of_mem _ h))
          (λ a ha x ann bound e h ↦ gfresh a ha x ann bound e (List.mem_cons_of_mem _ h)),
        Relation.lcomp₂.assoc]
  | receive hτ _ IH =>
    cases adjacent with
    | receive hτ' adjacent =>
      obtain rfl := Option.some.inj (hτ'.symm.trans hτ)
      rw [receiveGroup, ← Relation.lcomp₂.assoc, reorder_pending_receive pairs,
        IH adjacent (pairs.snoc (rfresh _ _ _ List.mem_cons_self))
          (λ c r coe h ↦ rfresh c r coe (List.mem_cons_of_mem _ h))
          (λ a ha x ann bound e h ↦ gfresh a ha x ann bound e (List.mem_cons_of_mem _ h)),
        NetworkPlusCal.Statement.listReducing'_cons, Relation.lcomp₂.assoc]

/-- **And the failing runs are ordered.** `Walk.reorder`'s aborting counterpart: the emitted target
— every compiled guard, then every consumption assignment — can only abort where the adjacent
ordering with the same accumulator pending in front of it can.

An inclusion, and only this direction is wanted. `StrongRefinement.Mono` *shrinks* a target, so a
target that aborts in fewer states is one the same source still refines; the reverse inclusion is
false anyway, since a guard can block where an assignment cannot.

The shape of the induction is `Walk.reorder`'s, with `Relation.lcomp₁.commute_step` where that one
had a chain of associativity rewrites. Every constructor supplies the same three things: the reducing
equation the other half already proved, its aborting counterpart, and the induction hypothesis. The
hypotheses are `Walk.reorder`'s, unchanged and needed for the same reasons. -/
private theorem Walk.reorder_aborting {chans : Guarded2NetworkChans} {inbox : String}
    {st st' : ReceiveState} {Ss res} {adj : Set (LocalState' V × Trace V × LocalState' V)}
    {adj' : Set (LocalState' V × Trace V)}
    (walk : Walk chans inbox st Ss res st') (adjacent : Adjacent chans inbox Ss adj adj')
    (pairs : ConsumptionPairs inbox st.i st.newInstrs)
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss → r.name ≠ inbox)
    (gfresh : ∀ a ∈ st'.newInstrs, ∀ x ann bound e,
      GuardedPlusCal.Statement.with x ann bound e ∈ Ss →
        x ∉ GuardedPlusCal.Ref.freeVars a.1 ∧ Expression.FreshIn x a.2.1) :
    NetworkPlusCal.Statement.listAborting' (V := V) res ∪
        NetworkPlusCal.Statement.listReducing' res ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting' (consumptions st'.newInstrs) ≤
      NetworkPlusCal.Statement.listAborting' (V := V) (consumptions st.newInstrs) ∪
        NetworkPlusCal.Statement.listReducing' (consumptions st.newInstrs) ∘ᵣ₁ adj' := by
  induction walk generalizing adj adj' with
  | nil =>
    cases adjacent
    rw [NetworkPlusCal.Statement.listAborting'_nil, NetworkPlusCal.Statement.listReducing'_nil,
      Relation.lcomp₁.left_id_eq, Relation.lcomp₁.right_empty_eq_empty, Set.empty_union,
      Set.union_empty]
  | «with» walk IH =>
    cases adjacent with
    | «with» adjacent =>
      rw [NetworkPlusCal.Statement.listAborting'_cons,
        NetworkPlusCal.Statement.listReducing'_cons, Relation.lcomp₁.union_lcomp₂]
      refine Relation.lcomp₁.commute_step (reorder_assigns_guard' ?fresh).symm
        (reorder_assigns_guard_abort' ?fresh)
        (IH adjacent pairs (λ c r coe h ↦ rfresh c r coe (List.mem_cons_of_mem _ h))
          (λ a ha x ann bound e h ↦ gfresh a ha x ann bound e (List.mem_cons_of_mem _ h))) le_rfl
      case fresh =>
        intro a ha _ _ _ _ hS
        cases hS
        exact gfresh a (walk.newInstrs_prefix.subset ha) _ _ _ _ List.mem_cons_self
  | await _ IH =>
    cases adjacent with
    | await adjacent =>
      rw [NetworkPlusCal.Statement.listAborting'_cons,
        NetworkPlusCal.Statement.listReducing'_cons, Relation.lcomp₁.union_lcomp₂]
      exact Relation.lcomp₁.commute_step (reorder_assigns_guard' (λ _ _ ↦ GuardFresh.await)).symm
        (reorder_assigns_guard_abort' (λ _ _ ↦ GuardFresh.await))
        (IH adjacent pairs (λ c r coe h ↦ rfresh c r coe (List.mem_cons_of_mem _ h))
          (λ a ha x ann bound e h ↦ gfresh a ha x ann bound e (List.mem_cons_of_mem _ h))) le_rfl
  | receive hτ _ IH =>
    cases adjacent with
    | receive hτ' adjacent =>
      obtain rfl := Option.some.inj (hτ'.symm.trans hτ)
      have hmid := IH adjacent (pairs.snoc (rfresh _ _ _ List.mem_cons_self))
        (λ c r coe h ↦ rfresh c r coe (List.mem_cons_of_mem _ h))
        (λ a ha x ann bound e h ↦ gfresh a ha x ann bound e (List.mem_cons_of_mem _ h))
      rw [consumptions_append, consumptions_receiveInstrs,
        NetworkPlusCal.Statement.listAborting'_append,
        NetworkPlusCal.Statement.listReducing'_append, Relation.lcomp₁.union_lcomp₂] at hmid
      rw [NetworkPlusCal.Statement.listAborting'_cons,
        NetworkPlusCal.Statement.listReducing'_cons, Relation.lcomp₁.union_lcomp₂, receiveGroup,
        receiveGroupAborting, Relation.lcomp₁.union_lcomp₂]
      -- the walk emits this guard at `k`; both reorder lemmas state that index as `0 + k`
      refine Relation.lcomp₁.commute_step ?_ ?_ hmid le_rfl
      · simpa only [Nat.zero_add] using (reorder_pairs_lenGt pairs (n := 0)).symm
      · simpa only [Nat.zero_add] using reorder_pairs_lenGt_abort pairs (n := 0)

/-- **The adjacent ordering refines the source block.** One `StrongRefinement.Comp` per source
guard: `receiveGroup_refines` where the source received, and the two languages' `with`/`await`
semantics being literally the same relation where it did not.

This is the half of the walk that reasons about states, and it is stated only about the *adjacent*
ordering — never about the emitted one, whose intermediate states are not `relatesTo`-related.
`Walk.reorder` is what connects the two, and it is an equation precisely so that this half never has
to look at them.

Divergence is `∅` on both sides (`Statement.listDiverging'_eq_empty`), so
`StrongRefinement.Diverging.Empty` carries that component throughout and `Adjacent` need not record
it. The trace relation stays `Rτ` rather than growing with each composition: `Comp` produces
`Rτ ⊔ Rτ ⊗ᵣ Rτ`, which `Relation.MulClosed.sup_rmul_self` collapses. -/
private theorem Adjacent.refines {chans : Guarded2NetworkChans} {c₀ : ComputableGuardedPlusCal.Ref}
    {inbox : String} {Ss} {adj : Set (LocalState' V × Trace V × LocalState' V)}
    {adj' : Set (LocalState' V × Trace V)} (adjacent : Adjacent chans inbox Ss adj adj')
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss → c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : ∀ S ∈ Ss, Fresh (.some (c₀, inbox)) S) :
    StrongRefinement (relatesTo (V := V) (.some (c₀, inbox))) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.listReducing' Ss) (GuardedPlusCal.Statement.listAborting' Ss)
      (GuardedPlusCal.Statement.listDiverging' Ss) adj adj' ∅ := by
  -- one composition per source guard; `head` is what each step contributes, `IH` the rest
  have step : ∀ {S : ComputableGuardedPlusCal.Statement true false} {Ss'}
      {aS : Set (LocalState' V × Trace V × LocalState' V)} {aS' : Set (LocalState' V × Trace V)}
      {a : Set (LocalState' V × Trace V × LocalState' V)} {a' : Set (LocalState' V × Trace V)},
      StrongRefinement (relatesTo (V := V) (.some (c₀, inbox))) (instTrace (V := V)).Rτ
        (GuardedPlusCal.Statement.reducing' S) (GuardedPlusCal.Statement.aborting' S)
        (GuardedPlusCal.Statement.diverging' S) aS aS' ∅ →
      StrongRefinement (relatesTo (V := V) (.some (c₀, inbox))) (instTrace (V := V)).Rτ
        (GuardedPlusCal.Statement.listReducing' Ss') (GuardedPlusCal.Statement.listAborting' Ss')
        (GuardedPlusCal.Statement.listDiverging' Ss') a a' ∅ →
      StrongRefinement (relatesTo (V := V) (.some (c₀, inbox))) (instTrace (V := V)).Rτ
        (GuardedPlusCal.Statement.listReducing' (S :: Ss'))
        (GuardedPlusCal.Statement.listAborting' (S :: Ss'))
        (GuardedPlusCal.Statement.listDiverging' (S :: Ss'))
        (aS ∘ᵣ₂ a) (aS' ∪ aS ∘ᵣ₁ a') ∅ := by
    intro _ _ _ _ _ _ head tail
    have hcomp := StrongRefinement.Comp _ head tail
    simp only [GuardedPlusCal.Statement.diverging'_eq_empty,
      GuardedPlusCal.Statement.listDiverging'_eq_empty, Relation.lcomp₁.right_empty_eq_empty,
      Set.union_self] at hcomp
    rwa [GuardedPlusCal.Statement.listReducing'_cons, GuardedPlusCal.Statement.listAborting'_cons,
      GuardedPlusCal.Statement.listDiverging'_eq_empty]
  induction adjacent with
  | nil =>
    rw [GuardedPlusCal.Statement.listReducing'_nil, GuardedPlusCal.Statement.listAborting'_nil]
    exact StrongRefinement.ofNonDiverging _
      (StrongRefinement.Terminating.Id _)
      (StrongRefinement.Aborting.Empty _)
  | «with» _ IH =>
    rw [with_reducing'_eq, with_aborting'_eq]
    exact step (guard_refines _ (λ _ _ _ h ↦ nomatch h) (gfresh _ List.mem_cons_self))
      (IH (λ c r coe h ↦ rfresh c r coe (List.mem_cons_of_mem _ h))
        (λ S hS ↦ gfresh S (List.mem_cons_of_mem _ hS)))
  | await _ IH =>
    rw [await_reducing'_eq, await_aborting'_eq]
    exact step (guard_refines _ (λ _ _ _ h ↦ nomatch h) (gfresh _ List.mem_cons_self))
      (IH (λ c r coe h ↦ rfresh c r coe (List.mem_cons_of_mem _ h))
        (λ S hS ↦ gfresh S (List.mem_cons_of_mem _ hS)))
  | receive _ _ IH =>
    obtain ⟨rfl, hfr⟩ := rfresh _ _ _ List.mem_cons_self
    exact step (receiveGroup_refines hfr)
      (IH (λ c r coe h ↦ rfresh c r coe (List.mem_cons_of_mem _ h))
        (λ S hS ↦ gfresh S (List.mem_cons_of_mem _ hS)))

/-! ## The two halves joined

  `Walk.reorder` says the emitted target *is* the adjacent one; `Adjacent.refines` says the adjacent
  one refines the source. Composing them is `StrongRefinement.Mono`, which shrinks a target — which
  is why the aborting half only had to be an inclusion.

  Everything below is stated over `Block.reducing`/`.aborting`, the form the rest of the pass's proof
  meets, rather than over the flattened list the walk produces. `Block.reducing_eq_listReducing` is
  the only step that costs anything, and it is free: a block and its statement list are the same fold.
-/

/-- Every entry the walk accumulates comes from a `receive` it passed. What lets a freshness
condition stated about the *source* block cover the pass's own generated assignments, which no
source-level predicate can mention. -/
private theorem Walk.newInstrs_mem {chans : Guarded2NetworkChans} {inbox : String}
    {st st' : ReceiveState} {Ss res} (h : Walk chans inbox st Ss res st')
    {a : ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan}
    (ha : a ∈ st'.newInstrs) :
    a ∈ st.newInstrs ∨ ∃ c r coe τ pos, GuardedPlusCal.Statement.receive c r coe ∈ Ss ∧
      a ∈ receiveInstrs r coe inbox τ pos := by
  induction h with
  | nil => exact .inl ha
  | «with» _ IH | await _ IH =>
    rcases IH ha with h' | ⟨c, r, coe, τ, pos, hmem, ha'⟩
    · exact .inl h'
    · exact .inr ⟨c, r, coe, τ, pos, List.mem_cons_of_mem _ hmem, ha'⟩
  | receive _ _ IH =>
    rcases IH ha with h' | ⟨c, r, coe, τ, pos, hmem, ha'⟩
    · rcases List.mem_append.mp h' with h'' | h''
      · exact .inl h''
      · exact .inr ⟨_, _, _, _, _, List.mem_cons_self, h''⟩
    · exact .inr ⟨c, r, coe, τ, pos, List.mem_cons_of_mem _ hmem, ha'⟩

/-- `PairsFresh` in the form the reorder lemmas take it, for a walk starting from the initial state:
nothing is pending there, so every accumulated pair came from a `receive` in the block. -/
private theorem PairsFresh.ofWalk {chans : Guarded2NetworkChans} {inbox : String} {st' : ReceiveState}
    {Ss res} (walk : Walk chans inbox {} Ss res st') (pfresh : PairsFresh inbox Ss) :
    ∀ a ∈ st'.newInstrs, ∀ x ann bound e,
      GuardedPlusCal.Statement.with x ann bound e ∈ Ss →
        x ∉ GuardedPlusCal.Ref.freeVars a.1 ∧ Expression.FreshIn x a.2.1 := by
  intro a ha x ann bound e hwith
  rcases walk.newInstrs_mem ha with h | ⟨c, r, coe, τ, pos, hrecv, ha'⟩
  · nomatch h
  · exact pfresh x ann bound e hwith c r coe hrecv τ pos a ha'

/-- **`rfresh` assembled from its two sources.** The receive half comes from well-formedness, where
`WellFormedness/Restrictions.lean`'s executable checks put it; the two conditions on the *generated*
`inbox` come from whoever generated it, which is `Thread.toNetwork` (plan step D8) and not this
file.

The split is deliberate and follows the shape of the problem: one half is a property of the source
program that a front-end pass rejects, the other is a property of a name this pass invents. Nothing
in `Algorithm.WellScoped` could establish the second — `inbox` does not occur in the source at
all. -/
theorem rfresh_of_wellFormed {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
    {Ss : List (ComputableGuardedPlusCal.Statement true false)}
    (recv : GuardedPlusCal.PreconditionReceives c₀ Ss)
    (hinbox : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss →
        inbox ∉ GuardedPlusCal.Ref.freeVars c ∧ inbox ∉ GuardedPlusCal.Ref.freeVars r) :
    ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss → c = c₀ ∧ ReceiveFresh c r inbox :=
  λ c r coe hmem ↦
    ⟨recv.one_channel c r coe hmem, (hinbox c r coe hmem).1, (hinbox c r coe hmem).2,
      recv.target_not_in_channel c r coe hmem⟩

/-- **A compiled precondition block refines the source one.** The pass's two outputs read together:
the rewritten block `B'`, and the consumption assignments it hoisted out to be run after it.

The proof is the two halves of the walk composed. `Walk.reorder` turns the emitted ordering into the
adjacent one — an equation, so the reducing component transfers exactly — and `Walk.reorder_aborting`
does the aborting one as an inclusion, which is the direction `StrongRefinement.Mono` accepts.
`Adjacent.refines` supplies the refinement itself. Nothing here reasons about states; that all
happened in `Adjacent.refines`, over an ordering whose intermediate states are `relatesTo`-related. -/
private theorem processPrecondition_refines {chans : Guarded2NetworkChans}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
    {B : GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement true) false}
    {B' : GuardedPlusCal.Block (ComputableNetworkPlusCal.Statement true) false}
    {assigns : List (ComputableNetworkPlusCal.Statement false false)}
    {rxs : List (ComputableGuardedPlusCal.Ref × ComputableTLAPlus.Typ)} {n n' : Nat}
    (h : ((processPrecondition (m := G2NM) chans inbox (.some B)).run.run n) =
      (.ok (.some B', assigns, rxs), n'))
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ B.toList → c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : ∀ S ∈ B.toList, Fresh (.some (c₀, inbox)) S)
    (pfresh : PairsFresh inbox B.toList) :
    StrongRefinement (relatesTo (V := V) (.some (c₀, inbox))) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Block.reducing (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing') B)
      (GuardedPlusCal.Block.aborting (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.aborting')
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing') B)
      (GuardedPlusCal.Block.diverging (β := λ _ ↦ LocalState' V)
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.diverging')
        (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing') B)
      (GuardedPlusCal.Block.reducing (β := λ _ ↦ LocalState' V)
          (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing') B' ∘ᵣ₂
        NetworkPlusCal.Statement.listReducing' assigns)
      (GuardedPlusCal.Block.aborting (β := λ _ ↦ LocalState' V)
          (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.aborting')
          (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing') B' ∪
        GuardedPlusCal.Block.reducing (β := λ _ ↦ LocalState' V)
            (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing') B' ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting' assigns)
      ∅ := by
  obtain ⟨st, walk, rfl, -⟩ := processPrecondition_walk h
  obtain ⟨adj, adj', adjacent⟩ := walk.adjacent (V := V)
  have rn : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ B.toList → r.name ≠ inbox :=
    λ c r coe hmem ↦ (ne_name_of_fresh (rfresh c r coe hmem).2.2.1).symm
  have hred := walk.reorder adjacent .nil rn (PairsFresh.ofWalk walk pfresh)
  have habt := walk.reorder_aborting adjacent .nil rn (PairsFresh.ofWalk walk pfresh)
  rw [consumptions_nil, NetworkPlusCal.Statement.listReducing'_nil,
    Relation.lcomp₂.left_id_eq] at hred
  rw [consumptions_nil, NetworkPlusCal.Statement.listAborting'_nil,
    NetworkPlusCal.Statement.listReducing'_nil, Relation.lcomp₁.left_id_eq,
    Set.empty_union] at habt
  rw [GuardedPlusCal.Block.reducing_eq_listReducing, GuardedPlusCal.Block.aborting_eq_listAborting,
    GuardedPlusCal.Block.diverging_eq_listAborting,
    GuardedPlusCal.Block.reducing_eq_listReducing (B := B'),
    GuardedPlusCal.Block.aborting_eq_listAborting (B := B')]
  exact StrongRefinement.Mono le_rfl le_rfl le_rfl (le_of_eq hred.symm) habt le_rfl
    (adjacent.refines rfresh gfresh)

open Std.Do in
private theorem processPrecondition_spec {chans : Guarded2NetworkChans}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
    {B : GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement true) false}
    {B' : GuardedPlusCal.Block (ComputableNetworkPlusCal.Statement true) false}
    {assigns : List (ComputableNetworkPlusCal.Statement false false)}
    {rxs : List (ComputableGuardedPlusCal.Ref × ComputableTLAPlus.Typ)} {n n' : Nat}
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ B.toList → c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : ∀ S ∈ B.toList, Fresh (.some (c₀, inbox)) S)
    (pfresh : PairsFresh inbox B.toList) :
    ⦃λ n₀ ↦ ⌜n₀ = n⌝⦄
    processPrecondition (m := G2NM) chans inbox (.some B)
    ⦃⇓? (B', assigns, rxs) n' => match B' with
      | .none => ⌜False⌝
      | .some B' => ⌜StrongRefinement (relatesTo (V := V) (.some (c₀, inbox))) (instTrace (V := V)).Rτ
        (GuardedPlusCal.Block.reducing (β := λ _ ↦ LocalState' V)
          (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing') B)
        (GuardedPlusCal.Block.aborting (β := λ _ ↦ LocalState' V)
          (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.aborting')
          (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing') B)
        (GuardedPlusCal.Block.diverging (β := λ _ ↦ LocalState' V)
          (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.diverging')
          (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing') B)
        (GuardedPlusCal.Block.reducing (β := λ _ ↦ LocalState' V)
            (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing') B' ∘ᵣ₂
          NetworkPlusCal.Statement.listReducing' assigns)
        (GuardedPlusCal.Block.aborting (β := λ _ ↦ LocalState' V)
            (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.aborting')
            (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing') B' ∪
          GuardedPlusCal.Block.reducing (β := λ _ ↦ LocalState' V)
              (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing') B' ∘ᵣ₁
            NetworkPlusCal.Statement.listAborting' assigns)
        ∅⌝⦄ := by
    mvcgen [processPrecondition]
    mspec (mapM_stepStatement_refines_run (V := V) (c₀ := c₀) rfresh gfresh pfresh)
    case vc1.success s hs r =>
      mspec Std.Do.Spec.pure
      mrename_i hinv
      mpure hinv
      mpure_intro
      obtain ⟨⟨pairs, hlen, ref⟩, -⟩ := hinv
      -- `dropLast`/`getLast!` put the block back together only because the walk emitted one
      -- statement per source statement, and a `Block` is non-empty by construction
      have hne : r.1 ≠ [] := by
        rw [← List.length_pos_iff, hlen, List.length_concat]
        omega
      simpa only [GuardedPlusCal.Block.reducing_eq_listReducing,
        GuardedPlusCal.Block.aborting_eq_listAborting,
        GuardedPlusCal.Block.diverging'_eq_empty, GuardedPlusCal.Block.toList,
        List.dropLast_concat_getLast! hne]

end Guarded2Network

end
