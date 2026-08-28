module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Monad
public import Guarded2Network.Lemmas.Reorder
public import Guarded2Network.Lemmas.Locality
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
  assignments sit immediately after its `await`. The reorder lemmas turn that ordering into the
  emitted one, and the walk applies them one step at a time — the pair a `receive` contributes is
  moved past the following guards by the very steps that compile those guards, so no two orderings
  of a whole block are ever related.

  **Index versus substitution.** In the emitted ordering the k-th `receive`'s guard is
  `Len(inbox) > k`, because no assignment has run yet and the inbox still holds every pending
  message. In the adjacent ordering the k preceding pairs have already run, the inbox has been
  tailed k times, and the guard is `Len(inbox) > 0`. The two say the same thing, but no
  *substitution* relates them — this pass emits no offset for `substGuards` to grow — so the bridge
  is the semantic `reorder_consumption_lenGt` below instead.

  The last section is the walk itself, as a chain of Hoare triples: `stepStatement_spec` carries the
  refinement-so-far in the state, `Spec.mapM_list` iterates it over the block, and
  `processPrecondition_spec` reads the block back off the result.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Expression Memory PathStep OperatorEnv Model)
open GuardedPlusCal (ChanKey EvalStep FIFOs LocalState LocalState Trace)

variable {V : Type} [ExprSemantics V] [SeqBuiltins V] {Ξ : OperatorEnv} {Ω : Model V}

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
    {F : FIFOs V} {sv : V} {vs : List V} {σ' : LocalState V} {ε : Trace V}
    (hlk : M.lookup inbox = .some sv) (hseq : ExprSemantics.isSeq sv vs) :
    (⟨(M, F, .none), ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
        NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ (inboxVar inbox τ) n)) ↔
      σ' = (M, F, .none) ∧ ε = 1 ∧ n < vs.length := by
  obtain ⟨b, hb, -, hiff⟩ := eval_lenGt_inbox (Ξ := Ξ) (Ω := Ω) (τ := τ) (n := n) hlk hseq
  iff_rintro h ⟨rfl, rfl, hlen⟩
  · obtain ⟨M', F', hσ, rfl, htru, rfl⟩ := h
    simp only [Prod.mk.injEq] at hσ
    obtain ⟨rfl, rfl, -⟩ := hσ
    obtain rfl := ExprSemantics.evalUnique hb htru
    exact ⟨rfl, rfl, hiff.mp rfl⟩
  · obtain rfl := hiff.mpr hlen
    exact NetworkPlusCal.Statement.reducing.await.intro ⟨M, F, rfl, rfl, hb, rfl⟩

/-- The compiled guard's *blocked* step: it is blocked exactly when the inbox holds no more than `n`
elements. `await_lenGt_iff`'s companion — one is the guard firing, the other its blocking. -/
theorem await_lenGt_blocking_iff {inbox : String} {τ : ComputableTLAPlus.Typ} {n : Nat}
    {M : Memory V} {F : FIFOs V} {sv : V} {vs : List V} {ε : Trace V}
    (hlk : M.lookup inbox = .some sv) (hseq : ExprSemantics.isSeq sv vs) :
    (⟨(M, F, .none), ε⟩ : LocalState V × Trace V) ∈
        NetworkPlusCal.Statement.blocking Ξ Ω (.await (lenGt τ (inboxVar inbox τ) n)) ↔
      ε = 1 ∧ vs.length ≤ n := by
  obtain ⟨b, hb, hbool, hiff⟩ := eval_lenGt_inbox (Ξ := Ξ) (Ω := Ω) (τ := τ) (n := n) hlk hseq
  iff_rintro h ⟨rfl, hlen⟩
  · obtain ⟨M', F', v, hbool', hne, hv, hσ, rfl⟩ := h
    simp only [Prod.mk.injEq] at hσ
    obtain ⟨rfl, rfl, -⟩ := hσ
    obtain rfl := ExprSemantics.evalUnique hv hb
    refine ⟨rfl, ?_⟩
    by_contra hlt
    exact hne (hiff.mpr (by omega))
  · refine ⟨M, F, b, hbool, ?_, hb, rfl, rfl⟩
    intro heq
    exact (Nat.not_lt.mpr hlen) (hiff.mp heq)

/-- One `receive`'s two consumption assignments, as a single step: the inbox must hold at least one
element, the coerced head lands under the reference, and the tail is written back. Note what the pair
does *not* need — nothing about `r`'s index path relative to `inbox`, since both orderings evaluate
the assignments at exactly the same two memories. Only `r.name ≠ inbox` matters, and only so that the
first assignment leaves the inbox for the second to read. -/
theorem consumption_pair_iff {r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ : ComputableTLAPlus.Typ} (hne : r.name ≠ inbox)
    {σ σ' : LocalState V} {ε : Trace V} :
    (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
        NetworkPlusCal.Statement.reducing Ξ Ω
            (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
          NetworkPlusCal.Statement.reducing Ξ Ω
            (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))) ↔
      ∃ M F M' sv t v v' vs rpath,
        σ = (M, F, .none) ∧ σ' = (M'.insert inbox t, F, .none) ∧ ε = 1 ∧
        M.lookup inbox = .some sv ∧ ExprSemantics.isSeq sv (v :: vs) ∧
        ExprSemantics.isSeq t vs ∧ ExprSemantics.coerce coe v v' ∧ Ref.EvalArgs Ξ Ω M r rpath ∧
        ComputableTLAPlus.Memory.update M r.name rpath v' = .some M' := by
  iff_rintro ⟨mid, ε₁, ε₂, hR, hI, rfl⟩
    ⟨M, F, M', sv, t, v, v', vs, rpath, rfl, rfl, rfl, hsv, hseq, ht, hcoe, hrpath, hupd⟩
  · obtain ⟨M₁, F₁, M', v', rpath, hv', hrpath, hupd, rfl, rfl, rfl⟩ := hR
    obtain ⟨M, F, M₄, t, ipath, htail, hipath, hupdI, hσ, rfl, rfl⟩ := hI
    simp only [Prod.mk.injEq] at hσ
    obtain ⟨rfl, rfl, -⟩ := hσ
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
    refine ⟨(M', F, .none), 1, 1,
      NetworkPlusCal.Statement.reducing.assign.intro
        ⟨M, F, M', v', rpath, ExprSemantics.evalCoerce.mpr
          ⟨v, (eval_head_inbox hsv hseq).mpr rfl, hcoe⟩, hrpath, hupd, rfl, rfl, rfl⟩,
      NetworkPlusCal.Statement.reducing.assign.intro
        ⟨M', F, M'.insert inbox t, t, [], (eval_tail_inbox hsv' hseq).mpr ht, .nil, ?_,
          rfl, rfl, rfl⟩,
      by simp⟩
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
    {inbox : String} {τ : ComputableTLAPlus.Typ} {pref : ChanKey V → List V}
    (fresh : ReceiveFresh c r inbox) {σₛ σₜ σₜ' : LocalState V} {ε : Trace V}
    (sim : σₛ ∼[Ξ, Ω,.some (c, inbox), pref] σₜ)
    (step : (⟨σₜ, ε, σₜ'⟩ : LocalState V × Trace V × LocalState V) ∈
      NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₂
      NetworkPlusCal.Statement.reducing Ξ Ω
        (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
      NetworkPlusCal.Statement.reducing Ξ Ω (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ)))) :
    ε = 1 ∧
      ((∃ σₛ', σₛ' ∼[Ξ, Ω,.some (c, inbox), pref] σₜ' ∧
        (⟨σₛ, 1, σₛ'⟩ : LocalState V × Trace V × LocalState V) ∈
          GuardedPlusCal.Statement.reducing Ξ Ω (.receive c r coe)) ∨
      (⟨σₛ, 1⟩ : LocalState V × Trace V) ∈
        GuardedPlusCal.Statement.aborting Ξ Ω (.receive c r coe)) := by
  obtain ⟨hfc, hfr, hfw⟩ := fresh
  have hrname : r.name ≠ inbox := Ne.symm (ne_name_of_fresh hfr)
  obtain ⟨cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩ := sim.inbox_seq
  have hagree := sim.mem_agree
  have hlabel := sim.label_eq
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  simp only [LocalState.mem_mk, LocalState.fifos_mk, LocalState.label_mk]
    at hpath hinbox hoff hsplit hagree hlabel
  -- the target's three steps
  obtain ⟨mid1, ε₁, ε₂, hawait, ⟨mid2, ε₃, ε₄, hassignR, hassignI, rfl⟩, rfl⟩ := step
  obtain ⟨M, F, rfl, rfl, htru, rfl⟩ := hawait
  erw [LocalState.label_mk] at hlabel
  subst hlabel
  obtain ⟨M₀, F₀, M₃, v', rpath, hv', hrpath, hupd, hσ, rfl, rfl⟩ := hassignR
  simp only [Prod.mk.injEq] at hσ
  obtain ⟨rfl, rfl, -⟩ := hσ
  obtain ⟨M₁', F₁', M₄', t, ipath, ht, hipath, hupdI, hσ, rfl, rfl⟩ := hassignI
  simp only [Prod.mk.injEq] at hσ
  obtain ⟨rfl, rfl, -⟩ := hσ
  refine ⟨by simp, ?_⟩
  -- the guard says the inbox is non-empty, so the drained prefix has a head
  obtain ⟨b, hb, -, hiff⟩ := eval_lenGt_inbox (Ξ := Ξ) (Ω := Ω) (τ := τ) (n := 0) hinbox hseq
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
  cases hlk : F.lookup ((c.name, cpath) : ChanKey V) with
  | none =>
    -- the invariant permits an `inbox` holding messages over a channel the source has no FIFO for
    -- at all; there the source aborts rather than matching
    refine .inr (GuardedPlusCal.Statement.aborting.receive.intro
      (.inl (.inl (.inr ⟨M₁, F₁, cpath, rfl, rfl, hpath, ?_⟩))))
    erw [LocalState.fifos_mk] at hsplit
    rw [hsplit, hlk]
    rfl
  | some ws =>
    have hlk₁ : F₁.lookup ((c.name, cpath) : ChanKey V) = .some (v :: (vs' ++ ws)) := by
      erw [LocalState.fifos_mk] at hsplit
      rw [hsplit, hlk]
      rfl
    obtain ⟨M₁', hupd₁, hx⟩ := Memory.update_transfer (hagree r.name hrname).symm hupd
    -- the same write in both memories: at the name written they agree by `hx`, elsewhere neither
    -- memory moved
    have hagree₁ : ∀ y ≠ inbox, M₁'.lookup y = M₃.lookup y := by
      intro y hy
      by_cases hyr : y = r.name
      · subst hyr
        exact hx.symm
      · rw [Memory.lookup_update_ne hupd₁ hyr, Memory.lookup_update_ne hupd hyr]
        exact hagree y hy
    refine .inl ⟨⟨M₁', F₁.insert (c.name, cpath) (vs' ++ ws), .none⟩,
      relatesTo.chan_intro (cpath := cpath) rfl ?_ ?_ (Finmap.lookup_insert _) ht' ?_ ?_,
      GuardedPlusCal.Statement.reducing.receive.intro
        ⟨M₁, F₁, M₁', cpath, rpath, v, v', vs' ++ ws, hpath,
          (Ref.EvalArgs.congr_of_fresh hagree hfr).mpr hrpath, hlk₁, hcoe, hupd₁,
          rfl, rfl, rfl⟩⟩
    · intro y hy
      dsimp only [LocalState.mem_mk]
      rw [Finmap.lookup_insert_of_ne _ hy]
      exact hagree₁ y hy
    · exact (Ref.EvalArgs.congr_of_fresh
        (λ y hy ↦ (Memory.lookup_update_ne hupd₁ hy).symm) hfw).mp hpath
    · intro k hk
      dsimp only [LocalState.fifos_mk]
      rw [Finmap.lookup_insert_of_ne _ hk]
      exact hoff k hk
    · dsimp only [LocalState.fifos_mk]
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
    {inbox : String} {τ : ComputableTLAPlus.Typ} {pref : ChanKey V → List V}
    (fresh : ReceiveFresh c r inbox) {σₛ σₜ : LocalState V} {ε : Trace V}
    (sim : σₛ ∼[Ξ, Ω,.some (c, inbox), pref] σₜ)
    (step : (⟨σₜ, ε⟩ : LocalState V × Trace V) ∈
      NetworkPlusCal.Statement.aborting Ξ Ω (.await (lenGt τ (inboxVar inbox τ) 0)) ∪
      NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₁
        (NetworkPlusCal.Statement.aborting Ξ Ω
            (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∪
          NetworkPlusCal.Statement.reducing Ξ Ω
              (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₁
            NetworkPlusCal.Statement.aborting Ξ Ω
              (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))))) :
    (⟨σₛ, 1⟩ : LocalState V × Trace V) ∈
      GuardedPlusCal.Statement.aborting Ξ Ω (.receive c r coe) := by
  obtain ⟨hfc, hfr, hfw⟩ := fresh
  have hrname : r.name ≠ inbox := Ne.symm (ne_name_of_fresh hfr)
  obtain ⟨cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩ := sim.inbox_seq
  have hagree := sim.mem_agree
  have hlabel := sim.label_eq
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  simp only [LocalState.mem_mk, LocalState.fifos_mk, LocalState.label_mk]
    at hpath hinbox hoff hsplit hagree hlabel
  obtain ⟨b, hb, hbool, hiff⟩ := eval_lenGt_inbox (Ξ := Ξ) (Ω := Ω) (τ := τ) (n := 0) hinbox hseq
  rcases step with hab | ⟨mid, ε₁, ε₂, hred, hrest, -⟩
  · -- the guard has a value and is a boolean, so neither `await` abort clause is reachable
    rcases hab with ⟨M, F, habort, rfl, -⟩ | ⟨M, F, w, hw, hwv, rfl, -⟩
    · have hex : ∃ u, ExprSemantics.Eval Ξ Ω M (lenGt τ (inboxVar inbox τ) 0) u := ⟨b, hb⟩
      absurd hex
      exact habort
    · obtain rfl := ExprSemantics.evalUnique hb hwv
      absurd hbool
      exact hw
  · -- the guard held, so the drained prefix has a head
    obtain ⟨M, F, rfl, rfl, htru, -⟩ := hred
    simp only [LocalState.label_mk] at hlabel
    subst hlabel
    obtain rfl := ExprSemantics.evalUnique hb htru
    obtain ⟨v, vs', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (hiff.mp rfl))
    -- the source's queue may be absent altogether, and then the source aborts on the channel itself
    have habsent : F.lookup ((c.name, cpath) : ChanKey V) = .none →
        (⟨(M₁, F₁, .none), (1 : Trace V)⟩ : LocalState V × Trace V) ∈
          GuardedPlusCal.Statement.aborting Ξ Ω (.receive c r coe) := by
      intro hlk
      refine GuardedPlusCal.Statement.aborting.receive.intro
        (.inl (.inl (.inr ⟨M₁, F₁, cpath, rfl, rfl, hpath, ?_⟩)))
      erw [LocalState.fifos_mk] at hsplit
      rw [hsplit, hlk]
      rfl
    rcases hrest with hab | ⟨mid2, ε₃, ε₄, hredR, habI, -⟩
    · obtain ⟨M, F, hM, rfl, hd⟩ := NetworkPlusCal.Statement.aborting.assign.iff.mp hab
      simp only [Prod.mk.injEq] at hM
      obtain ⟨rfl, rfl, -⟩ := hM
      rcases hd with hname | habort | hrp | ⟨v', rpath, hv', hrpath, hupd⟩
      · -- the assignment's target is unbound in the target, so it is in the source too
        refine GuardedPlusCal.Statement.aborting.receive.intro
          (.inl (.inl (.inl (.inl (.inl ⟨M₁, F₁, ?_, rfl, rfl⟩)))))
        rw [← Finmap.lookup_eq_none, hagree r.name hrname, Finmap.lookup_eq_none]
        exact hname
      · -- `Head` has a value, so what fails is the coercion
        cases hlk : F.lookup ((c.name, cpath) : ChanKey V) with
        | none => exact habsent hlk
        | some ws =>
          refine GuardedPlusCal.Statement.aborting.receive.intro
            (.inl (.inr ⟨M₁, F₁, cpath, v, vs' ++ ws, rfl, rfl, hpath, ?_, ?_⟩))
          · erw [LocalState.fifos_mk] at hsplit
            rw [hsplit, hlk]
            rfl
          · rintro ⟨v', hv'⟩
            exact habort ⟨v', ExprSemantics.evalCoerce.mpr
              ⟨v, (eval_head_inbox hinbox hseq).mpr rfl, hv'⟩⟩
      · -- the assignment's reference does not resolve, and it reads no name the two memories differ on
        exact GuardedPlusCal.Statement.aborting.receive.intro
          (.inl (.inl (.inl (.inr ⟨M₁, F₁, rfl, rfl, (pathAborts_congr hagree hfr).mpr hrp⟩))))
      · -- the update itself fails, at a value the source computes the same way
        obtain ⟨w, hw, hcoe⟩ := ExprSemantics.evalCoerce.mp hv'
        obtain rfl := ((eval_head_inbox hinbox hseq).mp hw).symm
        cases hlk : F.lookup ((c.name, cpath) : ChanKey V) with
        | none => exact habsent hlk
        | some ws =>
          refine GuardedPlusCal.Statement.aborting.receive.intro
            (.inr ⟨M₁, F₁, cpath, rpath, v, v', vs' ++ ws, rfl, rfl, hpath,
              (Ref.EvalArgs.congr_of_fresh hagree hfr).mpr hrpath, ?_, hcoe, ?_⟩)
          · erw [LocalState.fifos_mk] at hsplit
            rw [hsplit, hlk]
            rfl
          · exact Memory.update_none_transfer (hagree r.name hrname) hupd
    · -- the second assignment cannot abort: `inbox` is bound, `Tail` has a value, and an empty-path
      -- update cannot fail
      obtain ⟨M, F, M₃, v', rpath, -, -, hupd, hσ, rfl, -⟩ := hredR
      simp only [Prod.mk.injEq] at hσ
      obtain ⟨rfl, rfl, -⟩ := hσ
      have hinbox₃ : M₃.lookup inbox = .some sv :=
        (Memory.lookup_update_ne hupd (Ne.symm hrname)).trans hinbox
      obtain ⟨M, F, hM, rfl, hd⟩ := NetworkPlusCal.Statement.aborting.assign.iff.mp habI
      simp only [Prod.mk.injEq] at hM
      obtain ⟨rfl, rfl, -⟩ := hM
      obtain ⟨t, ht'⟩ := ExprSemantics.isSeq_tail hseq
      rcases hd with hname | habort | hrp | ⟨u, ipath, -, hipath, hupdI⟩
      · rw [inboxRef_name, ← Finmap.lookup_eq_none, hinbox₃] at hname
        contradiction
      · have hex : ∃ u, ExprSemantics.Eval Ξ Ω M₃ (tail τ (inboxVar inbox τ)) u :=
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

/-- **The blocked half.** A target `Len(inbox) > 0` that blocks — the inbox is empty — is matched by
the source's `receive` blocking, *provided the mailbox channel is drained too*: the invariant gives
`F_s(c) = inbox ++ F_t(c)`, and with `inbox` empty and `F_t(c)` empty the source queue is empty,
which is exactly when `receive` blocks. `hdrain` is what the algorithm level supplies from
`relayBlocking`; here it is a hypothesis at the path the invariant resolves the channel to. -/
theorem receive_blocking_sim {c r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ : ComputableTLAPlus.Typ} {pref : ChanKey V → List V}
    {σₛ σₜ : LocalState V} {ε : Trace V}
    (sim : σₛ ∼[Ξ, Ω,.some (c, inbox), pref] σₜ)
    (hdrain : ∀ cpath, List.Forall₂ (EvalStep Ξ Ω σₛ.mem) c.args cpath →
      σₜ.fifos.lookup ⟨c.name, cpath⟩ = .some [])
    (step : (⟨σₜ, ε⟩ : LocalState V × Trace V) ∈
      NetworkPlusCal.Statement.blocking Ξ Ω (.await (lenGt τ (inboxVar inbox τ) 0))) :
    (⟨σₛ, ε⟩ : LocalState V × Trace V) ∈
      GuardedPlusCal.Statement.blocking Ξ Ω (.receive c r coe) := by
  obtain ⟨cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩ := sim.inbox_seq
  have hlabel := sim.label_eq
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  obtain ⟨M₂, F₂, l₂⟩ := σₜ
  simp only [LocalState.mem_mk, LocalState.fifos_mk, LocalState.label_mk] at *
  obtain ⟨M, F, b, hbool, hbne, hbeval, hσ, rfl⟩ := step
  simp only [Prod.mk.injEq] at hσ
  obtain ⟨rfl, rfl, rfl⟩ := hσ
  subst hlabel
  -- the guard blocks, so the inbox holds `0` or fewer elements
  obtain ⟨b', hb', -, hiff⟩ := eval_lenGt_inbox (Ξ := Ξ) (Ω := Ω) (τ := τ) (n := 0) hinbox hseq
  obtain rfl := ExprSemantics.evalUnique hbeval hb'
  obtain rfl : vs = [] := by
    rcases List.eq_nil_or_concat vs with rfl | ⟨ys, y, rfl⟩
    · rfl
    · exact (hbne (hiff.mpr (by simp))).elim
  -- so `F_s(c) = ([] ++ ·) <$> F_t(c) = F_t(c)`, and `F_t(c)` is drained
  simp only [hdrain cpath hpath, List.nil_append] at hsplit
  exact ⟨M₁, F₁, cpath, hpath, hsplit, rfl, rfl⟩

/-- **The `receive` elimination**, in the framework's own terms: one source `receive` refines the
group it compiles to — the inbox-length guard, then the two consumption assignments — at this pass's
trace relation. Still the adjacent ordering; `reorder_assigns_guard` is what moves the assignments to
where the pass actually emits them.

`terminating` is `receive_reducing_sim`, `aborting` is `receive_aborting_sim` with the `≼[Rτ]`
obligation trivial (an abort emits nothing, and the empty trace is a prefix of everything), and
`diverging` is vacuous: no statement diverges, so the target composite is empty and the framework
supplies that component itself. -/
theorem receive_refines {c r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ : ComputableTLAPlus.Typ} {pref : ChanKey V → List V}
    (fresh : ReceiveFresh c r inbox) :
    StrongRefinement (relatesTo (V := V) Ξ Ω (.some (c, inbox)) pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.reducing Ξ Ω (.receive c r coe))
      (GuardedPlusCal.Statement.aborting Ξ Ω (.receive c r coe))
      (GuardedPlusCal.Statement.diverging (.receive c r coe))
      (NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing Ξ Ω
          (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing Ξ Ω (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))))
      (NetworkPlusCal.Statement.aborting Ξ Ω (.await (lenGt τ (inboxVar inbox τ) 0)) ∪
        NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₁
          (NetworkPlusCal.Statement.aborting Ξ Ω
              (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∪
            NetworkPlusCal.Statement.reducing Ξ Ω
                (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₁
              NetworkPlusCal.Statement.aborting Ξ Ω
                (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ)))))
      ∅ ∅ ∅ := by
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
    (NetworkPlusCal.Statement.reducing (V := V) Ξ Ω
          (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing Ξ Ω
          (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ)))) ∘ᵣ₂
      NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') n)) =
    NetworkPlusCal.Statement.reducing (V := V) Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') (n + 1))) ∘ᵣ₂
      (NetworkPlusCal.Statement.reducing Ξ Ω
          (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing Ξ Ω
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
    obtain ⟨Mb, Fb, rfl, hσm, htru, rfl⟩ := hguard
    simp only [Prod.mk.injEq] at hσm
    obtain ⟨rfl, rfl, -⟩ := hσm
    obtain ⟨b, hb, -, hiff⟩ := eval_lenGt_inbox (Ξ := Ξ) (Ω := Ω) (τ := τ') (n := n + 1) hsv hseq
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
    NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') n)) ≤
      NetworkPlusCal.Statement.aborting (V := V) Ξ Ω
        (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) := by
  rintro ⟨⟨M, F, l⟩, ε⟩ hguard
  obtain ⟨M₀, F₀, hM, rfl, hd⟩ := NetworkPlusCal.Statement.aborting.await.iff.mp hguard
  simp only [Prod.mk.injEq] at hM
  obtain ⟨rfl, rfl, rfl⟩ := hM
  refine NetworkPlusCal.Statement.aborting.assign.iff.mpr
    ⟨_, _, rfl, rfl, .inr (.inl ?_)⟩
  rintro ⟨v', hv'⟩
  obtain ⟨v, hv, -⟩ := ExprSemantics.evalCoerce.mp hv'
  obtain ⟨s, vs, hs, hseq⟩ := SeqBuiltins.evalHead.mp hv
  obtain ⟨b, hb, hbool, -⟩ :=
    eval_lenGt_inbox (Ξ := Ξ) (Ω := Ω) (τ := τ') (n := n) (ExprSemantics.evalVar.mp hs) hseq
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
    NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') (n + 1))) ∪
        NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') (n + 1))) ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting Ξ Ω
            [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
              .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] ≤
      NetworkPlusCal.Statement.listAborting (V := V) Ξ Ω
          [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
            .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] ∪
        NetworkPlusCal.Statement.listReducing Ξ Ω
            [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
              .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] ∘ᵣ₁
          NetworkPlusCal.Statement.aborting Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') n)) := by
  refine le_trans (Set.union_subset ?_ ?_) Set.subset_union_left
  · rw [NetworkPlusCal.Statement.listAborting_cons]
    exact le_trans await_lenGt_aborting_le Set.subset_union_left
  · exact Relation.lcomp₁.le_of_left_le_idle NetworkPlusCal.Statement.reducing_await_le_idle

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
    NetworkPlusCal.Statement.listReducing (V := V) Ξ Ω (consumptions A) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') n)) =
      NetworkPlusCal.Statement.reducing (V := V) Ξ Ω
          (.await (lenGt τ' (inboxVar inbox τ') (n + k))) ∘ᵣ₂
        NetworkPlusCal.Statement.listReducing Ξ Ω (consumptions A) := by
  induction h generalizing n with
  | nil =>
    rw [consumptions_nil, NetworkPlusCal.Statement.listReducing_nil, Nat.add_zero,
      Relation.lcomp₂.left_id_eq, Relation.lcomp₂.right_id_eq]
  | snoc _ hne IH =>
    rw [consumptions_append, NetworkPlusCal.Statement.listReducing_append,
      consumptions_receiveInstrs, NetworkPlusCal.Statement.listReducing_cons,
      NetworkPlusCal.Statement.listReducing_cons, NetworkPlusCal.Statement.listReducing_nil,
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
    NetworkPlusCal.Statement.aborting (V := V) Ξ Ω
          (.await (lenGt τ' (inboxVar inbox τ') (n + k))) ∪
        NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') (n + k))) ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting Ξ Ω (consumptions A) ≤
      NetworkPlusCal.Statement.listAborting (V := V) Ξ Ω (consumptions A) ∪
        NetworkPlusCal.Statement.listReducing Ξ Ω (consumptions A) ∘ᵣ₁
          NetworkPlusCal.Statement.aborting Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') n)) := by
  induction h generalizing n with
  | nil =>
    rw [consumptions_nil, NetworkPlusCal.Statement.listAborting_nil,
      NetworkPlusCal.Statement.listReducing_nil, Relation.lcomp₁.right_empty_eq_empty,
      Relation.lcomp₁.left_id_eq, Set.union_empty, Set.empty_union, Nat.add_zero]
  | snoc pairs _ IH =>
    rw [consumptions_append, NetworkPlusCal.Statement.listAborting_append,
      NetworkPlusCal.Statement.listReducing_append, Relation.lcomp₁.union_lcomp₂,
      consumptions_receiveInstrs, ← Nat.add_assoc, Nat.add_right_comm]
    exact Relation.lcomp₁.commute_step (reorder_pairs_lenGt pairs).symm IH le_rfl
      reorder_consumption_lenGt_abort

/-- **One consumption pair past a compiled guard, for the runs that block.**
`reorder_consumption_lenGt`'s blocking twin — the guard's index drops one across the pair, since the
pair removes one element from the inbox. Unlike the aborting twin the guard is *not* a no-op here: it
really moves from `Len(inbox) > n + 1` to `Len(inbox) > n`. The pair supplies the sequence fact
(`Head(inbox)` has a value only when the inbox is a non-empty sequence), so no separate hypothesis
about the inbox is needed. -/
theorem reorder_consumption_lenGt_block {r : ComputableGuardedPlusCal.Ref}
    {coe : TypedTLAPlus.Coercion} {inbox : String} {τ τ' : ComputableTLAPlus.Typ} {n : Nat}
    (hne : r.name ≠ inbox) :
    NetworkPlusCal.Statement.blocking (V := V) Ξ Ω
          (.await (lenGt τ' (inboxVar inbox τ') (n + 1))) ∪
        NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') (n + 1))) ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting Ξ Ω
            [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
              .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] ≤
      NetworkPlusCal.Statement.listAborting (V := V) Ξ Ω
          [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
            .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] ∪
        NetworkPlusCal.Statement.listReducing Ξ Ω
            [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
              .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] ∘ᵣ₁
          NetworkPlusCal.Statement.blocking Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') n)) := by
  have hpair_eq : NetworkPlusCal.Statement.listReducing (V := V) Ξ Ω
      [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
        .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))] =
    NetworkPlusCal.Statement.reducing Ξ Ω (.assign r (coe.applyComputable (head τ (inboxVar inbox τ)))) ∘ᵣ₂
      NetworkPlusCal.Statement.reducing Ξ Ω (.assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))) := by
    rw [NetworkPlusCal.Statement.listReducing_cons, NetworkPlusCal.Statement.listReducing_cons,
      NetworkPlusCal.Statement.listReducing_nil, Relation.lcomp₂.right_id_eq]
  rintro ⟨σ, ε⟩ (hblk | ⟨mid, ε₁, ε₂, hred, hpairAbort, rfl⟩)
  · obtain ⟨M, F, b, hbool, hbne, hbeval, rfl, rfl⟩ := hblk
    rcases assign_aborts_or_steps (r := r)
        (rhs := coe.applyComputable (head τ (inboxVar inbox τ))) (M := M) (F := F) with
      hab | ⟨w, rpath, M', hw, hpath, hupd⟩
    · exact Set.mem_union_left _ (by
        rw [NetworkPlusCal.Statement.listAborting_cons]; exact Set.mem_union_left _ hab)
    · obtain ⟨v₀, hv₀, hcoe⟩ := ExprSemantics.evalCoerce.mp hw
      obtain ⟨sv, vs', hsvEval, hseq⟩ := SeqBuiltins.evalHead.mp hv₀
      have hsv : M.lookup inbox = .some sv := ExprSemantics.evalVar.mp hsvEval
      obtain ⟨b₀, hb₀, -, hiff₀⟩ :=
        eval_lenGt_inbox (Ξ := Ξ) (Ω := Ω) (τ := τ') (n := n + 1) hsv hseq
      obtain rfl := ExprSemantics.evalUnique hbeval hb₀
      have hlen : ¬ n < vs'.length := λ h ↦ hbne (hiff₀.mpr (by rw [List.length_cons]; omega))
      have hsv' : M'.lookup inbox = .some sv :=
        (Memory.lookup_update_ne hupd (Ne.symm hne)).trans hsv
      obtain ⟨t, ht⟩ := ExprSemantics.isSeq_tail hseq
      refine Set.mem_union_right _ ⟨⟨M'.insert inbox t, F, .none⟩, 1, 1, ?_, ?_, (one_mul 1).symm⟩
      · rw [hpair_eq]
        exact (consumption_pair_iff hne).mpr
          ⟨M, F, M', sv, t, v₀, w, vs', rpath, rfl, rfl, rfl, hsv, hseq, ht, hcoe, hpath, hupd⟩
      · rw [await_lenGt_blocking_iff (Finmap.lookup_insert _) ht]
        exact ⟨rfl, by omega⟩
  · obtain ⟨M, F, rfl, rfl, -, rfl⟩ := NetworkPlusCal.Statement.reducing.await.elim hred
    rw [one_mul]
    exact Set.mem_union_left _ hpairAbort

/-- **The whole accumulator past one compiled guard, for the runs that block.**
`reorder_pairs_lenGt`'s blocking twin, the same `Relation.lcomp₁.commute_step` induction as the
aborting one, with `reorder_consumption_lenGt_block` for the pair. The `∘ᵣ₁` side is `listAborting`
throughout: a consumption assignment never blocks, so the only failure the guard's block can become
across the pairs is one of them aborting. -/
theorem reorder_pairs_lenGt_block {inbox : String} {τ' : ComputableTLAPlus.Typ} {k : Nat}
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    (h : ConsumptionPairs inbox k A) {n : Nat} :
    NetworkPlusCal.Statement.blocking (V := V) Ξ Ω
          (.await (lenGt τ' (inboxVar inbox τ') (n + k))) ∪
        NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') (n + k))) ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting Ξ Ω (consumptions A) ≤
      NetworkPlusCal.Statement.listAborting (V := V) Ξ Ω (consumptions A) ∪
        NetworkPlusCal.Statement.listReducing Ξ Ω (consumptions A) ∘ᵣ₁
          NetworkPlusCal.Statement.blocking Ξ Ω (.await (lenGt τ' (inboxVar inbox τ') n)) := by
  induction h generalizing n with
  | nil =>
    rw [consumptions_nil, NetworkPlusCal.Statement.listAborting_nil,
      NetworkPlusCal.Statement.listReducing_nil,
      Relation.lcomp₁.right_empty_eq_empty, Relation.lcomp₁.left_id_eq, Set.union_empty,
      Set.empty_union, Nat.add_zero]
  | snoc pairs hne IH =>
    rw [consumptions_append, NetworkPlusCal.Statement.listAborting_append,
      NetworkPlusCal.Statement.listReducing_append, Relation.lcomp₁.union_lcomp₂,
      consumptions_receiveInstrs, ← Nat.add_assoc, Nat.add_right_comm]
    exact Relation.lcomp₁.commute_step (reorder_pairs_lenGt pairs).symm IH le_rfl
      (reorder_consumption_lenGt_block hne)

/-- One `receive`'s adjacent target: its inbox-length guard, then the two consumption assignments
it contributes. Named because the walk's `receive` step meets it twice — once reducing, once
aborting — and because it is `receive_refines`'s target. -/
def receiveGroup (Ξ : OperatorEnv) (Ω : Model V) (r : ComputableGuardedPlusCal.Ref)
    (coe : TypedTLAPlus.Coercion) (inbox : String) (τ : ComputableTLAPlus.Typ) :
    Set (LocalState V × Trace V × LocalState V) :=
  NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₂
    NetworkPlusCal.Statement.listReducing Ξ Ω
      [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
        .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))]

@[inherit_doc receiveGroup]
def receiveGroupAborting (Ξ : OperatorEnv) (Ω : Model V) (r : ComputableGuardedPlusCal.Ref)
    (coe : TypedTLAPlus.Coercion) (inbox : String) (τ : ComputableTLAPlus.Typ) :
    Set (LocalState V × Trace V) :=
  NetworkPlusCal.Statement.aborting Ξ Ω (.await (lenGt τ (inboxVar inbox τ) 0)) ∪
    NetworkPlusCal.Statement.reducing Ξ Ω (.await (lenGt τ (inboxVar inbox τ) 0)) ∘ᵣ₁
      NetworkPlusCal.Statement.listAborting Ξ Ω
        [.assign r (coe.applyComputable (head τ (inboxVar inbox τ))),
          .assign (inboxRef inbox τ) (tail τ (inboxVar inbox τ))]

/-- `receive_refines` at the two named groups, with the trailing `Relation.Idle`/`∅` the list forms
carry discharged. Nothing new — the same theorem, in the shape the walk's invariant states. -/
theorem receiveGroup_refines {c r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion}
    {inbox : String} {τ : ComputableTLAPlus.Typ} {pref : ChanKey V → List V}
    (fresh : ReceiveFresh c r inbox) :
    StrongRefinement (relatesTo (V := V) Ξ Ω (.some (c, inbox)) pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.reducing Ξ Ω (.receive c r coe))
      (GuardedPlusCal.Statement.aborting Ξ Ω (.receive c r coe))
      (GuardedPlusCal.Statement.diverging (.receive c r coe))
      (receiveGroup Ξ Ω r coe inbox τ) (receiveGroupAborting Ξ Ω r coe inbox τ) ∅ ∅ ∅ := by
  rw [receiveGroup, receiveGroupAborting, NetworkPlusCal.Statement.listReducing_cons,
    NetworkPlusCal.Statement.listReducing_cons, NetworkPlusCal.Statement.listReducing_nil,
    Relation.lcomp₂.right_id_eq, NetworkPlusCal.Statement.listAborting_cons,
    NetworkPlusCal.Statement.listAborting_cons, NetworkPlusCal.Statement.listAborting_nil,
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
private def AccFresh (_inbox : String) (st : ReceiveState)
    (suff : List (ComputableGuardedPlusCal.Statement true false)) : Prop :=
  ∀ a ∈ st.newInstrs, ∀ x ann bound e,
    GuardedPlusCal.Statement.with x ann bound e ∈ suff →
      x ∉ GuardedPlusCal.Ref.freeVars a.1 ∧ Expression.FreshIn x a.2.1

/-- A compiled guard is an `await` or a `with` — everything `stepStatement` emits. Named so the
blocking clause of `WalkInv` and its fifo-locality argument can quantify over it. -/
def IsNetGuard (S : ComputableNetworkPlusCal.Statement true false) : Prop :=
  (∃ e, S = .await e) ∨ ∃ x ann bound e, S = .with x ann bound e

/-- Substituting into a guard leaves it a guard — `substGuardStmt` maps `await`/`with` to `await`/
`with`. -/
theorem isNetGuard_substGuards
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {S : ComputableNetworkPlusCal.Statement true false} (h : IsNetGuard S) :
    IsNetGuard (substGuards A S) := by
  induction A with
  | nil => rwa [substGuards_nil]
  | cons a A IH =>
    rw [substGuards_cons]
    rcases IH with ⟨e, he⟩ | ⟨x, ann, bound, e, he⟩
    · rw [he, substGuardStmt_await]; exact .inl ⟨_, rfl⟩
    · rw [he, substGuardStmt_with]; exact .inr ⟨_, _, _, _, rfl⟩

/-- **The mailbox channel is empty**, at whatever path its args resolve to in the state's memory —
the target-state shadow of `relayBlocking`, and what makes a `receive`'s blocking transfer across
`relatesTo`. Restricts the target reduce set of the walk's blocking clause,
`{x ∈ listBlocking results | Drained mbox x}`. -/
def Drained (Ξ : OperatorEnv) (Ω : Model V) (mbox : Mailbox)
    (x : GuardedPlusCal.LocalState V × Trace V) : Prop :=
  ∀ (c : ComputableGuardedPlusCal.Ref) (ib : String)
    (cp : List (ComputableTLAPlus.PathStep V)), mbox = .some (c, ib) →
    List.Forall₂ (EvalStep Ξ Ω x.1.mem) c.args cp → x.1.fifos.lookup ⟨c.name, cp⟩ = .some []

/-- **The four-component `StrongRefinement` the walk carries.** Reducing/aborting are the emitted
guards followed by the pending consumption pairs, related to the source guards; **blocking** (the
fourth component) is the emitted guards blocked at a `Drained` state, related to the source blocked
or aborting. Named so the blocking-step helpers and `stepStatement_spec` pass it as one argument. -/
private abbrev WalkRef (Ξ : OperatorEnv) (Ω : Model V) (mbox : Mailbox) (pref : ChanKey V → List V)
    (walked : List (ComputableGuardedPlusCal.Statement true false))
    (results : List (ComputableNetworkPlusCal.Statement true false))
    (A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)) : Prop :=
  StrongRefinement (relatesTo (V := V) Ξ Ω mbox pref) (instTrace (V := V)).Rτ
    (GuardedPlusCal.Statement.listReducing Ξ Ω walked)
    (GuardedPlusCal.Statement.listAborting Ξ Ω walked) ∅
    (NetworkPlusCal.Statement.listReducing Ξ Ω results ∘ᵣ₂
      NetworkPlusCal.Statement.listReducing Ξ Ω (consumptions A))
    (NetworkPlusCal.Statement.listAborting Ξ Ω results ∪
      NetworkPlusCal.Statement.listReducing Ξ Ω results ∘ᵣ₁
        NetworkPlusCal.Statement.listAborting Ξ Ω (consumptions A))
    ∅
    (GuardedPlusCal.Statement.listBlocking Ξ Ω walked)
    {x ∈ NetworkPlusCal.Statement.listBlocking Ξ Ω results | Drained Ξ Ω mbox x}

/-- **The walk's loop invariant.** What holds of `stepStatement`'s state once the `walked` prefix of
a precondition has been compiled to `results`: the accumulator is exactly `st.i` consumption pairs,
and `walked` already refines the emitted guards followed by those pending pairs (`WalkRef`).

Carrying the refinement *here* is the whole design. Each pair is moved past the guards that follow it
by the very step that produces it, so no two orderings of a whole block ever have to be related — the
`Head`/`Tail` bookkeeping stays local to one step. `WalkRef`'s **fourth** component is the blocking
clause: its target set is `listBlocking results` restricted to `Drained` states, so a `receive`'s
`Len(inbox) > 0` guard blocking transfers to the source. The `IsNetGuard`/`Fresh` clauses ride
alongside — the former so the blocking step can reorder `substGuards` past the pairs, the latter for
that reorder's freshness side condition.

**`mbox` is a parameter, not `.some (c₀, inbox)`.** A process with no `receive` at all is compiled
without an `inbox` local and so must be related at `.none` (`Mailbox`'s own doc), which no chain
fixed at `.some` can reach. Every clause here is insensitive to which it is; what forces `.some` is a
`receive`, and `stepStatement_spec` below asks for it exactly there. -/
private def WalkInv (Ξ : OperatorEnv) (Ω : Model V) (mbox : Mailbox)
    (c₀ : ComputableGuardedPlusCal.Ref) (inbox : String)
    (pref : ChanKey V → List V)
    (walked : List (ComputableGuardedPlusCal.Statement true false))
    (results : List (ComputableNetworkPlusCal.Statement true false))
    (st : ReceiveState) : Prop :=
  ConsumptionPairs inbox st.i st.newInstrs ∧ results.length = walked.length ∧
    (∀ x ∈ st.rxs, x.1 = c₀ ∧ mbox = .some (c₀, inbox) ∧
      inbox ∉ GuardedPlusCal.Ref.freeVars c₀) ∧
    (∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ walked → st.rxs ≠ []) ∧
    (∀ S ∈ results, IsNetGuard S) ∧
    (∀ S ∈ walked, Fresh mbox S) ∧
    WalkRef (V := V) Ξ Ω mbox pref walked results st.newInstrs

omit [SeqBuiltins V] in
/-- The invariant holds at the start: nothing walked, nothing emitted, nothing pending. -/
private theorem WalkInv.nil {mbox : Mailbox} {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
    {pref : ChanKey V → List V} :
    WalkInv (V := V) Ξ Ω mbox c₀ inbox pref [] [] {} := by
  refine ⟨.nil, rfl, nofun, nofun, nofun, nofun, ?_⟩
  unfold WalkRef
  -- `simp only`, not `rw`: `({} : ReceiveState).newInstrs` is a projection out of a structure
  -- literal, and `rw`'s syntactic match never gets past it to `consumptions_nil`
  simp only [GuardedPlusCal.Statement.listReducing_nil, GuardedPlusCal.Statement.listAborting_nil,
    GuardedPlusCal.Statement.listBlocking_nil, consumptions_nil,
    NetworkPlusCal.Statement.listReducing_nil, NetworkPlusCal.Statement.listAborting_nil,
    NetworkPlusCal.Statement.listBlocking_nil, Set.sep_empty, Relation.lcomp₂.left_id_eq,
    Relation.lcomp₁.right_empty_eq_empty, Set.union_self]
  exact StrongRefinement.ofNonDiverging _ (StrongRefinement.Terminating.Id _)
    (StrongRefinement.Aborting.Empty _)

omit [SeqBuiltins V] in
/-- **The blocking field, extended by a `with`/`await` guard.** The new guard's block is reordered
past the pending pairs (`reorder_assigns_guard_block`); its `listAborting` branch is handed to the
reducing/aborting components of `ref`, its plain-guard branch composed into the reducing side and
then transferred by `guardBlocking'_sim`. `Drained` rides through untouched — a guard does not touch
the mailbox. -/
private theorem WalkRef.blocking_step_guard {mbox : Mailbox} {pref : ChanKey V → List V}
    {walked : List (ComputableGuardedPlusCal.Statement true false)}
    {results : List (ComputableNetworkPlusCal.Statement true false)}
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {S : ComputableGuardedPlusCal.Statement true false}
    {Sn : ComputableNetworkPlusCal.Statement true false}
    (hSn : NetworkPlusCal.Statement.blocking (V := V) Ξ Ω Sn =
      GuardedPlusCal.Statement.blocking Ξ Ω S)
    (notRecv : ∀ c r coe, S ≠ .receive c r coe) (gfresh : Fresh mbox S)
    (hfresh : ∀ a ∈ A, GuardFresh a.1 a.2.1 Sn)
    (ref : WalkRef (V := V) Ξ Ω mbox pref walked results A) :
    StrongRefinement.Blocking (relatesTo (V := V) Ξ Ω mbox pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.listBlocking Ξ Ω (walked ++ [S]))
      (GuardedPlusCal.Statement.listAborting Ξ Ω (walked ++ [S]))
      {x ∈ NetworkPlusCal.Statement.listBlocking Ξ Ω (results ++ [substGuards A Sn]) |
        Drained Ξ Ω mbox x} := by
  rintro σₜ ε σₛ sim ⟨hin, hdrained⟩
  rw [NetworkPlusCal.Statement.listBlocking_append, NetworkPlusCal.Statement.listBlocking_cons,
    NetworkPlusCal.Statement.listBlocking_nil, Relation.lcomp₁.right_empty_eq_empty,
    Set.union_empty] at hin
  rcases hin with hl | ⟨σₘ, ε₁, ε₂, hred, hgblk, rfl⟩
  · rcases ref.blocking σₜ ε σₛ sim ⟨hl, hdrained⟩ with ⟨ε', hτ, hb⟩ | ⟨ε', hpfx, ha⟩
    · exact .inl ⟨ε', hτ, by
        rw [GuardedPlusCal.Statement.listBlocking_append]; exact Set.mem_union_left _ hb⟩
    · exact .inr ⟨ε', hpfx, by
        rw [GuardedPlusCal.Statement.listAborting_append]; exact Set.mem_union_left _ ha⟩
  · rcases reorder_assigns_guard_block (V := V) (Ξ := Ξ) (Ω := Ω) hfresh hgblk with
      habs | ⟨σ_f, ε₃, ε₄, hcons, hSnblk, rfl⟩
    · have hmem : (⟨σₜ, ε₁ * ε₂⟩ : LocalState V × Trace V) ∈
          NetworkPlusCal.Statement.listAborting Ξ Ω results ∪
            NetworkPlusCal.Statement.listReducing Ξ Ω results ∘ᵣ₁
              NetworkPlusCal.Statement.listAborting Ξ Ω (consumptions A) :=
        Set.mem_union_right _ ⟨σₘ, ε₁, ε₂, hred, habs, rfl⟩
      rcases ref.aborting _ _ _ sim hmem with ⟨ε', hpfx, ha⟩
      exact .inr ⟨ε', hpfx, by
        rw [GuardedPlusCal.Statement.listAborting_append]; exact Set.mem_union_left _ ha⟩
    · have hrun : (⟨σₜ, ε₁ * ε₃, σ_f⟩ : LocalState V × Trace V × LocalState V) ∈
          NetworkPlusCal.Statement.listReducing Ξ Ω results ∘ᵣ₂
            NetworkPlusCal.Statement.listReducing Ξ Ω (consumptions A) :=
        ⟨σₘ, ε₁, ε₃, hred, hcons, rfl⟩
      obtain rfl := NetworkPlusCal.Statement.blocking_trace_eq_one hSnblk
      rcases ref.terminating _ _ _ _ sim hrun with
        ⟨σₛ', ε', hrel, hτ, hsred⟩ | ⟨ε', hpfx, ha⟩
      · obtain rfl : ε' = ε₁ * ε₃ := hτ
        have hSblk : (⟨σ_f, (1 : Trace V)⟩ : LocalState V × Trace V) ∈
          GuardedPlusCal.Statement.blocking Ξ Ω S := hSn ▸ hSnblk
        refine .inl ⟨ε₁ * ε₃ * 1, ?_, ?_⟩
        · show (ε₁ * ε₃ * 1 : Trace V) = ε₁ * (ε₃ * 1); rw [mul_assoc]
        · rw [GuardedPlusCal.Statement.listBlocking_append,
            GuardedPlusCal.Statement.listBlocking_cons, GuardedPlusCal.Statement.listBlocking_nil,
            Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]
          exact Set.mem_union_right _ ⟨σₛ', ε₁ * ε₃, 1, hsred,
            Statement.guardBlocking'_sim S notRecv gfresh hrel hSblk, rfl⟩
      · refine .inr ⟨ε', ?_, by
          rw [GuardedPlusCal.Statement.listAborting_append]; exact Set.mem_union_left _ ha⟩
        rw [mul_one]; exact hpfx

/-- **The blocking field, extended by a `receive`.** The compiled `Len(inbox) > k` guard's block is
reordered past the pending pairs (`reorder_pairs_lenGt_block`), which drops it to `Len(inbox) > 0`
after the pairs run; the reducing/aborting components carry the prefix, and `receive_blocking_sim`
finishes at the drained channel — `Drained` at the target state transported to the post-`walked`
source state, `M₂ → M₁` by `sim`, `M₁ → σₛ'.mem` by `Statement.listReducing_locality`. -/
private theorem WalkRef.blocking_step_receive {mbox : Mailbox} {c₀ : ComputableGuardedPlusCal.Ref}
    {inbox : String} {pref : ChanKey V → List V}
    {walked : List (ComputableGuardedPlusCal.Statement true false)}
    {results : List (ComputableNetworkPlusCal.Statement true false)}
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {c r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion} {τ : ComputableTLAPlus.Typ}
    {k : ℕ}
    (hmb : mbox = .some (c₀, inbox)) (hcc : c = c₀)
    (hcfresh : inbox ∉ GuardedPlusCal.Ref.freeVars c)
    (hA : ConsumptionPairs inbox k A)
    (hguards : ∀ S ∈ results, IsNetGuard S)
    (hwf : ∀ S ∈ walked, Fresh mbox S)
    (ref : WalkRef (V := V) Ξ Ω mbox pref walked results A) :
    StrongRefinement.Blocking (relatesTo (V := V) Ξ Ω mbox pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.listBlocking Ξ Ω (walked ++ [.receive c r coe]))
      (GuardedPlusCal.Statement.listAborting Ξ Ω (walked ++ [.receive c r coe]))
      {x ∈ NetworkPlusCal.Statement.listBlocking Ξ Ω
          (results ++ [.await (lenGt τ (inboxVar inbox τ) k)]) | Drained Ξ Ω mbox x} := by
  subst hcc hmb
  rintro σₜ ε σₛ sim ⟨hin, hdrained⟩
  rw [NetworkPlusCal.Statement.listBlocking_append, NetworkPlusCal.Statement.listBlocking_cons,
    NetworkPlusCal.Statement.listBlocking_nil, Relation.lcomp₁.right_empty_eq_empty,
    Set.union_empty] at hin
  rcases hin with hl | ⟨σₘ, ε₁, ε₂, hred, hgblk, rfl⟩
  · rcases ref.blocking σₜ ε σₛ sim ⟨hl, hdrained⟩ with ⟨ε', hτ, hb⟩ | ⟨ε', hpfx, ha⟩
    · exact .inl ⟨ε', hτ, by
        rw [GuardedPlusCal.Statement.listBlocking_append]; exact Set.mem_union_left _ hb⟩
    · exact .inr ⟨ε', hpfx, by
        rw [GuardedPlusCal.Statement.listAborting_append]; exact Set.mem_union_left _ ha⟩
  · have hpairs := reorder_pairs_lenGt_block (V := V) (Ξ := Ξ) (Ω := Ω) (τ' := τ) hA (n := 0)
    rw [Nat.zero_add] at hpairs
    rcases hpairs (Set.mem_union_left _ hgblk) with
      habs | ⟨σ_f, ε₃, ε₄, hcons, hb0, rfl⟩
    · have hmem : (⟨σₜ, ε₁ * ε₂⟩ : LocalState V × Trace V) ∈
          NetworkPlusCal.Statement.listAborting Ξ Ω results ∪
            NetworkPlusCal.Statement.listReducing Ξ Ω results ∘ᵣ₁
              NetworkPlusCal.Statement.listAborting Ξ Ω (consumptions A) :=
        Set.mem_union_right _ ⟨σₘ, ε₁, ε₂, hred, habs, rfl⟩
      rcases ref.aborting _ _ _ sim hmem with ⟨ε', hpfx, ha⟩
      exact .inr ⟨ε', hpfx, by
        rw [GuardedPlusCal.Statement.listAborting_append]; exact Set.mem_union_left _ ha⟩
    · have hrun : (⟨σₜ, ε₁ * ε₃, σ_f⟩ : LocalState V × Trace V × LocalState V) ∈
          NetworkPlusCal.Statement.listReducing Ξ Ω results ∘ᵣ₂
            NetworkPlusCal.Statement.listReducing Ξ Ω (consumptions A) :=
        ⟨σₘ, ε₁, ε₃, hred, hcons, rfl⟩
      obtain rfl := NetworkPlusCal.Statement.blocking_trace_eq_one hb0
      -- the target fifos never move through the guards and the consumption assignments
      have hff : σ_f.fifos = σₜ.fifos := by
        obtain ⟨σq, εq₁, εq₂, hq₁, hq₂, -⟩ := hrun
        rw [NetworkPlusCal.Statement.listReducing_fifos_of_assigns consumptions_all_assign hq₂,
          NetworkPlusCal.Statement.listReducing_fifos_of_guards hguards hq₁]
      rcases ref.terminating _ _ _ _ sim hrun with
        ⟨σₛ', ε', hrel, hτ, hsred⟩ | ⟨ε', hpfx, ha⟩
      · obtain rfl : ε' = ε₁ * ε₃ := hτ
        -- `Drained` is at `σₜ.mem`; move it to `σₛ'.mem` — `M₂ → M₁` by `sim`, `M₁ → σₛ'` by locality
        have hdrain' : ∀ p, List.Forall₂ (EvalStep Ξ Ω σₛ'.mem) c.args p →
            σ_f.fifos.lookup ⟨c.name, p⟩ = .some [] := by
          intro p hp
          have hloc : ∀ y ∈ GuardedPlusCal.Ref.freeVars c,
              Finmap.lookup y σₛ'.mem = Finmap.lookup y σₜ.mem := by
            intro y hy
            have hne : y ≠ inbox := fun h ↦ hcfresh (h ▸ hy)
            refine .trans ?_ (sim.mem_agree' y (fun _ ib₁ h ↦ by
              simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2 ▸ hne))
            refine Statement.listReducing_locality hsred (λ Sw hSw x hx hyx ↦ ?_)
            exact (hwf Sw hSw c inbox rfl).2.2.1 x hx (hyx ▸ hy)
          have hp' : List.Forall₂ (EvalStep Ξ Ω σₜ.mem) c.args p :=
            (Ref.EvalArgs.congr_of_agree hloc).mp hp
          rw [hff]
          exact hdrained c inbox p rfl hp'
        refine .inl ⟨ε₁ * ε₃ * 1, ?_, ?_⟩
        · show (ε₁ * ε₃ * 1 : Trace V) = ε₁ * (ε₃ * 1); rw [mul_assoc]
        · rw [GuardedPlusCal.Statement.listBlocking_append,
            GuardedPlusCal.Statement.listBlocking_cons, GuardedPlusCal.Statement.listBlocking_nil,
            Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]
          exact Set.mem_union_right _ ⟨σₛ', ε₁ * ε₃, 1, hsred,
            receive_blocking_sim (r := r) (coe := coe) hrel hdrain' hb0, rfl⟩
      · refine .inr ⟨ε', ?_, by
          rw [GuardedPlusCal.Statement.listAborting_append]; exact Set.mem_union_left _ ha⟩
        rw [mul_one]; exact hpfx

omit [SeqBuiltins V] in
/-- **`WalkRef` extended by a `with`/`await` guard.** Reducing/aborting are the emitted substituted
guard composed onto `ref` via `StrongRefinement.Comp`, then the pending pairs commuted back
(`reorder_assigns_guard'`); blocking is `WalkRef.blocking_step_guard`; diverging is vacuous. -/
private theorem WalkRef.step_guard {mbox : Mailbox} {pref : ChanKey V → List V}
    {walked : List (ComputableGuardedPlusCal.Statement true false)}
    {results : List (ComputableNetworkPlusCal.Statement true false)}
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {S : ComputableGuardedPlusCal.Statement true false}
    {Sn : ComputableNetworkPlusCal.Statement true false}
    (hSnR : NetworkPlusCal.Statement.reducing (V := V) Ξ Ω Sn =
      GuardedPlusCal.Statement.reducing Ξ Ω S)
    (hSnA : NetworkPlusCal.Statement.aborting (V := V) Ξ Ω Sn =
      GuardedPlusCal.Statement.aborting Ξ Ω S)
    (hSnB : NetworkPlusCal.Statement.blocking (V := V) Ξ Ω Sn =
      GuardedPlusCal.Statement.blocking Ξ Ω S)
    (notRecv : ∀ c r coe, S ≠ .receive c r coe) (gfresh : Fresh mbox S)
    (hfresh : ∀ a ∈ A, GuardFresh a.1 a.2.1 Sn)
    (ref : WalkRef (V := V) Ξ Ω mbox pref walked results A) :
    WalkRef (V := V) Ξ Ω mbox pref (walked ++ [S]) (results ++ [substGuards A Sn]) A := by
  have hcomp := StrongRefinement.Comp _ ref (guard_refines S notRecv gfresh)
  simp only [GuardedPlusCal.Statement.diverging_eq_empty,
    Relation.lcomp₁.right_empty_eq_empty, Set.union_self] at hcomp
  refine ⟨?_, ?_, StrongRefinement.Diverging.Empty _,
    WalkRef.blocking_step_guard hSnB notRecv gfresh hfresh ref⟩
  · simp only [GuardedPlusCal.Statement.listReducing_append,
      GuardedPlusCal.Statement.listAborting_append,
      NetworkPlusCal.Statement.listReducing_append,
      GuardedPlusCal.Statement.listReducing_cons, GuardedPlusCal.Statement.listReducing_nil,
      GuardedPlusCal.Statement.listAborting_cons, GuardedPlusCal.Statement.listAborting_nil,
      NetworkPlusCal.Statement.listReducing_cons, NetworkPlusCal.Statement.listReducing_nil,
      Relation.lcomp₂.right_id_eq, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]
    rw [← Relation.lcomp₂.assoc, ← reorder_assigns_guard' hfresh, Relation.lcomp₂.assoc, hSnR]
    exact hcomp.terminating
  · simp only [GuardedPlusCal.Statement.listAborting_append,
      NetworkPlusCal.Statement.listReducing_append,
      NetworkPlusCal.Statement.listAborting_append,
      GuardedPlusCal.Statement.listAborting_cons, GuardedPlusCal.Statement.listAborting_nil,
      NetworkPlusCal.Statement.listReducing_cons, NetworkPlusCal.Statement.listReducing_nil,
      NetworkPlusCal.Statement.listAborting_cons, NetworkPlusCal.Statement.listAborting_nil,
      Relation.lcomp₂.right_id_eq, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty,
      Relation.lcomp₁.union_lcomp₂]
    refine StrongRefinement.Aborting.Mono le_rfl ?_ hcomp.aborting
    rw [Relation.lcomp₁.union_lcomp₂, ← hSnA]
    exact Set.union_le_union le_rfl
      (Relation.lcomp₁.mono le_rfl (reorder_assigns_guard_abort' hfresh))

/-- **`WalkRef` extended by a `receive`.** The compiled `Len(inbox) > k` guard is composed onto
`ref`; the pending pairs (the new pair included) commute past it (`reorder_pairs_lenGt`); blocking
is `WalkRef.blocking_step_receive`; diverging is vacuous. -/
private theorem WalkRef.step_receive {mbox : Mailbox} {c₀ : ComputableGuardedPlusCal.Ref}
    {inbox : String} {pref : ChanKey V → List V}
    {walked : List (ComputableGuardedPlusCal.Statement true false)}
    {results : List (ComputableNetworkPlusCal.Statement true false)}
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {c r : ComputableGuardedPlusCal.Ref} {coe : TypedTLAPlus.Coercion} {τ : ComputableTLAPlus.Typ}
    {k : ℕ} {pos : SourceSpan}
    (hmb : mbox = .some (c₀, inbox)) (hcc : c = c₀)
    (hfr : ReceiveFresh c r inbox)
    (hA : ConsumptionPairs inbox k A)
    (hguards : ∀ S ∈ results, IsNetGuard S)
    (hwf : ∀ S ∈ walked, Fresh mbox S)
    (ref : WalkRef (V := V) Ξ Ω mbox pref walked results A) :
    WalkRef (V := V) Ξ Ω mbox pref (walked ++ [.receive c r coe])
      (results ++ [.await (lenGt τ (inboxVar inbox τ) k)])
      (A ++ receiveInstrs r coe inbox τ pos) := by
  subst hcc hmb
  have hnb : StrongRefinement (relatesTo (V := V) Ξ Ω (.some (c, inbox)) pref)
      (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.listReducing Ξ Ω (walked ++ [.receive c r coe]))
      (GuardedPlusCal.Statement.listAborting Ξ Ω (walked ++ [.receive c r coe])) ∅
      (NetworkPlusCal.Statement.listReducing Ξ Ω
          (results ++ [.await (lenGt τ (inboxVar inbox τ) k)]) ∘ᵣ₂
        NetworkPlusCal.Statement.listReducing Ξ Ω
          (consumptions (A ++ receiveInstrs r coe inbox τ pos)))
      (NetworkPlusCal.Statement.listAborting Ξ Ω
          (results ++ [.await (lenGt τ (inboxVar inbox τ) k)]) ∪
        NetworkPlusCal.Statement.listReducing Ξ Ω
            (results ++ [.await (lenGt τ (inboxVar inbox τ) k)]) ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting Ξ Ω
            (consumptions (A ++ receiveInstrs r coe inbox τ pos)))
      ∅
      (GuardedPlusCal.Statement.listBlocking Ξ Ω walked)
      {x ∈ NetworkPlusCal.Statement.listBlocking Ξ Ω results | Drained Ξ Ω (.some (c, inbox)) x} := by
    simp only [GuardedPlusCal.Statement.listReducing_append,
      GuardedPlusCal.Statement.listAborting_append,
      NetworkPlusCal.Statement.listReducing_append,
      NetworkPlusCal.Statement.listAborting_append,
      GuardedPlusCal.Statement.listReducing_cons, GuardedPlusCal.Statement.listReducing_nil,
      GuardedPlusCal.Statement.listAborting_cons, GuardedPlusCal.Statement.listAborting_nil,
      NetworkPlusCal.Statement.listReducing_cons, NetworkPlusCal.Statement.listReducing_nil,
      NetworkPlusCal.Statement.listAborting_cons, NetworkPlusCal.Statement.listAborting_nil,
      Relation.lcomp₂.right_id_eq, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty,
      Relation.lcomp₁.union_lcomp₂, consumptions_append,
      consumptions_receiveInstrs]
    have hQ := reorder_pairs_lenGt (V := V) (Ξ := Ξ) (Ω := Ω) (τ' := τ) hA (n := 0)
    have hQa := reorder_pairs_lenGt_abort (V := V) (Ξ := Ξ) (Ω := Ω) (τ' := τ) hA (n := 0)
    rw [Nat.zero_add] at hQ hQa
    have hcomp := StrongRefinement.Comp _ ref
      (receiveGroup_refines (V := V) (coe := coe) (τ := τ) hfr)
    simp only [GuardedPlusCal.Statement.diverging_eq_empty,
      Relation.lcomp₁.right_empty_eq_empty, Set.union_self, receiveGroup, receiveGroupAborting,
      NetworkPlusCal.Statement.listReducing_cons, NetworkPlusCal.Statement.listReducing_nil,
      NetworkPlusCal.Statement.listAborting_cons, NetworkPlusCal.Statement.listAborting_nil,
      Relation.lcomp₂.right_id_eq, Set.union_empty] at hcomp
    refine StrongRefinement.Mono le_rfl le_rfl le_rfl le_rfl ?_ ?_ le_rfl le_rfl hcomp
    · refine le_of_eq ?_
      simp only [inboxVar, ← Relation.lcomp₂.assoc] at hQ ⊢
      rw [Relation.lcomp₂.assoc (R₁ := NetworkPlusCal.Statement.reducing Ξ Ω
          (.await (lenGt τ (.var inbox (.seq τ) .binder) k))),
        ← hQ, ← Relation.lcomp₂.assoc]
    · simp only [inboxVar, inboxRef] at hQ hQa ⊢
      rw [Relation.lcomp₁.union_lcomp₂]
      exact Set.union_le_union le_rfl (Relation.lcomp₁.mono le_rfl
        (Relation.lcomp₁.commute_step hQ.symm hQa le_rfl le_rfl))
  exact ⟨hnb.terminating, hnb.aborting, hnb.diverging,
    WalkRef.blocking_step_receive rfl rfl hfr.1 hA hguards hwf ref⟩

open Std.Do in
/-- **One step of the walk, as a local refinement.** `stepStatement` extends the invariant by one
source statement: whatever it emits, together with whatever it appends to the accumulator, refines
the source statement composed onto the prefix.

The freshness side condition sits in the precondition rather than in the signature because it is
about the *accumulator*, which only exists at run time.

`hmb` is where the mailbox stops being arbitrary. A `with` or an `await` refines itself at any
`mbox`; a `receive` is what the pass compiles into reads of `inbox`, so relating the two sides across
one needs the invariant to *be* about that `inbox`. A receive-free walk never discharges `hmb` and so
runs at `.none` as happily as at `.some`. -/
private theorem stepStatement_spec {chans : Guarded2NetworkChans} {mbox : Mailbox}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
    (S : ComputableGuardedPlusCal.Statement true false)
    {pref : ChanKey V → List V}
    {walked : List (ComputableGuardedPlusCal.Statement true false)}
    {results : List (ComputableNetworkPlusCal.Statement true false)}
    {suff : List (ComputableGuardedPlusCal.Statement true false)}
    (hmb : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      S = GuardedPlusCal.Statement.receive c r coe → mbox = .some (c₀, inbox))
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      S = GuardedPlusCal.Statement.receive c r coe → c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : Fresh mbox S) (pfresh : PairsFresh inbox (S :: suff)) :
    ⦃λ st ↦ ⌜WalkInv (V := V) Ξ Ω mbox c₀ inbox pref walked results st ∧ AccFresh inbox st (S :: suff)⌝⦄
      (stepStatement (m := G2NM) chans inbox S)
    ⦃⇓? T st' => ⌜WalkInv (V := V) Ξ Ω mbox c₀ inbox pref (walked ++ [S]) (results ++ [T]) st' ∧
      AccFresh inbox st' suff⌝⦄ := by
  -- three goals, one per guard constructor, each a plain `WalkInv` obligation
  mintro ⟨inv, gf⟩
  cases S <;> simp only [stepStatement] <;> mvcgen
  case vc1.with name ann bound e st n hinv =>
    obtain ⟨⟨pairs, hlen, hrxs, hrecv, hguards, hwf, ref⟩, gf'⟩ := hinv
    have hfresh : ∀ a ∈ st.newInstrs,
        GuardFresh a.1 a.2.1 (NetworkPlusCal.Statement.with name ann bound e) := by
      intro a ha x _ _ _ heq
      injection heq with hx _ _ _
      subst hx
      exact gf' a ha _ _ _ _ List.mem_cons_self
    refine ⟨⟨pairs, by simp [hlen], hrxs, ?_, ?_, ?_, ?_⟩,
      λ a ha x _ _ _ hm ↦ gf' a ha x _ _ _ (List.mem_cons_of_mem _ hm)⟩
    · intro c r coe hmem
      rcases List.mem_append.mp hmem with h' | h'
      · exact hrecv c r coe h'
      · exact nomatch List.mem_singleton.mp h'
    · intro S' hS'
      rcases List.mem_append.mp hS' with h' | h'
      · exact hguards S' h'
      · obtain rfl := List.mem_singleton.mp h'
        exact isNetGuard_substGuards (.inr ⟨name, ann, bound, e, rfl⟩)
    · intro S' hS'
      rcases List.mem_append.mp hS' with h' | h'
      · exact hwf S' h'
      · obtain rfl := List.mem_singleton.mp h'; exact gfresh
    · exact WalkRef.step_guard with_reducing'_eq with_aborting'_eq with_blocking'_eq
        (λ _ _ _ h ↦ nomatch h) gfresh hfresh ref
  case vc1.await e st n hinv =>
    obtain ⟨⟨pairs, hlen, hrxs, hrecv, hguards, hwf, ref⟩, gf'⟩ := hinv
    -- an `await` binds nothing, so its freshness against the accumulator is unconditional
    have hfresh : ∀ a ∈ st.newInstrs,
        GuardFresh a.1 a.2.1 (NetworkPlusCal.Statement.await e) := λ _ _ ↦ GuardFresh.await
    refine ⟨⟨pairs, by simp [hlen], hrxs, ?_, ?_, ?_, ?_⟩,
      λ a ha x _ _ _ hm ↦ gf' a ha x _ _ _ (List.mem_cons_of_mem _ hm)⟩
    · intro c r coe hmem
      rcases List.mem_append.mp hmem with h' | h'
      · exact hrecv c r coe h'
      · exact nomatch List.mem_singleton.mp h'
    · intro S' hS'
      rcases List.mem_append.mp hS' with h' | h'
      · exact hguards S' h'
      · obtain rfl := List.mem_singleton.mp h'
        exact isNetGuard_substGuards (.inl ⟨e, rfl⟩)
    · intro S' hS'
      rcases List.mem_append.mp hS' with h' | h'
      · exact hwf S' h'
      · obtain rfl := List.mem_singleton.mp h'; exact gfresh
    · exact WalkRef.step_guard await_reducing'_eq await_aborting'_eq await_blocking'_eq
        (λ _ _ _ h ↦ nomatch h) gfresh hfresh ref
  case vc2.receive.h_2 c r coe st n hinv τ hτ =>
    obtain ⟨⟨pairs, hlen, hrxs, _, hguards, hwf, ref⟩, gf'⟩ := hinv
    -- the one statement that pins the mailbox: from here down the walk is about *this* `inbox`
    obtain rfl := hmb c r coe rfl
    obtain ⟨rfl, hfr⟩ := rfresh c r coe rfl
    refine ⟨⟨pairs.snoc (ne_name_of_fresh hfr.2.1).symm, by simp [hlen], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    -- the one step that grows `rxs`: by this `receive`'s own channel, and so to something non-empty
    · intro x hx
      rw [List.concat_eq_append] at hx
      rcases List.mem_append.mp hx with h' | h'
      · exact hrxs x h'
      · rw [List.mem_singleton.mp h']
        exact ⟨rfl, rfl, hfr.1⟩
    · simp_intro ..
    · intro S' hS'
      rcases List.mem_append.mp hS' with h' | h'
      · exact hguards S' h'
      · obtain rfl := List.mem_singleton.mp h'; exact .inl ⟨_, rfl⟩
    · intro S' hS'
      rcases List.mem_append.mp hS' with h' | h'
      · exact hwf S' h'
      · obtain rfl := List.mem_singleton.mp h'; exact gfresh
    · exact WalkRef.step_receive (c₀ := c) (pos := _) rfl rfl hfr pairs hguards hwf ref
    · intro a ha x ann bound e hm
      rcases List.mem_append.mp ha with h' | h'
      · exact gf' a h' x ann bound e (List.mem_cons_of_mem _ hm)
      · exact pfresh x ann bound e (List.mem_cons_of_mem _ hm) c r coe List.mem_cons_self _ _ a h'

open Std.Do in
/-- **The whole walk.** `Spec.mapM_list` at the invariant `stepStatement_spec` maintains: the prefix
compiled so far refines what was emitted for it followed by whatever is still pending, and the
accumulator stays fresh for the statements yet to come.

Both conjuncts are needed and neither can be dropped — the refinement is the point, and `AccFresh`
is what the next step's precondition asks for. It shrinks with the suffix on a guard and is
re-established from `PairsFresh` when a `receive` grows the accumulator. -/
private theorem mapM_stepStatement_refines {chans : Guarded2NetworkChans} {mbox : Mailbox}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V}
    {Ss : List (ComputableGuardedPlusCal.Statement true false)}
    (hmb : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss → mbox = .some (c₀, inbox))
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss → c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : ∀ S ∈ Ss, Fresh mbox S) (pfresh : PairsFresh inbox Ss) :
    ⦃λ stf ↦ ⌜WalkInv (V := V) Ξ Ω mbox c₀ inbox pref [] [] stf ∧ AccFresh inbox stf Ss⌝⦄
      Ss.mapM (stepStatement (m := G2NM) chans inbox)
    ⦃⇓? bs stf' => ⌜WalkInv (V := V) Ξ Ω mbox c₀ inbox pref Ss bs stf' ∧ AccFresh inbox stf' []⌝⦄ :=
  Spec.mapM_list
    (inv := ((λ q stf ↦ ⌜WalkInv (V := V) Ξ Ω mbox c₀ inbox pref q.1.prefix q.2 stf ∧
        AccFresh inbox stf q.1.suffix⌝, ExceptConds.true) :
      Invariant Ss (List (ComputableNetworkPlusCal.Statement true false))
        (.arg ReceiveState (.except G2NError (.arg Nat .pure)))))
    (λ _ cur _suff h _bs ↦
      stepStatement_spec (V := V) (c₀ := c₀) cur
        (λ c r coe heq ↦ hmb c r coe (heq ▸ h ▸ List.mem_append_right _ List.mem_cons_self))
        (λ c r coe heq ↦ rfresh c r coe (heq ▸ h ▸ List.mem_append_right _ List.mem_cons_self))
        (gfresh cur (h ▸ List.mem_append_right _ List.mem_cons_self))
        (pfresh.mono (h ▸ List.subset_append_right _ _)))

open Std.Do in
/-- `mapM_stepStatement_refines` at the initial state, which is the form `processPrecondition`'s own
body presents: it writes `(… .mapM …).run {}`, and `StateT.run x s` reduces to `x s`, so the
toolchain's `[spec] StateT.run` never fires and `mvcgen` cannot descend on its own.

Registered `@[spec]` so the block-level proof never has to look inside the walk. -/
@[spec] private theorem mapM_stepStatement_refines_run {chans : Guarded2NetworkChans}
    {mbox : Mailbox} {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String}
    {pref : ChanKey V → List V}
    {Ss : List (ComputableGuardedPlusCal.Statement true false)}
    (hmb : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss → mbox = .some (c₀, inbox))
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ Ss → c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : ∀ S ∈ Ss, Fresh mbox S) (pfresh : PairsFresh inbox Ss) :
    ⦃⌜True⌝⦄
      ((Ss.mapM (stepStatement (m := G2NM) chans inbox)).run {})
    ⦃⇓? p _ => ⌜WalkInv (V := V) Ξ Ω mbox c₀ inbox pref Ss p.1 p.2 ∧ AccFresh inbox p.2 []⌝⦄ :=
  λ n _ ↦ mapM_stepStatement_refines (V := V) hmb rfresh gfresh pfresh {} n
    ⟨WalkInv.nil, λ _ ha ↦ nomatch ha⟩

/-- **`rfresh` assembled from its two sources.** The receive half comes from well-formedness, where
the executable restriction checks put it; the two conditions on the *generated* `inbox` come from
whoever generated it, which is `Thread.toNetwork` and not this file.

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

/-- The statements of a branch's precondition, `[]` when it has none. What the freshness hypotheses
below quantify over — `Block.toList` cannot, an `Option` having no `toList` of the right shape. -/
def preconditionList
    (pre : Option (GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement true) false)) :
    List (ComputableGuardedPlusCal.Statement true false) :=
  pre.elim [] GuardedPlusCal.Block.toList

open Std.Do in
/-- **A compiled precondition refines the source one, present or absent.** The pass's two outputs
read together: the rewritten block, and the consumption assignments it hoisted out to be run after
it.

Stated over the `Option` the pass actually takes, so that a branch with no precondition needs no
separate lemma. That case is not degenerate-by-convention: no precondition compiles to no guards, no
assignments and no receives, so both sides are `Relation.Idle` and the refinement is
`Terminating.Id` — which is also why `AtomicBranch.reducing` composes a missing precondition with
the identity relation rather than with `∅`.

Divergence is `∅` on both sides rather than `Block.diverging`, the form every composition site wants:
no statement of either language diverges (`Statement.blockDiverging_eq_empty`). -/
private theorem processPrecondition_spec {chans : Guarded2NetworkChans} {mbox : Mailbox}
    {c₀ : ComputableGuardedPlusCal.Ref} {inbox : String} {pref : ChanKey V → List V}
    {pre : Option (GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement true) false)}
    {n : Nat}
    (hmb : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ preconditionList pre → mbox = .some (c₀, inbox))
    (rfresh : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
      GuardedPlusCal.Statement.receive c r coe ∈ preconditionList pre →
        c = c₀ ∧ ReceiveFresh c r inbox)
    (gfresh : ∀ S ∈ preconditionList pre, Fresh mbox S)
    (pfresh : PairsFresh inbox (preconditionList pre)) :
    ⦃λ n₀ ↦ ⌜n₀ = n⌝⦄
    processPrecondition (m := G2NM) chans inbox pre
    ⦃⇓? (pre', assigns, rxs) _ =>
      ⌜(∀ x ∈ rxs, x.1 = c₀ ∧ mbox = .some (c₀, inbox) ∧
          inbox ∉ GuardedPlusCal.Ref.freeVars c₀) ∧
        (∀ (c r : ComputableGuardedPlusCal.Ref) coe,
          GuardedPlusCal.Statement.receive c r coe ∈ preconditionList pre → rxs ≠ []) ∧
        StrongRefinement (relatesTo (V := V) Ξ Ω mbox pref) (instTrace (V := V)).Rτ
        (pre.elim Relation.Idle (GuardedPlusCal.Block.reducing
          (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing Ξ Ω)))
        (pre.elim ∅ (GuardedPlusCal.Block.aborting
          (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.aborting Ξ Ω)
          (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing Ξ Ω)))
        ∅
        (pre'.elim Relation.Idle (GuardedPlusCal.Block.reducing
            (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing Ξ Ω)) ∘ᵣ₂
          NetworkPlusCal.Statement.listReducing Ξ Ω assigns)
        (pre'.elim ∅ (GuardedPlusCal.Block.aborting
            (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.aborting Ξ Ω)
            (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing Ξ Ω)) ∪
          pre'.elim Relation.Idle (GuardedPlusCal.Block.reducing
              (λ ⦃_⦄ ↦ NetworkPlusCal.Statement.reducing Ξ Ω)) ∘ᵣ₁
            NetworkPlusCal.Statement.listAborting Ξ Ω assigns)
        ∅
        (GuardedPlusCal.Statement.listBlocking Ξ Ω (preconditionList pre))
        {x ∈ NetworkPlusCal.Statement.listBlocking Ξ Ω (pre'.elim [] GuardedPlusCal.Block.toList) |
          Drained Ξ Ω mbox x}⌝⦄ := by
    mvcgen [processPrecondition, -StateT.run]
    with | hmb | rfresh | gfresh | pfresh => subst pre; assumption

    case h_1 =>
      refine ⟨nofun, nofun, ?_⟩
      simp only [Option.elim, NetworkPlusCal.Statement.listReducing_nil,
        NetworkPlusCal.Statement.listAborting_nil, NetworkPlusCal.Statement.listBlocking_nil,
        GuardedPlusCal.Statement.listBlocking_nil, preconditionList, Set.sep_empty,
        Relation.lcomp₂.left_id_eq, Relation.lcomp₁.right_empty_eq_empty, Set.empty_union]
      exact StrongRefinement.ofNonDiverging _ (StrongRefinement.Terminating.Id _)
        (StrongRefinement.Aborting.Empty _)

    case post.success r _ hinv =>
      obtain ⟨⟨pairs, hlen, hrxs, hrecv, hguards, hwf, ref⟩, -⟩ := hinv
      -- `dropLast`/`getLast!` put the block back together only because the walk emitted one
      -- statement per source statement, and a `Block` is non-empty by construction
      have hne : r.1 ≠ [] := by
        simp +arith [← List.length_pos_iff, hlen]
      refine ⟨hrxs, hrecv, ?_⟩
      simp only [Option.elim, GuardedPlusCal.Block.reducing_eq_listReducing,
        GuardedPlusCal.Block.aborting_eq_listAborting, GuardedPlusCal.Block.toList,
        List.dropLast_concat_getLast! hne, preconditionList]
      exact ref

omit [SeqBuiltins V] in
/-- The precondition's `blockBlocking` as a list — `Block.aborting_eq_listAborting` at
`preconditionList`, both cases of the `Option`. -/
theorem listBlocking_preconditionList
    (pre : Option (GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement true) false)) :
    GuardedPlusCal.Statement.listBlocking (V := V) Ξ Ω (preconditionList pre) =
      pre.elim ∅ (GuardedPlusCal.Statement.blockBlocking Ξ Ω) := by
  cases pre with
  | none =>
    simp only [preconditionList, Option.elim_none, GuardedPlusCal.Statement.listBlocking_nil]
  | some B =>
    simp only [preconditionList, Option.elim_some, GuardedPlusCal.Statement.blockBlocking,
      GuardedPlusCal.Block.aborting_eq_listAborting]
    rfl

omit [SeqBuiltins V] in
@[inherit_doc listBlocking_preconditionList]
theorem listAborting_preconditionList
    (pre : Option (GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement true) false)) :
    GuardedPlusCal.Statement.listAborting (V := V) Ξ Ω (preconditionList pre) =
      pre.elim ∅ (GuardedPlusCal.Statement.blockAborting Ξ Ω) := by
  cases pre with
  | none =>
    simp only [preconditionList, Option.elim_none, GuardedPlusCal.Statement.listAborting_nil]
  | some B =>
    simp only [preconditionList, Option.elim_some, GuardedPlusCal.Statement.blockAborting,
      GuardedPlusCal.Block.aborting_eq_listAborting]
    rfl

omit [SeqBuiltins V] in
/-- The Network side: the compiled block's `blockBlocking` as a list over its `toList`. -/
theorem listBlocking_toList_net
    (pre' : Option (GuardedPlusCal.Block (ComputableNetworkPlusCal.Statement true) false)) :
    NetworkPlusCal.Statement.listBlocking (V := V) Ξ Ω (pre'.elim [] GuardedPlusCal.Block.toList) =
      pre'.elim ∅ (NetworkPlusCal.Statement.blockBlocking Ξ Ω) := by
  cases pre' with
  | none =>
    simp only [Option.elim_none, NetworkPlusCal.Statement.listBlocking_nil]
  | some B =>
    simp only [Option.elim_some, NetworkPlusCal.Statement.blockBlocking,
      GuardedPlusCal.Block.aborting_eq_listAborting]
    rfl

end Guarded2Network

end
