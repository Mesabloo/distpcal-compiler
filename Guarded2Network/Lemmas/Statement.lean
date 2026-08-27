module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Relation
public import Guarded2Network.Lemmas.Trace

@[expose] public section

/-!
  Statement-level refinement: what `Guarded2Network` does to a single action statement, and the two
  transfer lemmas every later proof leans on.

  **Evaluation transfer.** The pass introduces exactly one name, `inbox`, and it is fresh
  (`freshName`'s `$` separator makes collision with a source name impossible). So any source
  expression evaluates the same in the target's memory, which differs only at `inbox`: that is
  `relatesTo.eval_iff`.

  **Reference arguments.** A reference's index path is evaluated by a `List.Forall₂` over
  `EvalStep`. Naming that relation — `Ref.EvalArgs` — and giving it its own congruence lemma keeps
  the `Forall₂` nesting out of every use site.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Expression Memory PathStep OperatorEnv Model)
open GuardedPlusCal (ChanKey EvalStep LocalState)

variable {V : Type} [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}

/-! ## Evaluation transfer -/

/-- Binding a name the expression cannot read leaves its value alone. The one-name case of
`ExprSemantics.evalLocal`, which is the only case the pass ever needs: it introduces `inbox` and
nothing else. -/
theorem eval_insert_of_fresh {M : Memory V} {x : String} {v' v : V}
    {e : ComputablePlusCal.Expression} (fresh : Expression.FreshIn x e) :
    ExprSemantics.Eval Ξ Ω (M.insert x v') e v ↔ ExprSemantics.Eval Ξ Ω M e v := by
  apply ExprSemantics.evalLocal
  intro y hy
  apply Finmap.lookup_insert_of_ne _
  rintro rfl
  exact fresh hy

/-- Related states evaluate a source expression to the same values, provided the expression does
not mention `inbox` — which no source expression does, `inbox` being freshly generated. -/
theorem relatesTo.eval_iff {c : ComputableGuardedPlusCal.Ref} {inbox : String}
    {pref : ChanKey V → List V}
    {σₛ σₜ : LocalState V} (h : σₛ ∼[Ξ, Ω,.some (c, inbox), pref] σₜ)
    {e : ComputablePlusCal.Expression} {v : V} (fresh : Expression.FreshIn inbox e) :
    ExprSemantics.Eval Ξ Ω σₛ.mem e v ↔ ExprSemantics.Eval Ξ Ω σₜ.mem e v := by
  apply ExprSemantics.evalLocal
  intro y hy
  apply h.mem_agree
  rintro rfl
  exact fresh hy

/-- The same for a process that receives nothing: there the memories are equal outright and the
freshness hypothesis has nothing to say. -/
theorem relatesTo.eval_iff_none {pref : ChanKey V → List V} {σₛ σₜ : LocalState V}
    (h : σₛ ∼[Ξ, Ω,.none, pref] σₜ)
    {e : ComputablePlusCal.Expression} {v : V} :
    ExprSemantics.Eval Ξ Ω σₛ.mem e v ↔ ExprSemantics.Eval Ξ Ω σₜ.mem e v := by
  rw [h.mem_eq]

/-- Both cases at once, with the freshness hypothesis stated so that it is vacuous when there is no
mailbox — the form a lemma quantified over an arbitrary `mbox` needs. -/
theorem relatesTo.eval_iff' {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState V}
    (h : σₛ ∼[Ξ, Ω,mbox, pref] σₜ)
    {e : ComputablePlusCal.Expression} {v : V}
    (fresh : ∀ c inbox, mbox = .some (c, inbox) → Expression.FreshIn inbox e) :
    ExprSemantics.Eval Ξ Ω σₛ.mem e v ↔ ExprSemantics.Eval Ξ Ω σₜ.mem e v := by
  match mbox with
  | .none => exact h.eval_iff_none
  | .some (c, inbox) => exact h.eval_iff (fresh c inbox rfl)

/-! ## Reference arguments -/

/-- A reference's index path, evaluated. Named, rather than left as the raw `List.Forall₂` it
unfolds to, so that transferring it between memories is one lemma about `EvalArgs` instead of a
`Forall₂`-induction at every use site. -/
abbrev Ref.EvalArgs (Ξ : OperatorEnv) (Ω : Model V) (M : Memory V)
    (r : ComputableGuardedPlusCal.Ref) (path : List (PathStep V)) : Prop :=
  List.Forall₂ (EvalStep Ξ Ω M) r.args path

/-- A path resolves to at most one value — `EvalStep.path_inj`, at the named relation. -/
theorem Ref.EvalArgs.inj {M : Memory V} {r : ComputableGuardedPlusCal.Ref}
    {path path' : List (PathStep V)} (h : Ref.EvalArgs Ξ Ω M r path) (h' : Ref.EvalArgs Ξ Ω M r path') :
    path = path' :=
  EvalStep.path_inj h h'

/-- Every index expression of a reference reads only names the reference itself reads. The bridge
from a freshness fact about a `Ref` to one about each of its index expressions, which is what
`congr_of_fresh` needs per `Forall₂` step. -/
theorem Ref.freeVars_of_mem_args {r : ComputableGuardedPlusCal.Ref}
    {e : ComputablePlusCal.Expression} (hmem : Sum.inr e ∈ r.args) {x : String}
    (hx : x ∈ e.freeVars) : x ∈ GuardedPlusCal.Ref.freeVars r := by
  -- once `x` is in the accumulator it stays there, `∪` being monotone in its left argument
  have keep : ∀ (l : List (Finset String)) (acc : Finset String), x ∈ acc →
      x ∈ l.foldl (· ∪ ·) acc := by
    intro l
    induction l with
    | nil => intro _ h; exact h
    | cons hd tl ih => intro acc h; exact ih _ (Finset.mem_union_left _ h)
  have enters : ∀ (l : List (String ⊕ ComputablePlusCal.Expression)) (acc : Finset String),
      Sum.inr e ∈ l → x ∈ (l.map λ seg ↦ match seg with
        | .inl _ => (∅ : Finset String) | .inr e' => e'.freeVars).foldl (· ∪ ·) acc := by
    intro l
    induction l with
    | nil => intro _ hmem; cases hmem
    | cons hd tl ih =>
      intro acc hmem
      rw [List.map_cons, List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact keep _ _ (Finset.mem_union_right _ hx)
      · exact ih _ hmem'
  exact Finset.mem_union_right _ (enters r.args ∅ hmem)

/-- **A reference whose path resolves has no aborting index.** `Ref.pathAborts` and `Ref.EvalArgs`
are the two halves of one question — does the access path have a value — so they cannot both hold,
and every place a refinement invariant says the mailbox channel resolves is a place the target's
"index expression has no value" abort is unreachable. -/
theorem Ref.EvalArgs.not_pathAborts {M : Memory V} {r : ComputableGuardedPlusCal.Ref}
    {path : List (PathStep V)} (h : Ref.EvalArgs Ξ Ω M r path) :
    ¬ GuardedPlusCal.Ref.pathAborts Ξ Ω M r := by
  rintro ⟨e, he, hab⟩
  rw [List.mem_filterMap] at he
  obtain ⟨seg, hseg, hget⟩ := he
  match seg, hget with
  | .inr e', hget =>
    obtain rfl : e' = e := Option.some.inj hget
    obtain ⟨_, _, hstep⟩ := List.Forall₂.exists_right h hseg
    cases hstep with
    | index hv => exact hab ⟨_, hv⟩

/-- Memories agreeing on everything a reference *reads* resolve its path identically. The
`List.Forall₂` nesting is discharged once, here, and no later proof sees it.

Stated over the names read rather than over a single excepted name, because that is the form a
*block* needs — a block writes one name per statement, so "all but one" is never the shape on offer
past the first step. `congr_of_fresh` below is the one-name case. -/
theorem Ref.EvalArgs.congr_of_agree {M₁ M₂ : Memory V} {r : ComputableGuardedPlusCal.Ref}
    {path : List (PathStep V)}
    (agree : ∀ y ∈ GuardedPlusCal.Ref.freeVars r, M₁.lookup y = M₂.lookup y) :
    Ref.EvalArgs Ξ Ω M₁ r path ↔ Ref.EvalArgs Ξ Ω M₂ r path := by
  unfold Ref.EvalArgs
  have step : ∀ (args : List (String ⊕ ComputablePlusCal.Expression))
      (path : List (PathStep V)),
      (∀ e, Sum.inr e ∈ args → ∀ y ∈ e.freeVars, M₁.lookup y = M₂.lookup y) →
      (List.Forall₂ (EvalStep Ξ Ω M₁) args path ↔ List.Forall₂ (EvalStep Ξ Ω M₂) args path) := by
    intro args
    induction args with
    | nil =>
      intro path _
      rw [List.forall₂_nil_left_iff, List.forall₂_nil_left_iff]
    | cons hd tl ih =>
      intro path hagree
      -- the head segment's own agreement, needed in both directions
      have hhead : ∀ (e : ComputablePlusCal.Expression), hd = Sum.inr e →
          ∀ y ∈ e.freeVars, M₁.lookup y = M₂.lookup y := by
        rintro e rfl y hy
        exact hagree _ (List.mem_cons_self ..) y hy
      have htail : ∀ e, Sum.inr e ∈ tl → ∀ y ∈ e.freeVars, M₁.lookup y = M₂.lookup y :=
        λ e he ↦ hagree e (List.mem_cons_of_mem _ he)
      iff_intro h h
      · cases h with
        | cons hstep hrest =>
          refine List.Forall₂.cons ?_ ((ih _ htail).mp hrest)
          cases hstep with
          | field f => exact EvalStep.field f
          | index hv =>
            apply EvalStep.index
            exact (ExprSemantics.evalLocal (hhead _ rfl)).mp hv
      · cases h with
        | cons hstep hrest =>
          refine List.Forall₂.cons ?_ ((ih _ htail).mpr hrest)
          cases hstep with
          | field f => exact EvalStep.field f
          | index hv =>
            apply EvalStep.index
            exact (ExprSemantics.evalLocal (hhead _ rfl)).mpr hv
  exact step r.args path (λ e he y hy ↦ agree y (Ref.freeVars_of_mem_args he hy))

/-- The one-name case of `congr_of_agree`: memories agreeing away from `inbox` resolve a reference's
path identically, provided the reference does not read `inbox`. -/
theorem Ref.EvalArgs.congr_of_fresh {M₁ M₂ : Memory V} {r : ComputableGuardedPlusCal.Ref}
    {inbox : String} {path : List (PathStep V)}
    (agree : ∀ x ≠ inbox, M₁.lookup x = M₂.lookup x)
    (fresh : inbox ∉ GuardedPlusCal.Ref.freeVars r) :
    Ref.EvalArgs Ξ Ω M₁ r path ↔ Ref.EvalArgs Ξ Ω M₂ r path := by
  refine Ref.EvalArgs.congr_of_agree (λ y hy ↦ agree y ?_)
  rintro rfl
  exact fresh hy

/-- `Ref.EvalArgs.congr_of_fresh` at related states, with the freshness hypothesis in the guarded
shape — vacuous when the process has no mailbox, where the memories agree outright. The `EvalArgs`
counterpart of `relatesTo.eval_iff'`, and what keeps a simulation from having to know whether the
process receives before it can move a resolved path across. -/
theorem relatesTo.evalArgs_iff {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState V}
    (h : σₛ ∼[Ξ, Ω,mbox, pref] σₜ) {r : ComputableGuardedPlusCal.Ref} {path : List (PathStep V)}
    (fresh : ∀ c inbox, mbox = .some (c, inbox) → inbox ∉ GuardedPlusCal.Ref.freeVars r) :
    Ref.EvalArgs Ξ Ω σₛ.mem r path ↔ Ref.EvalArgs Ξ Ω σₜ.mem r path := by
  match mbox with
  | .none => rw [h.mem_eq]
  | .some (c, inbox) => exact Ref.EvalArgs.congr_of_fresh h.mem_agree (fresh c inbox rfl)

/-! ## Transferring a memory update

  `assign` (and, on the source side, `receive`) writes through `Memory.update`. Simulating that step
  means running the same update in the other memory and finding the results still related — which
  holds because the two memories agree at the written name, so they read the same old value, compute
  the same new one, and insert it.
-/

/-- An update that succeeds in one memory succeeds in any memory agreeing with it *at the written
name* — both read the same old value and compute the same new one — and the results then agree
there too. Everywhere else the two results agree exactly where the originals did, which is
`Memory.lookup_update_ne` and needs no hypothesis at all. -/
theorem Memory.update_transfer {M₁ M₂ M₁' : Memory V} {x : String}
    {path : List (PathStep V)} {v : V} (hx : M₁.lookup x = M₂.lookup x)
    (h₁ : ComputableTLAPlus.Memory.update M₁ x path v = .some M₁') :
    ∃ M₂', ComputableTLAPlus.Memory.update M₂ x path v = .some M₂' ∧
      M₁'.lookup x = M₂'.lookup x := by
  obtain ⟨old, new, hold, hnew, rfl⟩ := ComputableTLAPlus.Memory.update_eq_some_iff.mp h₁
  refine ⟨M₂.insert x new,
    ComputableTLAPlus.Memory.update_eq_some_iff.mpr ⟨old, new, ?_, hnew, rfl⟩, ?_⟩
  · rw [← hx]
    exact hold
  · rw [Finmap.lookup_insert _, Finmap.lookup_insert _]

/-- An update touches only the name it writes. What keeps the refinement invariant's *other*
components — the mailbox channel's resolved path, and `inbox`'s own contents — undisturbed by an
`assign` to some third variable. -/
theorem Memory.lookup_update_ne {M M' : Memory V} {x y : String} {path : List (PathStep V)} {v : V}
    (h : ComputableTLAPlus.Memory.update M x path v = .some M') (hy : y ≠ x) :
    M'.lookup y = M.lookup y := by
  obtain ⟨-, -, -, -, rfl⟩ := ComputableTLAPlus.Memory.update_eq_some_iff.mp h
  exact Finmap.lookup_insert_of_ne _ hy

/-- An update fails in one memory exactly when it fails in any memory agreeing at the written name:
both read the same old value and run the same `updatePath` on it. The aborting counterpart of
`Memory.update_transfer`. -/
theorem Memory.update_none_transfer {M₁ M₂ : Memory V} {x : String} {path : List (PathStep V)}
    {v : V} (hlk : M₁.lookup x = M₂.lookup x)
    (h : ComputableTLAPlus.Memory.update M₂ x path v = .none) :
    ComputableTLAPlus.Memory.update M₁ x path v = .none := by
  rw [ComputableTLAPlus.Memory.update_eq_none_iff] at h ⊢
  intro old hold
  exact h old (hlk ▸ hold)

/-- **Transporting the relation across a memory write**, the third of the transport lemmas
(`relatesTo.label_congr` and `.fifo_push` are the other two, in `Guarded2Network/Lemmas/
Relation.lean`; this one lives here because it needs `Ref.EvalArgs.congr_of_fresh`).

Both sides write the same name to the same value, which is what `assign` and `with` each do. The
name must be neither the generated `inbox` — else the target's mailbox contents would move — nor one
the mailbox channel is indexed by — else the key the invariant pins would move out from under it.
Both conditions arrive from `Fresh` already in the guarded shape, so no use site case-splits on
`mbox`. -/
theorem relatesTo.mem_congr {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState V}
    {M₁ M₂ : Memory V} {x : String} (h : σₛ ∼[Ξ, Ω,mbox, pref] σₜ)
    (hbox : ∀ c inbox, mbox = .some (c, inbox) →
      x ≠ inbox ∧ x ∉ GuardedPlusCal.Ref.freeVars c)
    (hs : ∀ y ≠ x, M₁.lookup y = σₛ.mem.lookup y)
    (ht : ∀ y ≠ x, M₂.lookup y = σₜ.mem.lookup y)
    (hx : M₁.lookup x = M₂.lookup x) (l : Option String) :
    (⟨M₁, σₛ.fifos, l⟩ : LocalState V) ∼[Ξ, Ω,mbox, pref] ⟨M₂, σₜ.fifos, l⟩ := by
  -- away from the written name the two new memories agree exactly where the old ones did
  have hagree : ∀ y, (∀ c inbox, mbox = .some (c, inbox) → y ≠ inbox) →
      M₁.lookup y = M₂.lookup y := by
    intro y hy
    by_cases hyx : y = x
    · rwa [hyx]
    · rw [hs y hyx, ht y hyx]
      exact h.mem_agree' y hy
  refine ⟨rfl, ?_⟩
  match mbox with
  | .none =>
    refine ⟨Finmap.ext_lookup λ y ↦ hagree y ?_, h.none_fifo_split⟩
    intro _ _ hm
    nomatch hm
  | .some (c, inbox) =>
    obtain ⟨hxi, hxc⟩ := hbox c inbox rfl
    obtain ⟨cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩ := h.inbox_seq
    refine ⟨λ y hy ↦ hagree y ?_, cpath, sv, vs, ?_, ?_, hseq, hoff, hsplit⟩
    · rintro _ _ ⟨rfl, rfl⟩
      exact hy
    · exact (Ref.EvalArgs.congr_of_fresh hs hxc).mpr hpath
    · rw [LocalState.mem_mk, ht inbox (Ne.symm hxi)]
      exact hinbox

/-! ## Action statements

  `convertActionStmt` maps each of the seven action constructors to its namesake in the target
  language, and the two `Statement.reducing` definitions agree character-for-character on those
  cases (the only differences in the whole `def` are the type name, one comment, and Guarded's extra
  `receive` case). So the semantics is not merely preserved but *definitionally equal*, and one
  `cases … <;> rfl` proves each semantic component.
-/

/-- The one name a statement writes, if any. Needed by `Fresh` below: the refinement invariant pins
*one* resolved channel key, so a statement that overwrote a variable the mailbox channel is indexed
by would move that key out from under it. -/
def Statement.writtenName? {b b' : Bool} :
    ComputableGuardedPlusCal.Statement b b' → Option String
  | .assign r _ => .some r.name
  | .receive _ r _ => .some r.name
  | .with x _ _ _ => .some x
  | _ => .none

/-- What a statement must avoid for the pass's `inbox` not to disturb it: it cannot read `inbox`,
`inbox` cannot be `self` — `print`/`send` read `self` to tag the event they emit, which is a name the
*semantics* reads on its own and so is invisible to a freshness condition stated over the statement's
free variables — it cannot write a name the mailbox channel is indexed by, and it cannot *bind*
`inbox`. All hold of any real compilation: `freshName`'s `$` separator puts `inbox` outside the
source program's namespace entirely.

Stated for every guard class, not just the action one: the last clause exists only for `with`, which
is guard-class, and the block-level refinement needs the same predicate on both halves of a
branch. -/
def Fresh (mbox : Mailbox) {g b : Bool} (S : ComputableGuardedPlusCal.Statement g b) : Prop :=
  ∀ c inbox, mbox = .some (c, inbox) →
    inbox ∉ GuardedPlusCal.Statement.freeVars S ∧ inbox ≠ GuardedPlusCal.selfName ∧
      (∀ x, Statement.writtenName? S = .some x → x ∉ GuardedPlusCal.Ref.freeVars c) ∧
      ∀ x, GuardedPlusCal.Statement.boundName? S = .some x → x ≠ inbox

/-- `assign` and `send` each read one reference and one expression, and `Statement.freeVars` is the
union of the two halves' free variables. Every branch of the two simulation lemmas below splits
`Fresh`'s first component this way, so the split is named once here. -/
theorem fresh_split {x : String} {r : ComputableGuardedPlusCal.Ref} {e : ComputablePlusCal.Expression}
    (h : x ∉ GuardedPlusCal.Ref.freeVars r ∪ Expression.freeVars e) :
    x ∉ GuardedPlusCal.Ref.freeVars r ∧ Expression.FreshIn x e :=
  ⟨λ hr ↦ h (Finset.mem_union_left _ hr), λ he ↦ h (Finset.mem_union_right _ he)⟩

/-- The workhorse behind `action_refines`: an action statement's semantics is closed under
`relatesTo`. Given a target step out of `σₜ` and a source state related to it, the source takes the
*same* step — same trace, results still related.

Phrased on one language's semantics because `convertActionStmt_reducing'` already says the target's
semantics *is* the source's; `action_refines` below is what states the result in the framework's own
terms. Each piece built above is spent here: `eval_iff'` for the statements that evaluate an
expression, `relatesTo.evalArgs_iff` for those that resolve a reference, `Memory.update_transfer`
and `relatesTo.mem_congr` for `assign`, `relatesTo.fifo_push` for `send`, and
`relatesTo.label_congr` for the four that do none of those.

Nothing here splits on `mbox`. Every hypothesis `Fresh` supplies is already guarded by
`mbox = .some (c, inbox)`, and every fact taken off `sim` — `mem_agree'`, `eval_iff'`,
`evalArgs_iff`, `fifo_split` and the transport lemmas — holds in both cases. -/
theorem Statement.reducing_sim {mbox : Mailbox} {pref : ChanKey V → List V} {b : Bool}
    (S : ComputableGuardedPlusCal.Statement false b) (fresh : Fresh mbox S)
    {σₛ σₜ σₜ' : LocalState V} {ε : GuardedPlusCal.Trace V} (sim : σₛ ∼[Ξ, Ω,mbox, pref] σₜ)
    (step : (⟨σₜ, ε, σₜ'⟩ : LocalState V × GuardedPlusCal.Trace V × LocalState V) ∈
      GuardedPlusCal.Statement.reducing Ξ Ω S) :
    ∃ σₛ', σₛ' ∼[Ξ, Ω,mbox, pref] σₜ' ∧
      (⟨σₛ, ε, σₛ'⟩ : LocalState V × GuardedPlusCal.Trace V × LocalState V) ∈
        GuardedPlusCal.Statement.reducing Ξ Ω S := by
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  have hagree : ∀ x, (∀ c inbox, mbox = .some (c, inbox) → x ≠ inbox) →
      M₁.lookup x = σₜ.mem.lookup x := sim.mem_agree'
  -- `print` and `send` read `self`, which the *semantics* reads on its own; `Fresh` says `inbox` is
  -- not it, and that is the only reason the two memories agree there
  have hself : ∀ x, (∀ c inbox, mbox = .some (c, inbox) → inbox ≠ x) →
      M₁.lookup x = σₜ.mem.lookup x :=
    λ x hx ↦ hagree x λ c inbox h ↦ Ne.symm (hx c inbox h)
  have hlabel := sim.label_eq
  cases S with
  | skip =>
    obtain ⟨M, F, rfl, rfl, rfl⟩ := step
    subst hlabel
    exact ⟨⟨M₁, F₁, .none⟩, sim.label_congr .none,
      GuardedPlusCal.Statement.reducing.skip.intro ⟨M₁, F₁, rfl, rfl, rfl⟩⟩
  | goto label =>
    obtain ⟨M, F, rfl, rfl, rfl⟩ := step
    subst hlabel
    exact ⟨⟨M₁, F₁, .some label⟩, sim.label_congr (.some label),
      GuardedPlusCal.Statement.reducing.goto.intro ⟨M₁, F₁, rfl, rfl, rfl⟩⟩
  | print e =>
    obtain ⟨M, F, v, p, rfl, rfl, hv, hp, rfl⟩ := step
    subst hlabel
    refine ⟨⟨M₁, F₁, .none⟩, sim.label_congr .none,
      GuardedPlusCal.Statement.reducing.print.intro ⟨M₁, F₁, v, p, rfl, rfl, ?_, ?_, rfl⟩⟩
    · exact (sim.eval_iff' λ c i h ↦ (fresh c i h).1).mpr hv
    · exact (hself GuardedPlusCal.selfName λ c i h ↦ (fresh c i h).2.1).trans hp
  | assert e =>
    obtain ⟨M, F, rfl, rfl, hv, rfl⟩ := step
    subst hlabel
    refine ⟨⟨M₁, F₁, .none⟩, sim.label_congr .none,
      GuardedPlusCal.Statement.reducing.assert.intro ⟨M₁, F₁, rfl, rfl, ?_, rfl⟩⟩
    exact (sim.eval_iff' λ c i h ↦ (fresh c i h).1).mpr hv
  | multicast c filter => exact step.elim
  | assign r e =>
    obtain ⟨M, F, M', v, rpath, hv, hrpath, hupd, rfl, rfl, rfl⟩ := step
    subst hlabel
    -- `inbox` is read by neither the written reference nor the assigned expression
    have hfr : ∀ c i, mbox = .some (c, i) → i ∉ GuardedPlusCal.Ref.freeVars r :=
      λ c i h ↦ (fresh_split (fresh c i h).1).1
    -- and the name written is neither `inbox` nor one the mailbox channel is indexed by
    have hbox : ∀ c i, mbox = .some (c, i) →
        r.name ≠ i ∧ r.name ∉ GuardedPlusCal.Ref.freeVars c := by
      intro c i h
      refine ⟨?_, (fresh c i h).2.2.1 r.name rfl⟩
      rintro rfl
      exact hfr c _ h (Finset.mem_union_left _ (Finset.mem_singleton_self _))
    -- so the same update runs in the source memory, the two agreeing at the name it writes
    obtain ⟨M₁', hupd₁, hx⟩ :=
      Memory.update_transfer (hagree r.name λ c i h ↦ (hbox c i h).1).symm hupd
    refine ⟨⟨M₁', F₁, .none⟩, ?_,
      GuardedPlusCal.Statement.reducing.assign.intro
          ⟨M₁, F₁, M₁', v, rpath, ?_, ?_, hupd₁, rfl, rfl, rfl⟩⟩
    · exact sim.mem_congr hbox (λ y hy ↦ Memory.lookup_update_ne hupd₁ hy)
        (λ y hy ↦ Memory.lookup_update_ne hupd hy) hx.symm .none
    · exact (sim.eval_iff' λ c i h ↦ (fresh_split (fresh c i h).1).2).mpr hv
    · exact (sim.evalArgs_iff hfr).mpr hrpath
  | send c e =>
    obtain ⟨M, F, v, cpath, vs, p, hv, hcpath, hlk, hp, rfl, rfl, rfl⟩ := step
    subst hlabel
    -- the sent-to queue in the source is the target's behind that key's prefix, whichever of the
    -- two clauses supplies it — a `send` appends at the back, so no case on whether the channel
    -- sent to is the one this process receives from
    obtain ⟨ws, hlk₁⟩ := sim.fifo_lookup hlk
    refine ⟨⟨M₁, F₁.insert (c.name, cpath) ((ws ++ vs).concat v), .none⟩,
      sim.fifo_push hlk hlk₁ v .none,
      GuardedPlusCal.Statement.reducing.send.intro
          ⟨M₁, F₁, v, cpath, ws ++ vs, p, ?_, ?_, hlk₁, ?_, rfl, rfl, rfl⟩⟩
    · exact (sim.eval_iff' λ c' i h ↦ (fresh_split (fresh c' i h).1).2).mpr hv
    · exact (sim.evalArgs_iff λ c' i h ↦ (fresh_split (fresh c' i h).1).1).mpr hcpath
    · exact (hself GuardedPlusCal.selfName λ c' i h ↦ (fresh c' i h).2.1).trans hp

/-- The aborting counterpart of `reducing'_sim`, and the simpler statement: an abort emits nothing,
so the source aborts on the *same* trace rather than on a prefix of the target's. Each constructor's
abort disjuncts transfer one by one — a failed evaluation stays failed (`eval_iff'`), an unresolvable
index path stays unresolvable, a missing FIFO stays missing (`relatesTo.fifo_lookup_none`), and a
failed update stays failed. -/
theorem Statement.aborting_sim {mbox : Mailbox} {pref : ChanKey V → List V} {b : Bool}
    (S : ComputableGuardedPlusCal.Statement false b) (fresh : Fresh mbox S)
    {σₛ σₜ : LocalState V} {ε : GuardedPlusCal.Trace V} (sim : σₛ ∼[Ξ, Ω,mbox, pref] σₜ)
    (step : (⟨σₜ, ε⟩ : LocalState V × GuardedPlusCal.Trace V) ∈
      GuardedPlusCal.Statement.aborting Ξ Ω S) :
    (⟨σₛ, ε⟩ : LocalState V × GuardedPlusCal.Trace V) ∈
      GuardedPlusCal.Statement.aborting Ξ Ω S := by
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  have hagree : ∀ x, (∀ c inbox, mbox = .some (c, inbox) → x ≠ inbox) →
      M₁.lookup x = σₜ.mem.lookup x := sim.mem_agree'
  -- an expression the statement reads has no value in one memory exactly when it has none in
  -- the other
  have habort : ∀ {e : ComputablePlusCal.Expression},
      (∀ c i, mbox = .some (c, i) → Expression.FreshIn i e) →
        ExprSemantics.Aborts Ξ Ω σₜ.mem e → ExprSemantics.Aborts Ξ Ω M₁ e :=
    λ hfe hab ⟨v, hv⟩ ↦ hab ⟨v, (sim.eval_iff' hfe).mp hv⟩
  -- and likewise for a reference's index path
  have hpaths : ∀ {r : ComputableGuardedPlusCal.Ref},
      (∀ c i, mbox = .some (c, i) → i ∉ GuardedPlusCal.Ref.freeVars r) →
      GuardedPlusCal.Ref.pathAborts Ξ Ω σₜ.mem r → GuardedPlusCal.Ref.pathAborts Ξ Ω M₁ r := by
    rintro r hfr ⟨e, hmem, hab⟩
    refine ⟨e, hmem, habort ?_ hab⟩
    obtain ⟨seg, hseg, hval⟩ := List.mem_filterMap.mp hmem
    match seg, hval with
    | .inr e', rfl => exact λ c i h hx ↦ hfr c i h (Ref.freeVars_of_mem_args hseg hx)
  have hlabel := sim.label_eq
  cases S with
  | skip => exact step.elim
  | goto label => exact step.elim
  | multicast c filter => exact step.elim
  | print e =>
    obtain ⟨M, F, hab, rfl, rfl⟩ := step
    subst hlabel
    exact ⟨M₁, F₁, habort (λ c i h ↦ (fresh c i h).1) hab, rfl, rfl⟩
  | assert e =>
    rcases step with ⟨M, F, hab, rfl, rfl⟩ | ⟨M, F, v, hv, hvv, rfl, rfl⟩
    · subst hlabel; exact .inl ⟨M₁, F₁, habort (λ c i h ↦ (fresh c i h).1) hab, rfl, rfl⟩
    · subst hlabel
      exact .inr ⟨M₁, F₁, v, hv, (sim.eval_iff' λ c i h ↦ (fresh c i h).1).mpr hvv, rfl, rfl⟩
  | assign r e =>
    have hfr : ∀ c i, mbox = .some (c, i) → i ∉ GuardedPlusCal.Ref.freeVars r :=
      λ c i h ↦ (fresh_split (fresh c i h).1).1
    have hfe : ∀ c i, mbox = .some (c, i) → Expression.FreshIn i e :=
      λ c i h ↦ (fresh_split (fresh c i h).1).2
    have hrname : ∀ c i, mbox = .some (c, i) → r.name ≠ i := by
      intro c i h
      rintro rfl
      exact hfr c _ h (Finset.mem_union_left _ (Finset.mem_singleton_self _))
    rcases step with ((⟨M, F, hmem, rfl, rfl⟩ | ⟨M, F, hab, rfl, rfl⟩) | ⟨M, F, hab, rfl, rfl⟩) |
      ⟨M, F, v, rpath, hv, hrpath, hupd, rfl, rfl⟩
    · subst hlabel
      refine .inl (.inl (.inl ⟨M₁, F₁, ?_, rfl, rfl⟩))
      rw [← Finmap.lookup_isSome, hagree r.name hrname, Finmap.lookup_isSome]
      exact hmem
    · subst hlabel; exact .inl (.inl (.inr ⟨M₁, F₁, habort hfe hab, rfl, rfl⟩))
    · subst hlabel; exact .inl (.inr ⟨M₁, F₁, hpaths hfr hab, rfl, rfl⟩)
    · subst hlabel
      refine .inr ⟨M₁, F₁, v, rpath, (sim.eval_iff' hfe).mpr hv, ?_, ?_, rfl, rfl⟩
      · exact (sim.evalArgs_iff hfr).mpr hrpath
      · exact Memory.update_none_transfer (hagree r.name hrname) hupd
  | send c e =>
    have hfc : ∀ c' i, mbox = .some (c', i) → i ∉ GuardedPlusCal.Ref.freeVars c :=
      λ c' i h ↦ (fresh_split (fresh c' i h).1).1
    have hfe : ∀ c' i, mbox = .some (c', i) → Expression.FreshIn i e :=
      λ c' i h ↦ (fresh_split (fresh c' i h).1).2
    rcases step with (⟨M, F, hab, rfl, rfl⟩ | ⟨M, F, hab, rfl, rfl⟩) |
      ⟨M, F, cpath, hcpath, hlk, rfl, rfl⟩
    · subst hlabel; exact .inl (.inl ⟨M₁, F₁, habort hfe hab, rfl, rfl⟩)
    · subst hlabel; exact .inl (.inr ⟨M₁, F₁, hpaths hfc hab, rfl, rfl⟩)
    -- the FIFO the channel resolves to is absent in the target exactly when it is in the source
    · subst hlabel
      exact .inr ⟨M₁, F₁, cpath, (sim.evalArgs_iff hfc).mpr hcpath,
        sim.fifo_lookup_none hlk, rfl, rfl⟩

/-! ## The guard class

  `Statement.reducing_sim` covers the action constructors. The two guard constructors the pass
  copies across — `with` and `await` — need the same fact, and get their own lemma rather than a
  generalization of that one: the *third* guard constructor is `receive`, which emphatically does
  not preserve `relatesTo`, and a statement quantified over the class would have to carve it out by
  hand at every use.
-/

/-- `Statement.reducing_sim` for the guard class. `await` reads an expression and changes nothing;
`with` additionally binds a name, and the binding is invisible to the invariant exactly because
`Fresh` says the bound name is neither `inbox` nor read by the mailbox channel's index path. -/
theorem Statement.guardReducing'_sim {mbox : Mailbox} {pref : ChanKey V → List V}
    (S : ComputableGuardedPlusCal.Statement true false)
    (notRecv : ∀ c r coe, S ≠ .receive c r coe) (fresh : Fresh mbox S)
    {σₛ σₜ σₜ' : LocalState V} {ε : GuardedPlusCal.Trace V} (sim : σₛ ∼[Ξ, Ω,mbox, pref] σₜ)
    (step : (⟨σₜ, ε, σₜ'⟩ : LocalState V × GuardedPlusCal.Trace V × LocalState V) ∈
      GuardedPlusCal.Statement.reducing Ξ Ω S) :
    ∃ σₛ', σₛ' ∼[Ξ, Ω,mbox, pref] σₜ' ∧
      (⟨σₛ, ε, σₛ'⟩ : LocalState V × GuardedPlusCal.Trace V × LocalState V) ∈
        GuardedPlusCal.Statement.reducing Ξ Ω S := by
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  have hagree : ∀ x, (∀ c inbox, mbox = .some (c, inbox) → x ≠ inbox) →
      M₁.lookup x = σₜ.mem.lookup x := sim.mem_agree'
  have hlabel := sim.label_eq
  cases S with
  | «with» x ann bound e =>
    obtain ⟨M, F, v, hv, hnone, rfl, rfl, hb⟩ := step
    subst hlabel
    -- the binder is neither `inbox` nor a name the mailbox channel's index path reads
    have hbox : ∀ c i, mbox = .some (c, i) → x ≠ i ∧ x ∉ GuardedPlusCal.Ref.freeVars c :=
      λ c i h ↦ ⟨(fresh c i h).2.2.2 x rfl, (fresh c i h).2.2.1 x rfl⟩
    have hnone₁ : Finmap.lookup x M₁ = .none :=
      (hagree x λ c i h ↦ (hbox c i h).1).trans hnone
    have hv₁ : ExprSemantics.Eval Ξ Ω M₁ e v := (sim.eval_iff' λ c i h ↦ (fresh c i h).1).mpr hv
    -- so the same value is bound in both memories and neither half of the invariant moves
    have hrel : ∀ u : V, (⟨Finmap.insert x u M₁, F₁, .none⟩ : LocalState V) ∼[Ξ, Ω,mbox, pref]
        ⟨Finmap.insert x u M, F, .none⟩ := by
      refine λ u ↦ sim.mem_congr hbox (λ y hy ↦ Finmap.lookup_insert_of_ne _ hy)
        (λ y hy ↦ Finmap.lookup_insert_of_ne _ hy) ?_ .none
      rw [Finmap.lookup_insert, Finmap.lookup_insert]
    cases bound with
    | true =>
      subst hb
      exact ⟨⟨Finmap.insert x v M₁, F₁, .none⟩, hrel v,
        GuardedPlusCal.Statement.reducing.with.intro
          ⟨M₁, F₁, v, hv₁, hnone₁, rfl, rfl, rfl⟩⟩
    | false =>
      obtain ⟨u, hu, rfl⟩ := hb
      exact ⟨⟨Finmap.insert x u M₁, F₁, .none⟩, hrel u,
        GuardedPlusCal.Statement.reducing.with.intro
          ⟨M₁, F₁, v, hv₁, hnone₁, rfl, rfl, ⟨u, hu, rfl⟩⟩⟩
  | await e =>
    obtain ⟨M, F, rfl, rfl, hv, rfl⟩ := step
    subst hlabel
    exact ⟨⟨M₁, F₁, .none⟩, sim.label_congr .none,
      GuardedPlusCal.Statement.reducing.await.intro
          ⟨M₁, F₁, rfl, rfl, (sim.eval_iff' λ c i h ↦ (fresh c i h).1).mpr hv, rfl⟩⟩
  | receive c r coe =>
    absurd (rfl : GuardedPlusCal.Statement.receive c r coe = .receive c r coe)
    exact notRecv c r coe

/-- `Statement.aborting_sim` for the guard class. Both constructors abort on exactly two things —
the expression having no value, or having one of the wrong shape — and both transfer by
`relatesTo.eval_iff'`, in the aborting case through `ExprSemantics.aborts_congr`. -/
theorem Statement.guardAborting'_sim {mbox : Mailbox} {pref : ChanKey V → List V}
    (S : ComputableGuardedPlusCal.Statement true false)
    (notRecv : ∀ c r coe, S ≠ .receive c r coe) (fresh : Fresh mbox S)
    {σₛ σₜ : LocalState V} {ε : GuardedPlusCal.Trace V} (sim : σₛ ∼[Ξ, Ω,mbox, pref] σₜ)
    (step : (⟨σₜ, ε⟩ : LocalState V × GuardedPlusCal.Trace V) ∈
      GuardedPlusCal.Statement.aborting Ξ Ω S) :
    (⟨σₛ, ε⟩ : LocalState V × GuardedPlusCal.Trace V) ∈
      GuardedPlusCal.Statement.aborting Ξ Ω S := by
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  have hlabel := sim.label_eq
  cases S with
  | «with» x ann bound e =>
    have heval {v : V} : ExprSemantics.Eval Ξ Ω M₁ e v ↔ ExprSemantics.Eval Ξ Ω σₜ.mem e v :=
      sim.eval_iff' λ c i h ↦ (fresh c i h).1
    refine GuardedPlusCal.Statement.aborting.with.intro ?_
    rcases step with ⟨M, F, ha, rfl, rfl⟩ | ⟨M, F, v, hv, rfl, rfl, hset⟩
    · subst hlabel; exact .inl ⟨M₁, F₁, (ExprSemantics.aborts_congr λ _ ↦ heval).mpr ha, rfl, rfl⟩
    · subst hlabel; exact .inr ⟨M₁, F₁, v, heval.mpr hv, rfl, rfl, hset⟩
  | await e =>
    have heval {v : V} : ExprSemantics.Eval Ξ Ω M₁ e v ↔ ExprSemantics.Eval Ξ Ω σₜ.mem e v :=
      sim.eval_iff' λ c i h ↦ (fresh c i h).1
    refine GuardedPlusCal.Statement.aborting.await.intro ?_
    rcases step with ⟨M, F, ha, rfl, rfl⟩ | ⟨M, F, v, hbool, hv, rfl, rfl⟩
    · subst hlabel; exact .inl ⟨M₁, F₁, (ExprSemantics.aborts_congr λ _ ↦ heval).mpr ha, rfl, rfl⟩
    · subst hlabel; exact .inr ⟨M₁, F₁, v, hbool, heval.mpr hv, rfl, rfl⟩
  | receive c r coe =>
    absurd (rfl : GuardedPlusCal.Statement.receive c r coe = .receive c r coe)
    exact notRecv c r coe

theorem convertActionStmt_reducing' {b : Bool} (S : ComputableGuardedPlusCal.Statement false b) :
    NetworkPlusCal.Statement.reducing (V := V) Ξ Ω (convertActionStmt S) =
      GuardedPlusCal.Statement.reducing (V := V) Ξ Ω S := by
  cases S <;> rfl

theorem convertActionStmt_aborting' {b : Bool} (S : ComputableGuardedPlusCal.Statement false b) :
    NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (convertActionStmt S) =
      GuardedPlusCal.Statement.aborting (V := V) Ξ Ω S := by
  cases S <;> rfl

omit [ExprSemantics V] in
theorem convertActionStmt_diverging' {b : Bool} (S : ComputableGuardedPlusCal.Statement false b) :
    NetworkPlusCal.Statement.diverging (V := V) (convertActionStmt S) =
      GuardedPlusCal.Statement.diverging (V := V) S := by
  cases S <;> rfl

/-! ## The guard-class statements the two languages share

  `with` and `await` exist in both languages with the same fields and the same meaning. There is no
  conversion function to state this against — one cannot exist, `receive` having no image — and
  `stepStatement` writes the target constructor out directly. So what the refinement needs is not
  that a conversion preserves semantics but that the two constructors *denote the same relation*,
  which they do on the nose.

  Six `rfl`s rather than one lemma over a conversion, and that is the honest shape: the fact is
  per-constructor, and the class of statements it covers is not the image of any function.
-/

theorem with_reducing'_eq {x : String} {ann : ComputableTLAPlus.Typ} {bound : Bool}
    {e : ComputablePlusCal.Expression} :
    NetworkPlusCal.Statement.reducing (V := V) Ξ Ω (.with x ann bound e) =
      GuardedPlusCal.Statement.reducing (V := V) Ξ Ω (.with x ann bound e) :=
  rfl

@[inherit_doc with_reducing'_eq]
theorem with_aborting'_eq {x : String} {ann : ComputableTLAPlus.Typ} {bound : Bool}
    {e : ComputablePlusCal.Expression} :
    NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (.with x ann bound e) =
      GuardedPlusCal.Statement.aborting (V := V) Ξ Ω (.with x ann bound e) :=
  rfl

omit [ExprSemantics V] in
@[inherit_doc with_reducing'_eq]
theorem with_diverging'_eq {x : String} {ann : ComputableTLAPlus.Typ} {bound : Bool}
    {e : ComputablePlusCal.Expression} :
    NetworkPlusCal.Statement.diverging (V := V) (.with x ann bound e) =
      GuardedPlusCal.Statement.diverging (V := V) (.with x ann bound e) :=
  rfl

@[inherit_doc with_reducing'_eq]
theorem await_reducing'_eq {e : ComputablePlusCal.Expression} :
    NetworkPlusCal.Statement.reducing (V := V) Ξ Ω (.await e) =
      GuardedPlusCal.Statement.reducing (V := V) Ξ Ω (.await e) :=
  rfl

@[inherit_doc with_reducing'_eq]
theorem await_aborting'_eq {e : ComputablePlusCal.Expression} :
    NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (.await e) =
      GuardedPlusCal.Statement.aborting (V := V) Ξ Ω (.await e) :=
  rfl

omit [ExprSemantics V] in
@[inherit_doc with_reducing'_eq]
theorem await_diverging'_eq {e : ComputablePlusCal.Expression} :
    NetworkPlusCal.Statement.diverging (V := V) (.await e) =
      GuardedPlusCal.Statement.diverging (V := V) (.await e) :=
  rfl

/-- `convertActionStmt` refines, statement by statement, at this pass's
own trace relation (equality — `Guarded2Network/Lemmas/Trace.lean`).

The three components come out very differently. `terminating` is the whole of `reducing'_sim`;
`aborting` is `aborting'_sim` with the `≼[Rτ]` obligation trivial, an abort emitting the empty
trace; `diverging` is vacuous, a statement having no non-terminating semantics at all — divergence
enters only at the block and algorithm layers. -/
theorem action_refines {mbox : Mailbox} {pref : ChanKey V → List V} {b : Bool}
    (S : ComputableGuardedPlusCal.Statement false b) (fresh : Fresh mbox S) :
    StrongRefinement (relatesTo (V := V) Ξ Ω mbox pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.reducing Ξ Ω S) (GuardedPlusCal.Statement.aborting Ξ Ω S)
      (GuardedPlusCal.Statement.diverging S)
      (NetworkPlusCal.Statement.reducing Ξ Ω (convertActionStmt S))
      (NetworkPlusCal.Statement.aborting Ξ Ω (convertActionStmt S))
      (NetworkPlusCal.Statement.diverging (convertActionStmt S)) ∅ ∅ := by
  have hterm : StrongRefinement.Terminating (relatesTo (V := V) Ξ Ω mbox pref)
      (relatesTo Ξ Ω mbox pref)
      (instTrace (V := V)).Rτ (GuardedPlusCal.Statement.reducing Ξ Ω S)
      (GuardedPlusCal.Statement.aborting Ξ Ω S) (GuardedPlusCal.Statement.reducing Ξ Ω S) := by
    intro σₜ σₜ' ε σₛ sim step
    obtain ⟨σₛ', hrel, hstep⟩ := Statement.reducing_sim S fresh sim step
    refines_match σₛ', ε
    · exact hrel
    · trace_rel
    · exact hstep
  have habort : StrongRefinement.Aborting (relatesTo (V := V) Ξ Ω mbox pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.aborting Ξ Ω S) (GuardedPlusCal.Statement.aborting Ξ Ω S) := by
    intro σₜ ε σₛ sim step
    refines_abort ε
    · trace_pfx
    · exact Statement.aborting_sim S fresh sim step
  -- the target cannot diverge, so the framework supplies the third component itself
  rw [convertActionStmt_reducing', convertActionStmt_aborting', convertActionStmt_diverging',
    GuardedPlusCal.Statement.diverging_eq_empty]
  exact StrongRefinement.ofNonDiverging (relatesTo (V := V) Ξ Ω mbox pref) hterm habort

/-- A `with` or an `await` refines itself, the two languages'
constructors denoting the same relation (`with_reducing'_eq` and friends). Stated on the *source*
semantics for the same reason `action_refines` is stated through `convertActionStmt`: the target's
semantics is the source's, and saying so once keeps the two languages out of the proof. -/
theorem guard_refines {mbox : Mailbox} {pref : ChanKey V → List V}
    (S : ComputableGuardedPlusCal.Statement true false)
    (notRecv : ∀ c r coe, S ≠ .receive c r coe) (fresh : Fresh mbox S) :
    StrongRefinement (relatesTo (V := V) Ξ Ω mbox pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.reducing Ξ Ω S) (GuardedPlusCal.Statement.aborting Ξ Ω S)
      (GuardedPlusCal.Statement.diverging S)
      (GuardedPlusCal.Statement.reducing Ξ Ω S) (GuardedPlusCal.Statement.aborting Ξ Ω S) ∅ ∅ ∅ := by
  refine StrongRefinement.ofNonDiverging (relatesTo (V := V) Ξ Ω mbox pref) ?_ ?_
  · intro σₜ σₜ' ε σₛ sim step
    obtain ⟨σₛ', hrel, hstep⟩ := Statement.guardReducing'_sim S notRecv fresh sim step
    refines_match σₛ', ε
    · exact hrel
    · trace_rel
    · exact hstep
  · intro σₜ ε σₛ sim step
    refines_abort ε
    · trace_pfx
    · exact Statement.guardAborting'_sim S notRecv fresh sim step

end Guarded2Network

end
