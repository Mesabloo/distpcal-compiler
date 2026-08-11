module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Relation
public import Guarded2Network.Lemmas.Trace

@[expose] public section

/-!
  Statement-level refinement: what `Guarded2Network` does to a single action statement, and the two
  transfer lemmas every later proof leans on.

  **Evaluation transfer (plan D1).** The pass introduces exactly one name, `inbox`, and it is fresh
  (`freshName`'s `$` separator makes collision with a source name impossible). So any source
  expression evaluates the same in the target's memory, which differs only at `inbox`. Prior art
  re-derives that fact inline at least eight times, as a five-line `rw`/`apply eval_ext`/
  `List.singleton_disjoint` sandwich. Here it is `relatesTo.eval_iff`, once.

  **Reference arguments (plan D2).** A reference's index path is evaluated by a `List.Forall₂` over
  `EvalStep`, and pushing the transfer under it is what drove prior art's repeated
  `List.forall₂_iff_forall₂_attach`/`attach` gymnastics. Naming that relation — `Ref.EvalArgs` —
  and giving it its own congruence lemma removes the nesting from view entirely.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Expression Memory PathStep)
open GuardedPlusCal (ChanKey EvalStep LocalState')

variable {V : Type} [ExprSemantics V]

/-! ## D1 — evaluation transfer -/

/-- Binding a name the expression cannot read leaves its value alone. The one-name case of
`ExprSemantics.evalLocal`, which is the only case the pass ever needs: it introduces `inbox` and
nothing else. -/
theorem eval_insert_of_fresh {M : Memory V} {x : String} {v' v : V}
    {e : ComputablePlusCal.Expression} (fresh : Expression.FreshIn x e) :
    ((M.insert x v') ⊢ e ⇒ v) ↔ (M ⊢ e ⇒ v) := by
  apply ExprSemantics.evalLocal
  intro y hy
  apply Finmap.lookup_insert_of_ne _
  rintro rfl
  exact fresh hy

/-- Related states evaluate a source expression to the same values, provided the expression does
not mention `inbox` — which no source expression does, `inbox` being freshly generated. -/
theorem relatesTo.eval_iff {c : ComputableGuardedPlusCal.Ref} {inbox : String}
    {pref : ChanKey V → List V}
    {σₛ σₜ : LocalState' V} (h : σₛ ∼[.some (c, inbox), pref] σₜ)
    {e : ComputablePlusCal.Expression} {v : V} (fresh : Expression.FreshIn inbox e) :
    ((σₛ.mem ⊢ e ⇒ v)) ↔ ((σₜ.mem ⊢ e ⇒ v)) := by
  apply ExprSemantics.evalLocal
  intro y hy
  apply h.mem_agree
  rintro rfl
  exact fresh hy

/-- The same for a process that receives nothing: there the memories are equal outright and the
freshness hypothesis has nothing to say. -/
theorem relatesTo.eval_iff_none {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[.none, pref] σₜ)
    {e : ComputablePlusCal.Expression} {v : V} :
    ((σₛ.mem ⊢ e ⇒ v)) ↔ ((σₜ.mem ⊢ e ⇒ v)) := by
  rw [h.mem_eq]

/-- Both cases at once, with the freshness hypothesis stated so that it is vacuous when there is no
mailbox — the form a lemma quantified over an arbitrary `mbox` needs. -/
theorem relatesTo.eval_iff' {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[mbox, pref] σₜ)
    {e : ComputablePlusCal.Expression} {v : V}
    (fresh : ∀ c inbox, mbox = .some (c, inbox) → Expression.FreshIn inbox e) :
    ((σₛ.mem ⊢ e ⇒ v)) ↔ ((σₜ.mem ⊢ e ⇒ v)) := by
  match mbox with
  | .none => exact h.eval_iff_none
  | .some (c, inbox) => exact h.eval_iff (fresh c inbox rfl)

/-! ## D2 — reference arguments -/

/-- A reference's index path, evaluated. Named, rather than left as the raw `List.Forall₂` it
unfolds to, so that transferring it between memories is one lemma about `EvalArgs` instead of a
`Forall₂`-induction at every use site. -/
abbrev Ref.EvalArgs (M : Memory V) (r : ComputableGuardedPlusCal.Ref)
    (path : List (PathStep V)) : Prop :=
  List.Forall₂ (EvalStep M) r.args path

/-- A path resolves to at most one value — `EvalStep.path_inj`, at the named relation. -/
theorem Ref.EvalArgs.inj {M : Memory V} {r : ComputableGuardedPlusCal.Ref}
    {path path' : List (PathStep V)} (h : Ref.EvalArgs M r path) (h' : Ref.EvalArgs M r path') :
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

/-- Memories agreeing on everything a reference *reads* resolve its path identically. This is D2's
point: the `List.Forall₂` nesting is discharged once, here, and no later proof sees it.

Stated over the names read rather than over a single excepted name, because that is the form a
*block* needs — a block writes one name per statement, so "all but one" is never the shape on offer
past the first step. `congr_of_fresh` below is the one-name case. -/
theorem Ref.EvalArgs.congr_of_agree {M₁ M₂ : Memory V} {r : ComputableGuardedPlusCal.Ref}
    {path : List (PathStep V)}
    (agree : ∀ y ∈ GuardedPlusCal.Ref.freeVars r, M₁.lookup y = M₂.lookup y) :
    Ref.EvalArgs M₁ r path ↔ Ref.EvalArgs M₂ r path := by
  unfold Ref.EvalArgs
  have step : ∀ (args : List (String ⊕ ComputablePlusCal.Expression))
      (path : List (PathStep V)),
      (∀ e, Sum.inr e ∈ args → ∀ y ∈ e.freeVars, M₁.lookup y = M₂.lookup y) →
      (List.Forall₂ (EvalStep M₁) args path ↔ List.Forall₂ (EvalStep M₂) args path) := by
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
    Ref.EvalArgs M₁ r path ↔ Ref.EvalArgs M₂ r path := by
  refine Ref.EvalArgs.congr_of_agree (λ y hy ↦ agree y ?_)
  rintro rfl
  exact fresh hy

/-- `Ref.EvalArgs.congr_of_fresh` at related states, with the freshness hypothesis in the guarded
shape — vacuous when the process has no mailbox, where the memories agree outright. The `EvalArgs`
counterpart of `relatesTo.eval_iff'`, and what keeps a simulation from having to know whether the
process receives before it can move a resolved path across. -/
theorem relatesTo.evalArgs_iff {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    (h : σₛ ∼[mbox, pref] σₜ) {r : ComputableGuardedPlusCal.Ref} {path : List (PathStep V)}
    (fresh : ∀ c inbox, mbox = .some (c, inbox) → inbox ∉ GuardedPlusCal.Ref.freeVars r) :
    Ref.EvalArgs σₛ.mem r path ↔ Ref.EvalArgs σₜ.mem r path := by
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
theorem relatesTo.mem_congr {mbox : Mailbox} {pref : ChanKey V → List V} {σₛ σₜ : LocalState' V}
    {M₁ M₂ : Memory V} {x : String} (h : σₛ ∼[mbox, pref] σₜ)
    (hbox : ∀ c inbox, mbox = .some (c, inbox) →
      x ≠ inbox ∧ x ∉ GuardedPlusCal.Ref.freeVars c)
    (hs : ∀ y ≠ x, M₁.lookup y = σₛ.mem.lookup y)
    (ht : ∀ y ≠ x, M₂.lookup y = σₜ.mem.lookup y)
    (hx : M₁.lookup x = M₂.lookup x) (l : Option String) :
    (⟨M₁, σₛ.fifos, l⟩ : LocalState' V) ∼[mbox, pref] ⟨M₂, σₜ.fifos, l⟩ := by
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
    · rw [LocalState'.mem_mk, ht inbox (Ne.symm hxi)]
      exact hinbox

/-! ## D4 — action statements

  `convertActionStmt` maps each of the seven action constructors to its namesake in the target
  language, and the two `Statement.reducing` definitions agree character-for-character on those
  cases (the only differences in the whole `def` are the type name, one comment, and Guarded's extra
  `receive` case). So the semantics is not merely preserved but *definitionally equal*, and the
  seven-lemma port prior art writes collapses to one `cases … <;> rfl` per semantic component.
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
theorem Statement.reducing'_sim {mbox : Mailbox} {pref : ChanKey V → List V} {b : Bool}
    (S : ComputableGuardedPlusCal.Statement false b) (fresh : Fresh mbox S)
    {σₛ σₜ σₜ' : LocalState' V} {ε : GuardedPlusCal.Trace V} (sim : σₛ ∼[mbox, pref] σₜ)
    (step : (⟨σₜ, ε, σₜ'⟩ : LocalState' V × GuardedPlusCal.Trace V × LocalState' V) ∈
      GuardedPlusCal.Statement.reducing' S) :
    ∃ σₛ', σₛ' ∼[mbox, pref] σₜ' ∧
      (⟨σₛ, ε, σₛ'⟩ : LocalState' V × GuardedPlusCal.Trace V × LocalState' V) ∈
        GuardedPlusCal.Statement.reducing' S := by
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  obtain ⟨M₂, F₂, l₂⟩ := σₜ
  obtain ⟨M₂', F₂', l₂'⟩ := σₜ'
  have hagree : ∀ x, (∀ c inbox, mbox = .some (c, inbox) → x ≠ inbox) →
      M₁.lookup x = M₂.lookup x := sim.mem_agree'
  -- `print` and `send` read `self`, which the *semantics* reads on its own; `Fresh` says `inbox` is
  -- not it, and that is the only reason the two memories agree there
  have hself : ∀ x, (∀ c inbox, mbox = .some (c, inbox) → inbox ≠ x) →
      M₁.lookup x = M₂.lookup x :=
    λ x hx ↦ hagree x λ c inbox h ↦ Ne.symm (hx c inbox h)
  have hlabel := sim.label_eq
  simp only [LocalState'.label_mk] at hlabel
  cases S with
  | skip =>
    obtain ⟨σ', hl, ⟨M, F, hM, hσ', hε⟩, hpost, rfl⟩ := step
    injection hM with hM hF
    subst hM; subst hF; subst hσ'; subst hε
    injection hpost with hM' hF'
    subst hM'; subst hF'
    exact ⟨⟨M₁, F₁, .none⟩, sim.label_congr .none,
      ⟨.running M₁ F₁, hlabel.trans hl,
        GuardedPlusCal.Statement.reducing.skip.intro ⟨M₁, F₁, rfl, rfl, rfl⟩, rfl, rfl⟩⟩
  | goto label =>
    obtain ⟨σ', hl, ⟨M, F, hM, hσ', hε⟩, l'', hpost, rfl⟩ := step
    injection hM with hM hF
    subst hM; subst hF; subst hε
    rw [hσ'] at hpost
    injection hpost with hM' hF' hl''
    subst hM'; subst hF'; subst hl''
    exact ⟨⟨M₁, F₁, .some label⟩, sim.label_congr (.some label),
      ⟨.done M₁ F₁ label, hlabel.trans hl,
        GuardedPlusCal.Statement.reducing.goto.intro ⟨M₁, F₁, rfl, rfl, rfl⟩, label, rfl, rfl⟩⟩
  | print e =>
    obtain ⟨σ', hl, ⟨M, F, v, p, hM, hσ', hv, hp, hε⟩, hpost, rfl⟩ := step
    injection hM with hM hF
    subst hM; subst hF; subst hσ'
    injection hpost with hM' hF'
    subst hM'; subst hF'; subst hε
    refine ⟨⟨M₁, F₁, .none⟩, sim.label_congr .none,
      ⟨.running M₁ F₁, hlabel.trans hl,
        GuardedPlusCal.Statement.reducing.print.intro ⟨M₁, F₁, v, p, rfl, rfl, ?_, ?_, rfl⟩,
        rfl, rfl⟩⟩
    · exact (sim.eval_iff' λ c i h ↦ (fresh c i h).1).mpr hv
    · exact (hself GuardedPlusCal.selfName λ c i h ↦ (fresh c i h).2.1).trans hp
  | assert e =>
    obtain ⟨σ', hl, ⟨M, F, hM, hσ', hv, hε⟩, hpost, rfl⟩ := step
    injection hM with hM hF
    subst hM; subst hF; subst hσ'
    injection hpost with hM' hF'
    subst hM'; subst hF'; subst hε
    refine ⟨⟨M₁, F₁, .none⟩, sim.label_congr .none,
      ⟨.running M₁ F₁, hlabel.trans hl,
        GuardedPlusCal.Statement.reducing.assert.intro ⟨M₁, F₁, rfl, rfl, ?_, rfl⟩, rfl, rfl⟩⟩
    exact (sim.eval_iff' λ c i h ↦ (fresh c i h).1).mpr hv
  | multicast c filter =>
    obtain ⟨σ', -, hmem, -⟩ := step
    exact hmem.elim
  | assign r e =>
    obtain ⟨σ', hl, ⟨M, F, M', v, rpath, hv, hrpath, hupd, hM, hσ', hε⟩, hpost, rfl⟩ := step
    injection hM with hM hF
    subst hM; subst hF; subst hσ'
    injection hpost with hM' hF'
    subst hM'; subst hF'; subst hε
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
      ⟨.running M₁' F₁, hlabel.trans hl,
        GuardedPlusCal.Statement.reducing.assign.intro
          ⟨M₁, F₁, M₁', v, rpath, ?_, ?_, hupd₁, rfl, rfl, rfl⟩, rfl, rfl⟩⟩
    · exact sim.mem_congr hbox (λ y hy ↦ Memory.lookup_update_ne hupd₁ hy)
        (λ y hy ↦ Memory.lookup_update_ne hupd hy) hx.symm .none
    · exact (sim.eval_iff' λ c i h ↦ (fresh_split (fresh c i h).1).2).mpr hv
    · exact (sim.evalArgs_iff hfr).mpr hrpath
  | send c e =>
    obtain ⟨σ', hl, ⟨M, F, v, cpath, vs, p, hv, hcpath, hlk, hp, hM, hσ', hε⟩, hpost, rfl⟩ := step
    injection hM with hM hF
    subst hM; subst hF; subst hσ'
    injection hpost with hM' hF'
    subst hM'; subst hF'; subst hε
    -- the sent-to queue in the source is the target's behind that key's prefix, whichever of the
    -- two clauses supplies it — a `send` appends at the back, so no case on whether the channel
    -- sent to is the one this process receives from
    obtain ⟨ws, hlk₁⟩ := sim.fifo_lookup hlk
    refine ⟨⟨M₁, F₁.insert (c.name, cpath) ((ws ++ vs).concat v), .none⟩,
      sim.fifo_push hlk hlk₁ v .none,
      ⟨.running M₁ (F₁.insert (c.name, cpath) ((ws ++ vs).concat v)), hlabel.trans hl,
        GuardedPlusCal.Statement.reducing.send.intro
          ⟨M₁, F₁, v, cpath, ws ++ vs, p, ?_, ?_, hlk₁, ?_, rfl, rfl, rfl⟩,
        rfl, rfl⟩⟩
    · exact (sim.eval_iff' λ c' i h ↦ (fresh_split (fresh c' i h).1).2).mpr hv
    · exact (sim.evalArgs_iff λ c' i h ↦ (fresh_split (fresh c' i h).1).1).mpr hcpath
    · exact (hself GuardedPlusCal.selfName λ c' i h ↦ (fresh c' i h).2.1).trans hp

/-- The aborting counterpart of `reducing'_sim`, and the simpler statement: an abort emits nothing,
so the source aborts on the *same* trace rather than on a prefix of the target's. Each constructor's
abort disjuncts transfer one by one — a failed evaluation stays failed (`eval_iff'`), an unresolvable
index path stays unresolvable, a missing FIFO stays missing (`relatesTo.fifo_lookup_none`), and a
failed update stays failed. -/
theorem Statement.aborting'_sim {mbox : Mailbox} {pref : ChanKey V → List V} {b : Bool}
    (S : ComputableGuardedPlusCal.Statement false b) (fresh : Fresh mbox S)
    {σₛ σₜ : LocalState' V} {ε : GuardedPlusCal.Trace V} (sim : σₛ ∼[mbox, pref] σₜ)
    (step : (⟨σₜ, ε⟩ : LocalState' V × GuardedPlusCal.Trace V) ∈
      GuardedPlusCal.Statement.aborting' S) :
    (⟨σₛ, ε⟩ : LocalState' V × GuardedPlusCal.Trace V) ∈
      GuardedPlusCal.Statement.aborting' S := by
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  obtain ⟨M₂, F₂, l₂⟩ := σₜ
  have hagree : ∀ x, (∀ c inbox, mbox = .some (c, inbox) → x ≠ inbox) →
      M₁.lookup x = M₂.lookup x := sim.mem_agree'
  have hlabel := sim.label_eq
  simp only [LocalState'.label_mk] at hlabel
  -- an expression the statement reads has no value in one memory exactly when it has none in
  -- the other
  have habort : ∀ {e : ComputablePlusCal.Expression},
      (∀ c i, mbox = .some (c, i) → Expression.FreshIn i e) → (M₂ ⊢ e ↯) → (M₁ ⊢ e ↯) :=
    λ hfe hab ⟨v, hv⟩ ↦ hab ⟨v, (sim.eval_iff' hfe).mp hv⟩
  -- and likewise for a reference's index path
  have hpaths : ∀ {r : ComputableGuardedPlusCal.Ref},
      (∀ c i, mbox = .some (c, i) → i ∉ GuardedPlusCal.Ref.freeVars r) →
      GuardedPlusCal.Ref.pathAborts M₂ r → GuardedPlusCal.Ref.pathAborts M₁ r := by
    rintro r hfr ⟨e, hmem, hab⟩
    refine ⟨e, hmem, habort ?_ hab⟩
    obtain ⟨seg, hseg, hval⟩ := List.mem_filterMap.mp hmem
    match seg, hval with
    | .inr e', rfl => exact λ c i h hx ↦ hfr c i h (Ref.freeVars_of_mem_args hseg hx)
  obtain ⟨hl, hab⟩ := step
  exists hlabel.trans hl
  cases S with
  | skip => exact hab.elim
  | goto label => exact hab.elim
  | multicast c filter => exact hab.elim
  | print e =>
    obtain ⟨M, F, hab, hM, hε⟩ := hab
    injection hM with hM hF
    subst hM; subst hF; subst hε
    exact ⟨M₁, F₁, habort (λ c i h ↦ (fresh c i h).1) hab, rfl, rfl⟩
  | assert e =>
    rcases hab with ⟨M, F, hab, hM, hε⟩ | ⟨M, F, v, hv, hvv, hM, hε⟩
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      exact .inl ⟨M₁, F₁, habort (λ c i h ↦ (fresh c i h).1) hab, rfl, rfl⟩
    · injection hM with hM hF
      subst hM; subst hF; subst hε
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
    rcases hab with ((⟨M, F, hmem, hM, hε⟩ | ⟨M, F, hab, hM, hε⟩) | ⟨M, F, hab, hM, hε⟩) |
      ⟨M, F, v, rpath, hv, hrpath, hupd, hM, hε⟩
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      refine .inl (.inl (.inl ⟨M₁, F₁, ?_, rfl, rfl⟩))
      rw [← Finmap.lookup_isSome, hagree r.name hrname, Finmap.lookup_isSome]
      exact hmem
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      exact .inl (.inl (.inr ⟨M₁, F₁, habort hfe hab, rfl, rfl⟩))
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      exact .inl (.inr ⟨M₁, F₁, hpaths hfr hab, rfl, rfl⟩)
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      refine .inr ⟨M₁, F₁, v, rpath, (sim.eval_iff' hfe).mpr hv, ?_, ?_, rfl, rfl⟩
      · exact (sim.evalArgs_iff hfr).mpr hrpath
      · exact Memory.update_none_transfer (hagree r.name hrname) hupd
  | send c e =>
    have hfc : ∀ c' i, mbox = .some (c', i) → i ∉ GuardedPlusCal.Ref.freeVars c :=
      λ c' i h ↦ (fresh_split (fresh c' i h).1).1
    have hfe : ∀ c' i, mbox = .some (c', i) → Expression.FreshIn i e :=
      λ c' i h ↦ (fresh_split (fresh c' i h).1).2
    rcases hab with (⟨M, F, hab, hM, hε⟩ | ⟨M, F, hab, hM, hε⟩) |
      ⟨M, F, cpath, hcpath, hlk, hM, hε⟩
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      exact .inl (.inl ⟨M₁, F₁, habort hfe hab, rfl, rfl⟩)
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      exact .inl (.inr ⟨M₁, F₁, hpaths hfc hab, rfl, rfl⟩)
    -- the FIFO the channel resolves to is absent in the target exactly when it is in the source
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      exact .inr ⟨M₁, F₁, cpath, (sim.evalArgs_iff hfc).mpr hcpath,
        sim.fifo_lookup_none hlk, rfl, rfl⟩

/-! ## The guard class

  `Statement.reducing'_sim` covers the action constructors. The two guard constructors the pass
  copies across — `with` and `await` — need the same fact, and get their own lemma rather than a
  generalization of that one: the *third* guard constructor is `receive`, which emphatically does
  not preserve `relatesTo`, and a statement quantified over the class would have to carve it out by
  hand at every use.
-/

/-- `Statement.reducing'_sim` for the guard class. `await` reads an expression and changes nothing;
`with` additionally binds a name, and the binding is invisible to the invariant exactly because
`Fresh` says the bound name is neither `inbox` nor read by the mailbox channel's index path. -/
theorem Statement.guardReducing'_sim {mbox : Mailbox} {pref : ChanKey V → List V}
    (S : ComputableGuardedPlusCal.Statement true false)
    (notRecv : ∀ c r coe, S ≠ .receive c r coe) (fresh : Fresh mbox S)
    {σₛ σₜ σₜ' : LocalState' V} {ε : GuardedPlusCal.Trace V} (sim : σₛ ∼[mbox, pref] σₜ)
    (step : (⟨σₜ, ε, σₜ'⟩ : LocalState' V × GuardedPlusCal.Trace V × LocalState' V) ∈
      GuardedPlusCal.Statement.reducing' S) :
    ∃ σₛ', σₛ' ∼[mbox, pref] σₜ' ∧
      (⟨σₛ, ε, σₛ'⟩ : LocalState' V × GuardedPlusCal.Trace V × LocalState' V) ∈
        GuardedPlusCal.Statement.reducing' S := by
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  obtain ⟨M₂, F₂, l₂⟩ := σₜ
  obtain ⟨M₂', F₂', l₂'⟩ := σₜ'
  have hagree : ∀ x, (∀ c inbox, mbox = .some (c, inbox) → x ≠ inbox) →
      M₁.lookup x = M₂.lookup x := sim.mem_agree'
  have hlabel := sim.label_eq
  simp only [LocalState'.label_mk] at hlabel
  cases S with
  | «with» x ann bound e =>
    obtain ⟨σ', hl, ⟨M, F, v, hv, hnone, hM, hε, hb⟩, hpost, rfl⟩ := step
    injection hM with hM hF
    subst hM; subst hF; subst hε
    -- the binder is neither `inbox` nor a name the mailbox channel's index path reads
    have hbox : ∀ c i, mbox = .some (c, i) → x ≠ i ∧ x ∉ GuardedPlusCal.Ref.freeVars c :=
      λ c i h ↦ ⟨(fresh c i h).2.2.2 x rfl, (fresh c i h).2.2.1 x rfl⟩
    have hnone₁ : Finmap.lookup x M₁ = .none :=
      (hagree x λ c i h ↦ (hbox c i h).1).trans hnone
    have hv₁ : M₁ ⊢ e ⇒ v := (sim.eval_iff' λ c i h ↦ (fresh c i h).1).mpr hv
    -- so the same value is bound in both memories and neither half of the invariant moves
    have hrel : ∀ u : V, (⟨Finmap.insert x u M₁, F₁, .none⟩ : LocalState' V) ∼[mbox, pref]
        ⟨Finmap.insert x u M₂, F₂, .none⟩ := by
      refine λ u ↦ sim.mem_congr hbox (λ y hy ↦ Finmap.lookup_insert_of_ne _ hy)
        (λ y hy ↦ Finmap.lookup_insert_of_ne _ hy) ?_ .none
      rw [Finmap.lookup_insert, Finmap.lookup_insert]
    cases bound with
    | true =>
      subst hb
      injection hpost with hM' hF'
      subst hM'; subst hF'
      exact ⟨⟨Finmap.insert x v M₁, F₁, .none⟩, hrel v,
        ⟨.running (Finmap.insert x v M₁) F₁, hlabel.trans hl,
          GuardedPlusCal.Statement.reducing.with.intro
            ⟨M₁, F₁, v, hv₁, hnone₁, rfl, rfl, rfl⟩, rfl, rfl⟩⟩
    | false =>
      obtain ⟨u, hu, rfl⟩ := hb
      injection hpost with hM' hF'
      subst hM'; subst hF'
      exact ⟨⟨Finmap.insert x u M₁, F₁, .none⟩, hrel u,
        ⟨.running (Finmap.insert x u M₁) F₁, hlabel.trans hl,
          GuardedPlusCal.Statement.reducing.with.intro
            ⟨M₁, F₁, v, hv₁, hnone₁, rfl, rfl, ⟨u, hu, rfl⟩⟩, rfl, rfl⟩⟩
  | await e =>
    obtain ⟨σ', hl, ⟨M, F, hM, hσ', hv, hε⟩, hpost, rfl⟩ := step
    injection hM with hM hF
    subst hM; subst hF; subst hσ'
    injection hpost with hM' hF'
    subst hM'; subst hF'; subst hε
    exact ⟨⟨M₁, F₁, .none⟩, sim.label_congr .none,
      ⟨.running M₁ F₁, hlabel.trans hl,
        GuardedPlusCal.Statement.reducing.await.intro
          ⟨M₁, F₁, rfl, rfl, (sim.eval_iff' λ c i h ↦ (fresh c i h).1).mpr hv, rfl⟩, rfl, rfl⟩⟩
  | receive c r coe =>
    absurd (rfl : GuardedPlusCal.Statement.receive c r coe = .receive c r coe)
    exact notRecv c r coe

/-- `Statement.aborting'_sim` for the guard class. Both constructors abort on exactly two things —
the expression having no value, or having one of the wrong shape — and both transfer by
`relatesTo.eval_iff'`, in the aborting case through `ExprSemantics.aborts_congr`. -/
theorem Statement.guardAborting'_sim {mbox : Mailbox} {pref : ChanKey V → List V}
    (S : ComputableGuardedPlusCal.Statement true false)
    (notRecv : ∀ c r coe, S ≠ .receive c r coe) (fresh : Fresh mbox S)
    {σₛ σₜ : LocalState' V} {ε : GuardedPlusCal.Trace V} (sim : σₛ ∼[mbox, pref] σₜ)
    (step : (⟨σₜ, ε⟩ : LocalState' V × GuardedPlusCal.Trace V) ∈
      GuardedPlusCal.Statement.aborting' S) :
    (⟨σₛ, ε⟩ : LocalState' V × GuardedPlusCal.Trace V) ∈
      GuardedPlusCal.Statement.aborting' S := by
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  obtain ⟨M₂, F₂, l₂⟩ := σₜ
  have hlabel := sim.label_eq
  simp only [LocalState'.label_mk] at hlabel
  cases S with
  | «with» x ann bound e =>
    obtain ⟨hl, habort⟩ := step
    have heval {v : V} : (M₁ ⊢ e ⇒ v) ↔ (M₂ ⊢ e ⇒ v) :=
      sim.eval_iff' λ c i h ↦ (fresh c i h).1
    refine ⟨hlabel.trans hl, GuardedPlusCal.Statement.aborting.with.intro ?_⟩
    rcases habort with ⟨M, F, ha, hM, hε⟩ | ⟨M, F, v, hv, hM, hε, hset⟩
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      exact .inl ⟨M₁, F₁, (ExprSemantics.aborts_congr λ _ ↦ heval).mpr ha, rfl, rfl⟩
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      exact .inr ⟨M₁, F₁, v, heval.mpr hv, rfl, rfl, hset⟩
  | await e =>
    obtain ⟨hl, habort⟩ := step
    have heval {v : V} : (M₁ ⊢ e ⇒ v) ↔ (M₂ ⊢ e ⇒ v) :=
      sim.eval_iff' λ c i h ↦ (fresh c i h).1
    refine ⟨hlabel.trans hl, GuardedPlusCal.Statement.aborting.await.intro ?_⟩
    rcases habort with ⟨M, F, ha, hM, hε⟩ | ⟨M, F, v, hbool, hv, hM, hε⟩
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      exact .inl ⟨M₁, F₁, (ExprSemantics.aborts_congr λ _ ↦ heval).mpr ha, rfl, rfl⟩
    · injection hM with hM hF
      subst hM; subst hF; subst hε
      exact .inr ⟨M₁, F₁, v, hbool, heval.mpr hv, rfl, rfl⟩
  | receive c r coe =>
    absurd (rfl : GuardedPlusCal.Statement.receive c r coe = .receive c r coe)
    exact notRecv c r coe

theorem convertActionStmt_reducing' {b : Bool} (S : ComputableGuardedPlusCal.Statement false b) :
    NetworkPlusCal.Statement.reducing' (V := V) (convertActionStmt S) =
      GuardedPlusCal.Statement.reducing' (V := V) S := by
  cases S <;> rfl

theorem convertActionStmt_aborting' {b : Bool} (S : ComputableGuardedPlusCal.Statement false b) :
    NetworkPlusCal.Statement.aborting' (V := V) (convertActionStmt S) =
      GuardedPlusCal.Statement.aborting' (V := V) S := by
  cases S <;> rfl

omit [ExprSemantics V] in
theorem convertActionStmt_diverging' {b : Bool} (S : ComputableGuardedPlusCal.Statement false b) :
    NetworkPlusCal.Statement.diverging' (V := V) (convertActionStmt S) =
      GuardedPlusCal.Statement.diverging' (V := V) S := by
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
    NetworkPlusCal.Statement.reducing' (V := V) (.with x ann bound e) =
      GuardedPlusCal.Statement.reducing' (V := V) (.with x ann bound e) :=
  rfl

@[inherit_doc with_reducing'_eq]
theorem with_aborting'_eq {x : String} {ann : ComputableTLAPlus.Typ} {bound : Bool}
    {e : ComputablePlusCal.Expression} :
    NetworkPlusCal.Statement.aborting' (V := V) (.with x ann bound e) =
      GuardedPlusCal.Statement.aborting' (V := V) (.with x ann bound e) :=
  rfl

omit [ExprSemantics V] in
@[inherit_doc with_reducing'_eq]
theorem with_diverging'_eq {x : String} {ann : ComputableTLAPlus.Typ} {bound : Bool}
    {e : ComputablePlusCal.Expression} :
    NetworkPlusCal.Statement.diverging' (V := V) (.with x ann bound e) =
      GuardedPlusCal.Statement.diverging' (V := V) (.with x ann bound e) :=
  rfl

@[inherit_doc with_reducing'_eq]
theorem await_reducing'_eq {e : ComputablePlusCal.Expression} :
    NetworkPlusCal.Statement.reducing' (V := V) (.await e) =
      GuardedPlusCal.Statement.reducing' (V := V) (.await e) :=
  rfl

@[inherit_doc with_reducing'_eq]
theorem await_aborting'_eq {e : ComputablePlusCal.Expression} :
    NetworkPlusCal.Statement.aborting' (V := V) (.await e) =
      GuardedPlusCal.Statement.aborting' (V := V) (.await e) :=
  rfl

omit [ExprSemantics V] in
@[inherit_doc with_reducing'_eq]
theorem await_diverging'_eq {e : ComputablePlusCal.Expression} :
    NetworkPlusCal.Statement.diverging' (V := V) (.await e) =
      GuardedPlusCal.Statement.diverging' (V := V) (.await e) :=
  rfl

/-- **D4, the deliverable**: `convertActionStmt` refines, statement by statement, at this pass's
own trace relation (equality — `Guarded2Network/Lemmas/Trace.lean`).

The three components come out very differently. `terminating` is the whole of `reducing'_sim`;
`aborting` is `aborting'_sim` with the `≼[Rτ]` obligation trivial, an abort emitting the empty
trace; `diverging` is vacuous, a statement having no non-terminating semantics at all — divergence
enters only at the block and algorithm layers. -/
theorem action_refines {mbox : Mailbox} {pref : ChanKey V → List V} {b : Bool}
    (S : ComputableGuardedPlusCal.Statement false b) (fresh : Fresh mbox S) :
    StrongRefinement (relatesTo (V := V) mbox pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.reducing' S) (GuardedPlusCal.Statement.aborting' S)
      (GuardedPlusCal.Statement.diverging' S)
      (NetworkPlusCal.Statement.reducing' (convertActionStmt S))
      (NetworkPlusCal.Statement.aborting' (convertActionStmt S))
      (NetworkPlusCal.Statement.diverging' (convertActionStmt S)) := by
  have hterm : StrongRefinement.Terminating (relatesTo (V := V) mbox pref) (relatesTo mbox pref)
      (instTrace (V := V)).Rτ (GuardedPlusCal.Statement.reducing' S)
      (GuardedPlusCal.Statement.aborting' S) (GuardedPlusCal.Statement.reducing' S) := by
    intro σₜ σₜ' ε σₛ sim step
    obtain ⟨σₛ', hrel, hstep⟩ := Statement.reducing'_sim S fresh sim step
    refines_match σₛ', ε
    · exact hrel
    · trace_rel
    · exact hstep
  have habort : StrongRefinement.Aborting (relatesTo (V := V) mbox pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.aborting' S) (GuardedPlusCal.Statement.aborting' S) := by
    intro σₜ ε σₛ sim step
    refines_abort ε
    · trace_pfx
    · exact Statement.aborting'_sim S fresh sim step
  -- the target cannot diverge, so the framework supplies the third component itself
  rw [convertActionStmt_reducing', convertActionStmt_aborting', convertActionStmt_diverging',
    GuardedPlusCal.Statement.diverging'_eq_empty]
  exact StrongRefinement.ofNonDiverging (relatesTo (V := V) mbox pref) hterm habort

/-- **D4's guard-class counterpart**: a `with` or an `await` refines itself, the two languages'
constructors denoting the same relation (`with_reducing'_eq` and friends). Stated on the *source*
semantics for the same reason `action_refines` is stated through `convertActionStmt`: the target's
semantics is the source's, and saying so once keeps the two languages out of the proof. -/
theorem guard_refines {mbox : Mailbox} {pref : ChanKey V → List V}
    (S : ComputableGuardedPlusCal.Statement true false)
    (notRecv : ∀ c r coe, S ≠ .receive c r coe) (fresh : Fresh mbox S) :
    StrongRefinement (relatesTo (V := V) mbox pref) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.reducing' S) (GuardedPlusCal.Statement.aborting' S)
      (GuardedPlusCal.Statement.diverging' S)
      (GuardedPlusCal.Statement.reducing' S) (GuardedPlusCal.Statement.aborting' S) ∅ := by
  refine StrongRefinement.ofNonDiverging (relatesTo (V := V) mbox pref) ?_ ?_
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
