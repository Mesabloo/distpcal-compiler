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
    {σₛ σₜ : LocalState' V} (h : σₛ ∼[.some (c, inbox)] σₜ)
    {e : ComputablePlusCal.Expression} {v : V} (fresh : Expression.FreshIn inbox e) :
    ((σₛ.mem ⊢ e ⇒ v)) ↔ ((σₜ.mem ⊢ e ⇒ v)) := by
  apply ExprSemantics.evalLocal
  intro y hy
  apply h.mem_agree
  rintro rfl
  exact fresh hy

/-- The same for a process that receives nothing: there the memories are equal outright and the
freshness hypothesis has nothing to say. -/
theorem relatesTo.eval_iff_none {σₛ σₜ : LocalState' V} (h : σₛ ∼[.none] σₜ)
    {e : ComputablePlusCal.Expression} {v : V} :
    ((σₛ.mem ⊢ e ⇒ v)) ↔ ((σₜ.mem ⊢ e ⇒ v)) := by
  rw [h.mem_eq]

/-- Both cases at once, with the freshness hypothesis stated so that it is vacuous when there is no
mailbox — the form a lemma quantified over an arbitrary `mbox` needs. -/
theorem relatesTo.eval_iff' {mbox : Mailbox} {σₛ σₜ : LocalState' V} (h : σₛ ∼[mbox] σₜ)
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

/-- Memories agreeing away from `inbox` resolve a reference's path identically, provided the
reference does not read `inbox`. This is D2's point: the `List.Forall₂` nesting is discharged once,
here, and no later proof sees it. -/
theorem Ref.EvalArgs.congr_of_fresh {M₁ M₂ : Memory V} {r : ComputableGuardedPlusCal.Ref}
    {inbox : String} {path : List (PathStep V)}
    (agree : ∀ x ≠ inbox, M₁.lookup x = M₂.lookup x)
    (fresh : inbox ∉ GuardedPlusCal.Ref.freeVars r) :
    Ref.EvalArgs M₁ r path ↔ Ref.EvalArgs M₂ r path := by
  unfold Ref.EvalArgs
  have step : ∀ (args : List (String ⊕ ComputablePlusCal.Expression))
      (path : List (PathStep V)),
      (∀ e, Sum.inr e ∈ args → Expression.FreshIn inbox e) →
      (List.Forall₂ (EvalStep M₁) args path ↔ List.Forall₂ (EvalStep M₂) args path) := by
    intro args
    induction args with
    | nil =>
      intro path _
      rw [List.forall₂_nil_left_iff, List.forall₂_nil_left_iff]
    | cons hd tl ih =>
      intro path hfresh
      -- the head segment's own agreement, needed in both directions
      have hhead : ∀ (e : ComputablePlusCal.Expression), hd = Sum.inr e →
          ∀ y ∈ e.freeVars, M₁.lookup y = M₂.lookup y := by
        rintro e rfl y hy
        apply agree y
        rintro rfl
        exact hfresh _ (List.mem_cons_self ..) hy
      have htail : ∀ e, Sum.inr e ∈ tl → Expression.FreshIn inbox e :=
        λ e he ↦ hfresh e (List.mem_cons_of_mem _ he)
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
  exact step r.args path (λ e he hx ↦ fresh (Ref.freeVars_of_mem_args he hx))

/-- With no mailbox the two states are equal outright — the three projections exhaust
`LocalState'`. Lets the no-`receive` case of every simulation below close immediately. -/
theorem relatesTo.eq_of_none {σₛ σₜ : LocalState' V} (h : σₛ ∼[.none] σₜ) : σₛ = σₜ := by
  obtain ⟨M₁, F₁, l₁⟩ := σₛ
  obtain ⟨M₂, F₂, l₂⟩ := σₜ
  obtain ⟨hl, hm, hf⟩ := h
  simp_all

/-! ## Transferring a memory update

  `assign` (and, on the source side, `receive`) writes through `Memory.update`. Simulating that step
  means running the same update in the other memory and finding the results still related — which
  holds because the two memories agree at the written name, so they read the same old value, compute
  the same new one, and insert it.
-/

/-- An update that succeeds in one memory succeeds in any memory agreeing with it away from `inbox`,
provided the written name is not `inbox` itself, and the results still agree away from `inbox`. -/
theorem Memory.update_transfer {M₁ M₂ M₁' : Memory V} {inbox x : String}
    {path : List (PathStep V)} {v : V}
    (agree : ∀ y ≠ inbox, M₁.lookup y = M₂.lookup y) (hx : x ≠ inbox)
    (h₁ : ComputableTLAPlus.Memory.update M₁ x path v = .some M₁') :
    ∃ M₂', ComputableTLAPlus.Memory.update M₂ x path v = .some M₂' ∧
      ∀ y ≠ inbox, M₁'.lookup y = M₂'.lookup y := by
  obtain ⟨old, new, hold, hnew, rfl⟩ := ComputableTLAPlus.Memory.update_eq_some_iff.mp h₁
  refine ⟨M₂.insert x new,
    ComputableTLAPlus.Memory.update_eq_some_iff.mpr ⟨old, new, ?_, hnew, rfl⟩, ?_⟩
  · rw [← agree x hx]
    exact hold
  · intro y hy
    by_cases hyx : y = x
    · subst hyx
      rw [Finmap.lookup_insert _, Finmap.lookup_insert _]
    · rw [Finmap.lookup_insert_of_ne _ hyx, Finmap.lookup_insert_of_ne _ hyx]
      exact agree y hy

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
  | _ => .none

/-- What an action statement must avoid for the pass's `inbox` not to disturb it: the statement
cannot read `inbox`, and `inbox` cannot be `self` — `print`/`send` read `self` to tag the event they
emit, which is a name the *semantics* reads on its own and so is invisible to a freshness condition
stated over the statement's free variables. Both hold of any real compilation: `freshName`'s `$`
separator puts `inbox` outside the source program's namespace entirely. -/
def Fresh (mbox : Mailbox) {b : Bool} (S : ComputableGuardedPlusCal.Statement false b) : Prop :=
  ∀ c inbox, mbox = .some (c, inbox) →
    inbox ∉ GuardedPlusCal.Statement.freeVars S ∧ inbox ≠ GuardedPlusCal.selfName ∧
      ∀ x, Statement.writtenName? S = .some x → x ∉ GuardedPlusCal.Ref.freeVars c

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
terms. Each piece built above is spent here: `eval_iff` for the statements that evaluate an
expression, `Ref.EvalArgs.congr_of_fresh` for those that resolve a reference,
`Memory.update_transfer` for `assign`, `relatesTo.fifo_split` for `send`. -/
theorem Statement.reducing'_sim {mbox : Mailbox} {b : Bool}
    (S : ComputableGuardedPlusCal.Statement false b) (fresh : Fresh mbox S)
    {σₛ σₜ σₜ' : LocalState' V} {ε : GuardedPlusCal.Trace V} (sim : σₛ ∼[mbox] σₜ)
    (step : (⟨σₜ, ε, σₜ'⟩ : LocalState' V × GuardedPlusCal.Trace V × LocalState' V) ∈
      GuardedPlusCal.Statement.reducing' S) :
    ∃ σₛ', σₛ' ∼[mbox] σₜ' ∧
      (⟨σₛ, ε, σₛ'⟩ : LocalState' V × GuardedPlusCal.Trace V × LocalState' V) ∈
        GuardedPlusCal.Statement.reducing' S := by
  match mbox with
  | .none =>
    obtain rfl := sim.eq_of_none
    exact ⟨σₜ', relatesTo.none_intro rfl rfl rfl, step⟩
  | .some (c₀, inbox) =>
    obtain ⟨hfresh, hself, hwrite⟩ := fresh c₀ inbox rfl
    obtain ⟨cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩ := sim.inbox_seq
    obtain ⟨M₁, F₁, l₁⟩ := σₛ
    obtain ⟨M₂, F₂, l₂⟩ := σₜ
    obtain ⟨M₂', F₂', l₂'⟩ := σₜ'
    have hagree := sim.mem_agree
    have hlabel := sim.label_eq
    simp only [LocalState'.mem_mk, LocalState'.fifos_mk, LocalState'.label_mk]
      at hpath hinbox hoff hsplit hagree hlabel
    cases S with
    | skip =>
      obtain ⟨σ', hl, ⟨M, F, hM, hσ', hε⟩, hpost, rfl⟩ := step
      injection hM with hM hF
      subst hM; subst hF; subst hσ'; subst hε
      injection hpost with hM' hF'
      subst hM'; subst hF'
      exact ⟨⟨M₁, F₁, .none⟩,
        relatesTo.chan_intro rfl hagree hpath hinbox hseq hoff hsplit,
        ⟨.running M₁ F₁, hlabel.trans hl,
          GuardedPlusCal.Statement.reducing.skip.intro ⟨M₁, F₁, rfl, rfl, rfl⟩, rfl, rfl⟩⟩
    | goto label =>
      obtain ⟨σ', hl, ⟨M, F, hM, hσ', hε⟩, l'', hpost, rfl⟩ := step
      injection hM with hM hF
      subst hM; subst hF; subst hε
      rw [hσ'] at hpost
      injection hpost with hM' hF' hl''
      subst hM'; subst hF'; subst hl''
      exact ⟨⟨M₁, F₁, .some label⟩,
        relatesTo.chan_intro rfl hagree hpath hinbox hseq hoff hsplit,
        ⟨.done M₁ F₁ label, hlabel.trans hl,
          GuardedPlusCal.Statement.reducing.goto.intro ⟨M₁, F₁, rfl, rfl, rfl⟩, label, rfl, rfl⟩⟩
    | print e =>
      obtain ⟨σ', hl, ⟨M, F, v, p, hM, hσ', hv, hp, hε⟩, hpost, rfl⟩ := step
      injection hM with hM hF
      subst hM; subst hF; subst hσ'
      injection hpost with hM' hF'
      subst hM'; subst hF'; subst hε
      refine ⟨⟨M₁, F₁, .none⟩,
        relatesTo.chan_intro rfl hagree hpath hinbox hseq hoff hsplit,
        ⟨.running M₁ F₁, hlabel.trans hl,
          GuardedPlusCal.Statement.reducing.print.intro ⟨M₁, F₁, v, p, rfl, rfl, ?_, ?_, rfl⟩,
          rfl, rfl⟩⟩
      · exact (sim.eval_iff hfresh).mpr hv
      · exact (hagree GuardedPlusCal.selfName (Ne.symm hself)).trans hp
    | assert e =>
      obtain ⟨σ', hl, ⟨M, F, hM, hσ', hv, hε⟩, hpost, rfl⟩ := step
      injection hM with hM hF
      subst hM; subst hF; subst hσ'
      injection hpost with hM' hF'
      subst hM'; subst hF'; subst hε
      refine ⟨⟨M₁, F₁, .none⟩,
        relatesTo.chan_intro rfl hagree hpath hinbox hseq hoff hsplit,
        ⟨.running M₁ F₁, hlabel.trans hl,
          GuardedPlusCal.Statement.reducing.assert.intro ⟨M₁, F₁, rfl, rfl, ?_, rfl⟩, rfl, rfl⟩⟩
      exact (sim.eval_iff hfresh).mpr hv
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
      obtain ⟨hfr, hfe⟩ := fresh_split hfresh
      have hrname : r.name ≠ inbox := by
        rintro rfl
        exact hfr (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      -- the same update runs in the source memory, and the results still agree away from `inbox`
      obtain ⟨M₁', hupd₁, hagree'⟩ :=
        Memory.update_transfer (λ y hy ↦ (hagree y hy).symm) hrname hupd
      -- and it leaves the mailbox channel's own index expressions alone
      have hstable : ∀ y ≠ r.name, M₁'.lookup y = M₁.lookup y :=
        λ y hy ↦ Memory.lookup_update_ne hupd₁ hy
      refine ⟨⟨M₁', F₁, .none⟩, relatesTo.chan_intro rfl (λ y hy ↦ (hagree' y hy).symm) ?_ ?_ hseq
          hoff hsplit,
        ⟨.running M₁' F₁, hlabel.trans hl,
          GuardedPlusCal.Statement.reducing.assign.intro
            ⟨M₁, F₁, M₁', v, rpath, ?_, ?_, hupd₁, rfl, rfl, rfl⟩, rfl, rfl⟩⟩
      · exact (Ref.EvalArgs.congr_of_fresh hstable (hwrite r.name rfl)).mpr hpath
      · exact (Memory.lookup_update_ne hupd (Ne.symm hrname)).trans hinbox
      · exact (sim.eval_iff hfe).mpr hv
      · exact (Ref.EvalArgs.congr_of_fresh (λ y hy ↦ (hagree y hy).symm) hfr).mp hrpath
    | send c e =>
      obtain ⟨σ', hl, ⟨M, F, v, cpath', vs', p, hv, hcpath, hlk, hp, hM, hσ', hε⟩, hpost, rfl⟩ :=
        step
      injection hM with hM hF
      subst hM; subst hF; subst hσ'
      injection hpost with hM' hF'
      subst hM'; subst hF'; subst hε
      obtain ⟨hfc, hfe⟩ := fresh_split hfresh
      have hcpath₁ : Ref.EvalArgs M₁ c cpath' :=
        (Ref.EvalArgs.congr_of_fresh (λ y hy ↦ (hagree y hy).symm) hfc).mp hcpath
      -- the sent-to queue in the source: the target's, with this process's `inbox` in front when
      -- the channel sent on is the very one it receives from
      by_cases hkey : (c.name, cpath') = ((c₀.name, cpath) : ChanKey V)
      · obtain rfl : cpath = cpath' := (congrArg Prod.snd hkey).symm
        have hsplitc : F₁.lookup ((c.name, cpath) : ChanKey V) =
            (vs ++ ·) <$> F₂.lookup ((c.name, cpath) : ChanKey V) := by
          rw [hkey]
          exact hsplit
        have hsplit₁ : F₁.lookup ((c.name, cpath) : ChanKey V) = .some (vs ++ vs') := by
          rw [hsplitc, hlk]
          rfl
        refine ⟨⟨M₁, F₁.insert (c.name, cpath) ((vs ++ vs').concat v), .none⟩,
          relatesTo.chan_intro rfl hagree hpath hinbox hseq ?_ ?_,
          ⟨.running M₁ (F₁.insert (c.name, cpath) ((vs ++ vs').concat v)), hlabel.trans hl,
            GuardedPlusCal.Statement.reducing.send.intro
              ⟨M₁, F₁, v, cpath, vs ++ vs', p, ?_, hcpath₁, hsplit₁, ?_, rfl, rfl, rfl⟩,
            rfl, rfl⟩⟩
        · intro k hk
          simp only [LocalState'.fifos_mk]
          have hk' : k ≠ ((c.name, cpath) : ChanKey V) := by rw [hkey]; exact hk
          rw [Finmap.lookup_insert_of_ne _ hk', Finmap.lookup_insert_of_ne _ hk']
          exact hoff k hk
        · simp only [LocalState'.fifos_mk]
          rewrite [← hkey, Finmap.lookup_insert _, Finmap.lookup_insert _]
          simp [List.concat_eq_append, List.append_assoc]
        · exact (sim.eval_iff hfe).mpr hv
        · exact (hagree GuardedPlusCal.selfName (Ne.symm hself)).trans hp
      · have hlk₁ : F₁.lookup (c.name, cpath') = .some vs' := (hoff _ hkey).trans hlk
        refine ⟨⟨M₁, F₁.insert (c.name, cpath') (vs'.concat v), .none⟩,
          relatesTo.chan_intro rfl hagree hpath hinbox hseq ?_ ?_,
          ⟨.running M₁ (F₁.insert (c.name, cpath') (vs'.concat v)), hlabel.trans hl,
            GuardedPlusCal.Statement.reducing.send.intro
              ⟨M₁, F₁, v, cpath', vs', p, ?_, hcpath₁, hlk₁, ?_, rfl, rfl, rfl⟩, rfl, rfl⟩⟩
        · intro k hk
          simp only [LocalState'.fifos_mk]
          by_cases hkk : k = (c.name, cpath')
          · rw [hkk, Finmap.lookup_insert _, Finmap.lookup_insert _]
          · rw [Finmap.lookup_insert_of_ne _ hkk, Finmap.lookup_insert_of_ne _ hkk]
            exact hoff k hk
        · simp only [LocalState'.fifos_mk, Finmap.lookup_insert_of_ne _ (Ne.symm hkey)]
          exact hsplit
        · exact (sim.eval_iff hfe).mpr hv
        · exact (hagree GuardedPlusCal.selfName (Ne.symm hself)).trans hp

/-- The aborting counterpart of `reducing'_sim`, and the simpler statement: an abort emits nothing,
so the source aborts on the *same* trace rather than on a prefix of the target's. Each constructor's
abort disjuncts transfer one by one — a failed evaluation stays failed (`eval_iff`), an unresolvable
index path stays unresolvable, a missing FIFO stays missing (both cases of `relatesTo`'s FIFO
clauses give `none` on one side exactly when the other does), and a failed update stays failed. -/
theorem Statement.aborting'_sim {mbox : Mailbox} {b : Bool}
    (S : ComputableGuardedPlusCal.Statement false b) (fresh : Fresh mbox S)
    {σₛ σₜ : LocalState' V} {ε : GuardedPlusCal.Trace V} (sim : σₛ ∼[mbox] σₜ)
    (step : (⟨σₜ, ε⟩ : LocalState' V × GuardedPlusCal.Trace V) ∈
      GuardedPlusCal.Statement.aborting' S) :
    (⟨σₛ, ε⟩ : LocalState' V × GuardedPlusCal.Trace V) ∈
      GuardedPlusCal.Statement.aborting' S := by
  match mbox with
  | .none =>
    obtain rfl := sim.eq_of_none
    exact step
  | .some (c₀, inbox) =>
    obtain ⟨hfresh, hself, -⟩ := fresh c₀ inbox rfl
    obtain ⟨cpath, sv, vs, hpath, hinbox, hseq, hoff, hsplit⟩ := sim.inbox_seq
    obtain ⟨M₁, F₁, l₁⟩ := σₛ
    obtain ⟨M₂, F₂, l₂⟩ := σₜ
    have hagree := sim.mem_agree
    have hlabel := sim.label_eq
    simp only [LocalState'.mem_mk, LocalState'.fifos_mk, LocalState'.label_mk]
      at hpath hinbox hoff hsplit hagree hlabel
    -- an expression the statement reads has no value in one memory exactly when it has none in
    -- the other
    have habort : ∀ {e : ComputablePlusCal.Expression}, Expression.FreshIn inbox e →
        (M₂ ⊢ e ↯) → (M₁ ⊢ e ↯) :=
      λ hfe hab ⟨v, hv⟩ ↦ hab ⟨v, (sim.eval_iff hfe).mp hv⟩
    -- and likewise for a reference's index path
    have hpaths : ∀ {r : ComputableGuardedPlusCal.Ref},
        inbox ∉ GuardedPlusCal.Ref.freeVars r →
        GuardedPlusCal.Ref.pathAborts M₂ r → GuardedPlusCal.Ref.pathAborts M₁ r := by
      rintro r hfr ⟨e, hmem, hab⟩
      refine ⟨e, hmem, habort ?_ hab⟩
      obtain ⟨seg, hseg, hval⟩ := List.mem_filterMap.mp hmem
      match seg, hval with
      | .inr e', rfl => exact λ hx ↦ hfr (Ref.freeVars_of_mem_args hseg hx)
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
      exact ⟨M₁, F₁, habort hfresh hab, rfl, rfl⟩
    | assert e =>
      rcases hab with ⟨M, F, hab, hM, hε⟩ | ⟨M, F, v, hv, hvv, hM, hε⟩
      · injection hM with hM hF
        subst hM; subst hF; subst hε
        exact .inl ⟨M₁, F₁, habort hfresh hab, rfl, rfl⟩
      · injection hM with hM hF
        subst hM; subst hF; subst hε
        exact .inr ⟨M₁, F₁, v, hv, (sim.eval_iff hfresh).mpr hvv, rfl, rfl⟩
    | assign r e =>
      obtain ⟨hfr, hfe⟩ := fresh_split hfresh
      have hrname : r.name ≠ inbox := by
        rintro rfl
        exact hfr (Finset.mem_union_left _ (Finset.mem_singleton_self _))
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
        refine .inr ⟨M₁, F₁, v, rpath, (sim.eval_iff hfe).mpr hv, ?_, ?_, rfl, rfl⟩
        · exact (Ref.EvalArgs.congr_of_fresh (λ y hy ↦ (hagree y hy).symm) hfr).mp hrpath
        · exact Memory.update_none_transfer (hagree r.name hrname) hupd
    | send c e =>
      obtain ⟨hfc, hfe⟩ := fresh_split hfresh
      rcases hab with (⟨M, F, hab, hM, hε⟩ | ⟨M, F, hab, hM, hε⟩) |
        ⟨M, F, cpath', hcpath, hlk, hM, hε⟩
      · injection hM with hM hF
        subst hM; subst hF; subst hε
        exact .inl (.inl ⟨M₁, F₁, habort hfe hab, rfl, rfl⟩)
      · injection hM with hM hF
        subst hM; subst hF; subst hε
        exact .inl (.inr ⟨M₁, F₁, hpaths hfc hab, rfl, rfl⟩)
      -- the FIFO the channel resolves to is absent in the target exactly when it is in the source
      · injection hM with hM hF
        subst hM; subst hF; subst hε
        refine .inr ⟨M₁, F₁, cpath',
          (Ref.EvalArgs.congr_of_fresh (λ y hy ↦ (hagree y hy).symm) hfc).mp hcpath, ?_, rfl, rfl⟩
        by_cases hkey : (c.name, cpath') = ((c₀.name, cpath) : ChanKey V)
        · rw [hkey] at hlk ⊢
          rw [hsplit, hlk]
          rfl
        · rw [hoff _ hkey]
          exact hlk

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

/-- **D4, the deliverable**: `convertActionStmt` refines, statement by statement, at this pass's
own trace relation (equality — `Guarded2Network/Lemmas/Trace.lean`).

The three components come out very differently. `terminating` is the whole of `reducing'_sim`;
`aborting` is `aborting'_sim` with the `≼[Rτ]` obligation trivial, an abort emitting the empty
trace; `diverging` is vacuous, a statement having no non-terminating semantics at all — divergence
enters only at the block and algorithm layers. -/
theorem action_refines {mbox : Mailbox} {b : Bool}
    (S : ComputableGuardedPlusCal.Statement false b) (fresh : Fresh mbox S) :
    StrongRefinement (relatesTo (V := V) mbox) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.reducing' S) (GuardedPlusCal.Statement.aborting' S)
      (GuardedPlusCal.Statement.diverging' S)
      (NetworkPlusCal.Statement.reducing' (convertActionStmt S))
      (NetworkPlusCal.Statement.aborting' (convertActionStmt S))
      (NetworkPlusCal.Statement.diverging' (convertActionStmt S)) := by
  have hterm : StrongRefinement.Terminating (relatesTo (V := V) mbox) (relatesTo mbox)
      (instTrace (V := V)).Rτ (GuardedPlusCal.Statement.reducing' S)
      (GuardedPlusCal.Statement.aborting' S) (GuardedPlusCal.Statement.reducing' S) := by
    intro σₜ σₜ' ε σₛ sim step
    obtain ⟨σₛ', hrel, hstep⟩ := Statement.reducing'_sim S fresh sim step
    refines_match σₛ', ε
    · exact hrel
    · trace_rel
    · exact hstep
  have habort : StrongRefinement.Aborting (relatesTo (V := V) mbox) (instTrace (V := V)).Rτ
      (GuardedPlusCal.Statement.aborting' S) (GuardedPlusCal.Statement.aborting' S) := by
    intro σₜ ε σₛ sim step
    refines_abort ε
    · trace_pfx
    · exact Statement.aborting'_sim S fresh sim step
  -- the target cannot diverge, so the framework supplies the third component itself
  rw [convertActionStmt_reducing', convertActionStmt_aborting', convertActionStmt_diverging',
    GuardedPlusCal.Statement.diverging'_eq_empty]
  exact StrongRefinement.ofNonDiverging (relatesTo (V := V) mbox) hterm habort

end Guarded2Network

end
