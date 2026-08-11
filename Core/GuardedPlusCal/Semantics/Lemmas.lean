module

meta import CustomPrelude
public import Core.GuardedPlusCal.Semantics.Denotational
public import Core.GuardedPlusCal.Syntax.Lemmas

@[expose] public section

/-!
  Semantic equations for Guarded PlusCal: how `Block.reducing`/`.aborting`/`.diverging` decompose
  along `Block`'s list-like interface (`end`/`cons`/`concat`/`prepend`), and how they commute with an
  injective relabelling of the state type.

  Everything here is about *this* language's own semantics, not about the relationship between
  Guarded and Network PlusCal — prior art inlined these into `Guarded2Network/Lemmas.lean`, which is
  what made that file 7521 lines.

  Nothing in this file mentions values or the expression layer: the `Block` combinators are generic
  over the statement family `α`, the state family `β`, and the behavior monoid `γ`, so
  `NetworkPlusCal`'s own semantics reuses these lemmas verbatim rather than restating them.

  Prior art phrased these with the `⟦·⟧*`/`⟦·⟧⊥`/`⟦·⟧∞` notations, resolving the semantics through
  `Reduce`/`Abort`/`Diverge` instances. Those instances do not exist here (see
  `Semantics/Denotational.lean`'s module doc), so each lemma takes the step relation explicitly.
-/

namespace GuardedPlusCal

open ComputableTLAPlus (Memory ExprSemantics)

/-! # Path resolution is deterministic

  `Ref.args` resolves to a `List (PathStep V)` through `EvalStep`, and a `ChanKey` is a channel's
  name paired with that list — so a reference names *the* FIFO it reads only if the resolution is
  unique. It is, because `ExprSemantics.evalUnique` says an expression has at most one value; the
  two lemmas below are that fact lifted over one segment and over a whole path.
-/

section Resolution

variable {V : Type} [ExprSemantics V] {M : Memory V}

/-- One path segment resolves to at most one `PathStep`. -/
theorem EvalStep.inj {a : String ⊕ ComputablePlusCal.Expression} {p q : ComputableTLAPlus.PathStep V}
    (h₁ : EvalStep M a p) (h₂ : EvalStep M a q) : p = q := by
  cases h₁ with
  | field f => cases h₂; rfl
  | index hv =>
    cases h₂ with
    | index hw => rw [ExprSemantics.evalUnique hv hw]

/-- A whole `Ref.args` resolves to at most one path. -/
theorem EvalStep.path_inj {args : List (String ⊕ ComputablePlusCal.Expression)}
    {p q : List (ComputableTLAPlus.PathStep V)}
    (h₁ : List.Forall₂ (EvalStep M) args p) (h₂ : List.Forall₂ (EvalStep M) args q) : p = q := by
  induction h₁ generalizing q with
  | nil => cases h₂; rfl
  | cons hhd _ ih =>
    cases h₂ with
    | cons hhd' htl' => rw [EvalStep.inj hhd hhd', ih htl']

/-- `List.Forall₂ (EvalStep M)` and `ComputableTLAPlus.ResolvesPath` are one relation in two shapes.
The statement semantics resolves a `Ref.args` with the former; `ExprSemantics.evalExcept` states the
`EXCEPT` law against the latter, having been declared before `EvalStep` exists. Nothing else bridges
them, so anything relating an `assign` to the substitution standing for it
(`Guarded2Network/Lemmas/Reorder.lean`) passes through here. -/
theorem EvalStep.resolvesPath_iff {args : List (String ⊕ ComputablePlusCal.Expression)}
    {path : List (ComputableTLAPlus.PathStep V)} :
    List.Forall₂ (EvalStep M) args path ↔
      ComputableTLAPlus.ResolvesPath ExprSemantics.Eval M args path := by
  iff_rintro h h
  · induction h with
    | nil => exact .nil
    | cons hhd _ ih =>
      cases hhd with
      | field _ => exact .inl ih
      | index hv => exact .inr hv ih
  · induction h with
    | nil => exact .nil
    | inl _ ih => exact .cons (.field _) ih
    | inr hv _ ih => exact .cons (.index hv) ih

/-- A list of reference segments resolves exactly when each of its index expressions has a value.
The list-level content of `Ref.not_pathAborts_iff` below, separate because the induction runs on the
list while `Ref.pathAborts` is stated about a whole `Ref`. -/
theorem EvalStep.exists_forall₂_iff {args : List (String ⊕ ComputablePlusCal.Expression)} :
    (∃ path, List.Forall₂ (EvalStep M) args path) ↔ ∀ e, Sum.inr e ∈ args → ∃ v, M ⊢ e ⇒ v := by
  induction args with
  | nil =>
    simp only [List.not_mem_nil, false_implies, implies_true, iff_true]
    exact ⟨[], .nil⟩
  | cons hd tl ih =>
    iff_rintro ⟨path, hpath⟩ h
    · intro e he
      cases hpath with
      | cons hhd htl =>
        rcases List.mem_cons.mp he with rfl | he'
        · cases hhd with
          | index hv => exact ⟨_, hv⟩
        · exact ih.mp ⟨_, htl⟩ e he'
    · obtain ⟨path, hpath⟩ := ih.mpr λ e he ↦ h e (List.mem_cons_of_mem _ he)
      cases hd with
      | inl f => exact ⟨.inl f :: path, .cons (.field f) hpath⟩
      | inr e =>
        obtain ⟨v, hv⟩ := h e List.mem_cons_self
        exact ⟨.inr v :: path, .cons (.index hv) hpath⟩

/-- `Ref.pathAborts` with the `filterMap` gone: some index segment of the reference has no value.
The definition filters the `.inr` segments out of `Ref.args` to say that; every consumer wants the
membership back in terms of `Ref.args` itself, which is what `Ref.freeVars`'s own lemmas are stated
against. -/
theorem Ref.pathAborts_iff {r : ComputableGuardedPlusCal.Ref} :
    Ref.pathAborts M r ↔ ∃ e, Sum.inr e ∈ r.args ∧ (M ⊢ e ↯) := by
  unfold Ref.pathAborts
  simp only [List.mem_filterMap, Sum.getRight?_eq_some_iff]
  iff_rintro ⟨e, ⟨_, ha, rfl⟩, habort⟩ ⟨e, hmem, habort⟩
  · exact ⟨e, ha, habort⟩
  · exact ⟨e, ⟨.inr e, hmem, rfl⟩, habort⟩

/-- The positive reading of "the path does not abort": every index segment has a value, so the whole
`Ref.args` resolves. `Eval` being a relation is what makes this classical — "has no derivation" only
yields a value by excluded middle — and it is what lets an `assign` be shown to *step* whenever it
does not abort (`Guarded2Network/Lemmas/Reorder.lean`). -/
theorem Ref.not_pathAborts_iff {r : ComputableGuardedPlusCal.Ref} :
    ¬ Ref.pathAborts M r ↔ ∃ path, List.Forall₂ (EvalStep M) r.args path := by classical
  simp only [EvalStep.exists_forall₂_iff, Ref.pathAborts_iff, not_exists, not_and,
    ExprSemantics.Aborts, not_forall_not]

end Resolution

/-! # Constructor-intro lemmas

  Restate each constructor's `Statement.reducing`/`.aborting` case as a named lemma whose
  hypothesis is exactly that case's own body — proved by `trivial` (the two sides are defeq).
  Exist solely so a caller (`sem_red`'s dispatch macro, §3 T1) can `apply` a fixed name per
  constructor instead of unfolding the raw `Set`-membership definition inline. `multicast` has no
  semantics yet (`TODO(item 7)`, `OPEN_QUESTIONS.md` §9.27) and no aborting counterpart for
  `skip`/`goto` exists, since both are always `∅` there.

  Duplicated between `GuardedPlusCal`/`NetworkPlusCal` rather than stated once generically:
  `Statement.reducing`/`.aborting` are two separate `def`s (one per language, on two separate
  inductives), and the proof is `trivial` either way — not worth a shared-`idle`/`test` refactor
  of `Semantics/Denotational.lean` for.
-/

section Intro

variable {V : Type} [ExprSemantics V]

theorem Statement.reducing.with.intro {σ σ' : LocalState V false} {ε : Trace V}
    {name ann bound e}
    (h : ∃ M F v, M ⊢ e ⇒ v ∧ Finmap.lookup name M = none ∧ σ = .running M F ∧ ε = 1 ∧
      match bound with
        | true => σ' = .running (M.insert name v) F
        | false => ∃ v', ExprSemantics.mem v' v ∧ σ' = .running (M.insert name v') F) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (GuardedPlusCal.Statement.with name ann bound e) :=
  h

theorem Statement.reducing.await.intro {σ σ' : LocalState V false} {ε : Trace V} {e}
    (h : ∃ M F, σ = .running M F ∧ σ' = .running M F ∧ M ⊢ e ⇒ ExprSemantics.tru ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (GuardedPlusCal.Statement.await e) :=
  h

theorem Statement.reducing.receive.intro {σ σ' : LocalState V false} {ε : Trace V}
    {c r coe}
    (h : ∃ M F M' cpath rpath v v' vs,
      List.Forall₂ (EvalStep M) c.args cpath ∧
      List.Forall₂ (EvalStep M) r.args rpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧
      ExprSemantics.coerce coe v v' ∧
      Memory.update M r.name rpath v' = .some M' ∧
      σ = .running M F ∧ σ' = .running M' (F.insert ⟨c.name, cpath⟩ vs) ∧
      ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (GuardedPlusCal.Statement.receive c r coe) :=
  h

theorem Statement.reducing.skip.intro {σ σ' : LocalState V false} {ε : Trace V}
    (h : ∃ M F, σ = .running M F ∧ σ' = .running M F ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing GuardedPlusCal.Statement.skip :=
  h

theorem Statement.reducing.goto.intro {σ : LocalState V false} {σ' : LocalState V true}
    {ε : Trace V} {label}
    (h : ∃ M F, σ = .running M F ∧ σ' = .done M F label ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (GuardedPlusCal.Statement.goto label) :=
  h

theorem Statement.reducing.print.intro {σ σ' : LocalState V false} {ε : Trace V} {e}
    (h : ∃ M F v p, σ = .running M F ∧ σ' = .running M F ∧ M ⊢ e ⇒ v ∧ M.lookup selfName = .some p ∧
      ε = Stream'.Seq.cons (.print p v) 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (GuardedPlusCal.Statement.print e) :=
  h

theorem Statement.reducing.assert.intro {σ σ' : LocalState V false} {ε : Trace V} {e}
    (h : ∃ M F, σ = .running M F ∧ σ' = .running M F ∧ M ⊢ e ⇒ ExprSemantics.tru ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (GuardedPlusCal.Statement.assert e) :=
  h

theorem Statement.reducing.send.intro {σ σ' : LocalState V false} {ε : Trace V} {c e}
    (h : ∃ M F v cpath vs p,
      M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) c.args cpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some vs ∧ M.lookup selfName = .some p ∧
      σ = .running M F ∧ σ' = .running M (F.insert ⟨c.name, cpath⟩ (vs.concat v)) ∧
      ε = Stream'.Seq.cons (.send p ⟨c.name, cpath⟩ v) 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (GuardedPlusCal.Statement.send c e) :=
  h

theorem Statement.reducing.assign.intro {σ σ' : LocalState V false} {ε : Trace V} {r e}
    (h : ∃ M F M' v rpath,
      M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
      Memory.update M r.name rpath v = .some M' ∧
      σ = .running M F ∧ σ' = .running M' F ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (GuardedPlusCal.Statement.assign r e) :=
  h

theorem Statement.aborting.with.intro {σ : LocalState V false} {ε : Trace V}
    {name ann bound e}
    (h : (⟨σ, ε⟩ : LocalState V false × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = 1 ∧ match bound with
          | true => False
          | false => ¬ ExprSemantics.isSet v}) :
    ⟨σ, ε⟩ ∈ Statement.aborting (GuardedPlusCal.Statement.with name ann bound e) :=
  h

theorem Statement.aborting.await.intro {σ : LocalState V false} {ε : Trace V} {e}
    (h : (⟨σ, ε⟩ : LocalState V false × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, ¬ ExprSemantics.isBool v ∧ M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting (GuardedPlusCal.Statement.await e) :=
  h

theorem Statement.aborting.receive.intro {σ : LocalState V false} {ε : Trace V} {c r coe}
    (h : (⟨σ, ε⟩ : LocalState V false × Trace V) ∈ ({⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = .running M F ∧ ε = 1}
        ∪ {⟨σ, ε⟩ | ∃ M F, σ = .running M F ∧ ε = 1 ∧ Ref.pathAborts M c}
        ∪ {⟨σ, ε⟩ | ∃ M F, σ = .running M F ∧ ε = 1 ∧ Ref.pathAborts M r}
        ∪ {⟨σ, ε⟩ | ∃ M F cpath, σ = .running M F ∧ ε = 1 ∧
            List.Forall₂ (EvalStep M) c.args cpath ∧ F.lookup ⟨c.name, cpath⟩ = .none}
        ∪ {⟨σ, ε⟩ | ∃ M F cpath v vs, σ = .running M F ∧ ε = 1 ∧
            List.Forall₂ (EvalStep M) c.args cpath ∧
            F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧ ¬ ∃ v', ExprSemantics.coerce coe v v'}
        ∪ {⟨σ, ε⟩ | ∃ M F cpath rpath v v' vs, σ = .running M F ∧ ε = 1 ∧
            List.Forall₂ (EvalStep M) c.args cpath ∧
            List.Forall₂ (EvalStep M) r.args rpath ∧
            F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧ ExprSemantics.coerce coe v v' ∧
            Memory.update M r.name rpath v' = .none})) :
    ⟨σ, ε⟩ ∈ Statement.aborting (GuardedPlusCal.Statement.receive c r coe) :=
  h

theorem Statement.aborting.print.intro {σ : LocalState V false} {ε : Trace V} {e}
    (h : ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1) :
    ⟨σ, ε⟩ ∈ Statement.aborting (GuardedPlusCal.Statement.print e) :=
  h

theorem Statement.aborting.assert.intro {σ : LocalState V false} {ε : Trace V} {e}
    (h : (⟨σ, ε⟩ : LocalState V false × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, v ≠ ExprSemantics.tru ∧ M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting (GuardedPlusCal.Statement.assert e) :=
  h

theorem Statement.aborting.send.intro {σ : LocalState V false} {ε : Trace V} {c e}
    (h : (⟨σ, ε⟩ : LocalState V false × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts M c ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep M) c.args cpath ∧
          F.lookup ⟨c.name, cpath⟩ = .none ∧ σ = .running M F ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting (GuardedPlusCal.Statement.send c e) :=
  h

theorem Statement.aborting.assign.intro {σ : LocalState V false} {ε : Trace V} {r e}
    (h : (⟨σ, ε⟩ : LocalState V false × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts M r ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v rpath,
          M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
          Memory.update M r.name rpath v = .none ∧ σ = .running M F ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting (GuardedPlusCal.Statement.assign r e) :=
  h

end Intro

-- Leaf discharge for `sem_side` (T1, `Core/NetworkPlusCal/Semantics/Lemmas.lean`'s `sem_red`).
attribute [aesop safe apply (rule_sets := [sem])]
  Statement.reducing.with.intro Statement.reducing.await.intro Statement.reducing.receive.intro
  Statement.reducing.skip.intro Statement.reducing.goto.intro Statement.reducing.print.intro
  Statement.reducing.assert.intro Statement.reducing.send.intro Statement.reducing.assign.intro
  Statement.aborting.with.intro Statement.aborting.await.intro Statement.aborting.receive.intro
  Statement.aborting.print.intro Statement.aborting.assert.intro Statement.aborting.send.intro
  Statement.aborting.assign.intro

/-! # Reduction -/

section Reducing

variable {α β : Bool → Type} {γ : Type} [Monoid γ]
  (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b))

@[aesop safe apply (rule_sets := [sem])]
theorem Block.listReducing_nil : Block.listReducing f [] = Relation.Idle := rfl

@[aesop safe apply (rule_sets := [sem])]
theorem Block.listReducing_cons {S : α false} {A : List (α false)} :
    Block.listReducing f (S :: A) = f S ∘ᵣ₂ Block.listReducing f A := rfl

/-- A run splits wherever its list does. Every `Block` equation below is this one plus
`Relation.lcomp₂.assoc`. -/
theorem Block.listReducing_append {A B : List (α false)} :
    Block.listReducing f (A ++ B) = Block.listReducing f A ∘ᵣ₂ Block.listReducing f B := by
  induction A with
  | nil => rw [List.nil_append, Block.listReducing_nil, Relation.lcomp₂.left_id_eq]
  | cons S A IH =>
    rw [List.cons_append, Block.listReducing_cons, Block.listReducing_cons, IH,
      Relation.lcomp₂.assoc]

@[inherit_doc Block.listReducing_append]
theorem Block.listReducing_concat {A : List (α false)} {S : α false} :
    Block.listReducing f (A.concat S) = Block.listReducing f A ∘ᵣ₂ f S := by
  rw [List.concat_eq_append, Block.listReducing_append, Block.listReducing_cons,
    Block.listReducing_nil, Relation.lcomp₂.right_id_eq]

theorem Block.reducing_end {b : Bool} {S : α b} : Block.reducing f (Block.end S) = f S := by
  rw [Block.reducing, Block.listReducing_nil, Relation.lcomp₂.left_id_eq]

theorem Block.reducing_cons {b : Bool} {B : Block α b} {S : α false} :
    Block.reducing f (Block.cons S B) = f S ∘ᵣ₂ Block.reducing f B := by
  rw [Block.reducing, Block.reducing, Block.listReducing_cons, Relation.lcomp₂.assoc]

/-- **A non-terminal block is its own statement list.** The two are the same fold; this is the only
place that has to say so, and it is what lets a proof about a `Block` be carried out on
`Block.toList` — which is the shape a pass's walk over the block produces. -/
theorem Block.reducing_eq_listReducing {B : Block α false} :
    Block.reducing f B = Block.listReducing f B.toList := by
  rw [Block.toList, Block.listReducing_concat, Block.reducing]

theorem Block.reducing_concat {b : Bool} {B : Block α false} {S : α b} :
    Block.reducing f (B.concat S) = Block.reducing f B ∘ᵣ₂ f S := by
  rw [Block.concat, Block.reducing, Block.reducing_eq_listReducing]

theorem Block.reducing_prepend' {b : Bool} {A : List (α false)} {B : Block α b} :
    Block.reducing f (B.prepend A) = Block.listReducing f A ∘ᵣ₂ Block.reducing f B := by
  rw [Block.prepend, Block.reducing, Block.reducing, Block.listReducing_append,
    Relation.lcomp₂.assoc]

end Reducing

-- Leaf discharge for `sem_side` (T1).
attribute [aesop safe apply (rule_sets := [sem])]
  Block.reducing_end Block.reducing_cons Block.reducing_concat

/-! # Abortion and divergence

  `aborting` and `diverging` share their shape exactly — both are "this element goes wrong, or it
  steps and the rest does" — so the two families of lemmas below are literal mirrors of each other.
-/

section Aborting

variable {α β : Bool → Type} {γ : Type} [Monoid γ]
  (g : ⦃b : Bool⦄ → α b → Set (β false × γ))
  (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b))

@[aesop safe apply (rule_sets := [sem])]
theorem Block.listAborting_nil : Block.listAborting g f [] = ∅ := rfl

@[aesop safe apply (rule_sets := [sem])]
theorem Block.listAborting_cons {S : α false} {A : List (α false)} :
    Block.listAborting g f (S :: A) = g S ∪ f S ∘ᵣ₁ Block.listAborting g f A := rfl

/-- A run goes wrong wherever its list splits: either the prefix does, or it runs and the suffix
does. `Block.listReducing_append`'s twin, and every `Block` equation below is this one plus
`Relation.lcomp₁.union_lcomp₂`. -/
theorem Block.listAborting_append {A B : List (α false)} :
    Block.listAborting g f (A ++ B) =
      Block.listAborting g f A ∪ Block.listReducing f A ∘ᵣ₁ Block.listAborting g f B := by
  induction A with
  | nil =>
    rw [List.nil_append, Block.listAborting_nil, Block.listReducing_nil,
      Relation.lcomp₁.left_id_eq, Set.empty_union]
  | cons S A IH =>
    rw [List.cons_append, Block.listAborting_cons, Block.listAborting_cons,
      Block.listReducing_cons, IH, Relation.lcomp₁.union_lcomp₂]

@[inherit_doc Block.listAborting_append]
theorem Block.listAborting_concat {A : List (α false)} {S : α false} :
    Block.listAborting g f (A.concat S) =
      Block.listAborting g f A ∪ Block.listReducing f A ∘ᵣ₁ g S := by
  rw [List.concat_eq_append, Block.listAborting_append, Block.listAborting_cons,
    Block.listAborting_nil, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]

theorem Block.aborting_end {b : Bool} {S : α b} : Block.aborting g f (Block.end S) = g S := by
  rw [Block.aborting, Block.listAborting_nil, Block.listReducing_nil,
    Relation.lcomp₁.left_id_eq, Set.empty_union]

theorem Block.aborting_cons {b : Bool} {S : α false} {B : Block α b} :
    Block.aborting g f (Block.cons S B) = g S ∪ f S ∘ᵣ₁ Block.aborting g f B := by
  rw [Block.aborting, Block.aborting, Block.listAborting_cons, Block.listReducing_cons,
    Relation.lcomp₁.union_lcomp₂]

@[inherit_doc Block.reducing_eq_listReducing]
theorem Block.aborting_eq_listAborting {B : Block α false} :
    Block.aborting g f B = Block.listAborting g f B.toList := by
  rw [Block.toList, Block.listAborting_concat, Block.aborting]

theorem Block.aborting_concat {b : Bool} {S : α b} {B : Block α false} :
    Block.aborting g f (B.concat S) =
      Block.aborting g f B ∪ Block.reducing f B ∘ᵣ₁ g S := by
  rw [Block.concat, Block.aborting, Block.aborting_eq_listAborting,
    Block.reducing_eq_listReducing]

/-- A prefixed block goes wrong either inside the prefix or, having run it, inside the block. The
shape a refinement against a block whose prefix a pass generated (`Guarded2Network`'s consumption
assignments) is stated in. -/
theorem Block.aborting_prepend {b : Bool} {A : List (α false)} {B : Block α b} :
    Block.aborting g f (B.prepend A) =
      Block.listAborting g f A ∪ Block.listReducing f A ∘ᵣ₁ Block.aborting g f B := by
  rw [Block.prepend, Block.aborting, Block.aborting, Block.listAborting_append,
    Block.listReducing_append, Relation.lcomp₁.union_lcomp₂]

end Aborting

section Diverging

variable {α β : Bool → Type} {γ : Type} [Monoid γ]
  (d : ⦃b : Bool⦄ → α b → Set (β false × γ))
  (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b))

/-- **`Block.diverging` *is* `Block.aborting`.** "This element goes wrong, or it steps and the rest
does" is one shape, and the two definitions spell it identically; the semantics has said so in prose
since they were written. Saying it as an equation is what keeps the two families of lemmas below
from drifting apart — each is now the aborting one under the diverging name, and none of them is a
second proof. -/
theorem Block.diverging_eq_aborting {b : Bool} {B : Block α b} :
    Block.diverging d f B = Block.aborting d f B := rfl

theorem Block.diverging_end {b : Bool} {S : α b} : Block.diverging d f (Block.end S) = d S :=
  Block.aborting_end d f

theorem Block.diverging_cons {b : Bool} {S : α false} {B : Block α b} :
    Block.diverging d f (Block.cons S B) = d S ∪ f S ∘ᵣ₁ Block.diverging d f B :=
  Block.aborting_cons d f

@[inherit_doc Block.reducing_eq_listReducing]
theorem Block.diverging_eq_listAborting {B : Block α false} :
    Block.diverging d f B = Block.listAborting d f B.toList :=
  Block.aborting_eq_listAborting d f

theorem Block.diverging_concat {b : Bool} {S : α b} {B : Block α false} :
    Block.diverging d f (B.concat S) =
      Block.diverging d f B ∪ Block.reducing f B ∘ᵣ₁ d S :=
  Block.aborting_concat d f

@[inherit_doc Block.aborting_prepend]
theorem Block.diverging_prepend {b : Bool} {A : List (α false)} {B : Block α b} :
    Block.diverging d f (B.prepend A) =
      Block.listAborting d f A ∪ Block.listReducing f A ∘ᵣ₁ Block.diverging d f B :=
  Block.aborting_prepend d f

end Diverging

/-! # Relabelling the state type

  Item 7 needs to move between the `Bool`-indexed `LocalState` and a flat, unindexed encoding of it,
  so that source and target states inhabit one type and `StrongRefinement`'s relation can be stated.
  These three lemmas are what make that move sound: an injective relabelling of states commutes with
  taking a block's semantics. Injectivity is genuinely needed — without it, two distinct
  intermediate states could be identified and a composite step invented that the original relation
  never had.
-/

theorem Block.reducing_map {α β δ : Bool → Type} {γ : Type} [Monoid γ] {b : Bool} {B : Block α b}
    (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (g : ⦃b : Bool⦄ → β b → δ b)
    (g_inj : ∀ ⦃b⦄, Function.Injective (@g b)) :
    Prod.map₃ (@g _) id (@g _) '' Block.reducing f B =
      Block.reducing (λ ⦃_⦄ x ↦ Prod.map₃ (@g _) id (@g _) '' f x) B := by
  induction B using Block.cons_end_induct with
  | «end» S => rw [Block.reducing_end, Block.reducing_end]
  | cons S B IH =>
    rw [Block.reducing_cons, Block.reducing_cons, ← IH, Relation.lcomp₂.image (g_inj (b := false))]

theorem Block.aborting_map {α β δ : Bool → Type} {γ : Type} [Monoid γ] {b : Bool} {B : Block α b}
    (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (g : ⦃b : Bool⦄ → α b → Set (β false × γ))
    (h : ⦃b : Bool⦄ → β b → δ b) (h_inj : ∀ ⦃b⦄, Function.Injective (@h b)) :
    Prod.map (@h _) id '' Block.aborting g f B =
      Block.aborting (λ ⦃_⦄ x ↦ Prod.map (@h _) id '' g x)
        (λ ⦃_⦄ x ↦ Prod.map₃ (@h _) id (@h _) '' f x) B := by
  induction B using Block.cons_end_induct with
  | «end» S => rw [Block.aborting_end, Block.aborting_end]
  | cons S B IH =>
    rw [Block.aborting_cons, Block.aborting_cons, ← IH, Set.image_union,
      Relation.lcomp₁.image (h_inj (b := false))]

@[inherit_doc Block.diverging_eq_aborting]
theorem Block.diverging_map {α β δ : Bool → Type} {γ : Type} [Monoid γ] {b : Bool} {B : Block α b}
    (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (d : ⦃b : Bool⦄ → α b → Set (β false × γ))
    (h : ⦃b : Bool⦄ → β b → δ b) (h_inj : ∀ ⦃b⦄, Function.Injective (@h b)) :
    Prod.map (@h _) id '' Block.diverging d f B =
      Block.diverging (λ ⦃_⦄ x ↦ Prod.map (@h _) id '' d x)
        (λ ⦃_⦄ x ↦ Prod.map₃ (@h _) id (@h _) '' f x) B :=
  Block.aborting_map f d h h_inj

/-! # The flat state encoding

  `LocalState` is indexed by whether the state is terminal, which is what makes the block semantics
  typecheck: only a terminal statement may produce a `done`. `StrongRefinement` cannot use an
  indexed state type — its relation has to hold source and target states of one fixed type — so item
  7 works over `LocalState'`, where the index becomes an ordinary `Option String` field: `none` for
  running, `some l` for done at label `l`.

  `toLocalState'` is the translation, `toLocalState'_inj` its injectivity, and the `*_eq_map` lemmas
  below say the two encodings give the same block semantics up to that translation. The `*_glue`
  lemmas are the membership-level corollaries, which is the form item 7 actually rewrites with.
-/

section Flat

variable {V : Type}

/-- `LocalState` with the terminality index traded for an `Option String` field. -/
abbrev LocalState' (V : Type) : Type := Memory V × FIFOs V × Option String

/-! Named projections of `LocalState'`. It is a nested anonymous product, so its components are
otherwise reachable only as `σ.1`/`σ.2.1`/`σ.2.2` or by destructuring at every binding site — and
the refinement proof binds a state roughly four times per lemma across dozens of lemmas. Named
projections let those proofs `intro σₜ σₜ' ε σₛ` with no pattern at all and reach components by
name, destructuring only where a proof genuinely case-splits on the label. Kept an `abbrev` rather
than promoted to a structure so `toLocalState'_inj` and the `*_eq_map` lemmas below are unaffected;
the `@[simp]` equations put each projection back into component form on demand. -/

/-- The memory component. -/
def LocalState'.mem (σ : LocalState' V) : Memory V := σ.1

/-- The FIFO component. -/
def LocalState'.fifos (σ : LocalState' V) : FIFOs V := σ.2.1

/-- The label component: `none` while running, `some l` once the block has jumped to `l`. -/
def LocalState'.label (σ : LocalState' V) : Option String := σ.2.2

@[simp] theorem LocalState'.mem_mk (M : Memory V) (F : FIFOs V) (l : Option String) :
    LocalState'.mem ⟨M, F, l⟩ = M := rfl

@[simp] theorem LocalState'.fifos_mk (M : Memory V) (F : FIFOs V) (l : Option String) :
    LocalState'.fifos ⟨M, F, l⟩ = F := rfl

@[simp] theorem LocalState'.label_mk (M : Memory V) (F : FIFOs V) (l : Option String) :
    LocalState'.label ⟨M, F, l⟩ = l := rfl

@[simp] theorem LocalState'.mk_mem_fifos_label (σ : LocalState' V) :
    (⟨σ.mem, σ.fifos, σ.label⟩ : LocalState' V) = σ := rfl

/-- `LocalState` in the flat encoding. -/
def LocalState.toLocalState' : {b : Bool} → LocalState V b → LocalState' V
  | false, .running M F => ⟨M, F, .none⟩
  | true, .done M F l => ⟨M, F, .some l⟩

theorem LocalState.toLocalState'_inj ⦃b : Bool⦄ :
    Function.Injective (@LocalState.toLocalState' V b) := by
  cases b with
  | false => rintro ⟨M, F⟩ ⟨M', F'⟩ (_|_); rfl
  | true => rintro (_|⟨M, F, l⟩) (_|⟨M', F', l'⟩) (_|_); rfl

variable [ExprSemantics V]

/-- `Statement.reducing` in the flat encoding. A step is only taken from a *running* state, so the
source's label field must be `none`; the target's records whether the statement was terminal. -/
def Statement.reducing' {b b' : Bool} (S : ComputableGuardedPlusCal.Statement b b') :
    Set (LocalState' V × Trace V × LocalState' V) :=
  {⟨⟨M, F, l⟩, ε, ⟨M', F', l'⟩⟩ | ∃ σ' : LocalState V b',
    l = Option.none ∧ ⟨LocalState.running M F, ε, σ'⟩ ∈ Statement.reducing S ∧ match b', σ' with
      | true, σ' => ∃ l'', σ' = LocalState.done M' F' l'' ∧ l' = Option.some l''
      | false, σ' => σ' = LocalState.running M' F' ∧ l' = Option.none}

@[inherit_doc Statement.reducing']
def Statement.aborting' {b b' : Bool} (S : ComputableGuardedPlusCal.Statement b b') :
    Set (LocalState' V × Trace V) :=
  {⟨⟨M, F, l⟩, ε⟩ | l = Option.none ∧ ⟨LocalState.running M F, ε⟩ ∈ Statement.aborting S}

@[inherit_doc Statement.reducing']
def Statement.diverging' {b b' : Bool} (S : ComputableGuardedPlusCal.Statement b b') :
    Set (LocalState' V × Trace V) :=
  {⟨⟨M, F, l⟩, ε⟩ | l = Option.none ∧ ⟨LocalState.running M F, ε⟩ ∈ Statement.diverging S}

omit [ExprSemantics V] in
/-- No statement diverges, in the flat encoding as in the indexed one. Stated rather than left
implicit because it is what lets a statement-level refinement be discharged by
`StrongRefinement.ofNonDiverging` instead of by an inlined "the target cannot diverge" argument. -/
@[simp] theorem Statement.diverging'_eq_empty {b b' : Bool}
    (S : ComputableGuardedPlusCal.Statement b b') :
    Statement.diverging' (V := V) S = ∅ := by
  ext ⟨⟨M, F, l⟩, ε⟩
  iff_rintro ⟨-, hd⟩ hd
  · exact hd.elim
  · exact hd.elim

/-! `Statement.listReducing'`/`.listAborting'`/`.listDiverging'` — the flat-encoding list forms, the
twins of `NetworkPlusCal`'s. Item 7 relates a *list* of source guards to a target composite, so the
source needs the same shape the target has. -/

@[inherit_doc Statement.reducing']
def Statement.listReducing' {g : Bool} (A : List (ComputableGuardedPlusCal.Statement g false)) :
    Set (LocalState' V × Trace V × LocalState' V) :=
  Block.listReducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') A

@[inherit_doc Statement.reducing']
def Statement.listAborting' {g : Bool} (A : List (ComputableGuardedPlusCal.Statement g false)) :
    Set (LocalState' V × Trace V) :=
  Block.listAborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
    (λ ⦃_⦄ ↦ Statement.reducing') A

@[inherit_doc Statement.reducing']
def Statement.listDiverging' {g : Bool} (A : List (ComputableGuardedPlusCal.Statement g false)) :
    Set (LocalState' V × Trace V) :=
  Block.listAborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
    (λ ⦃_⦄ ↦ Statement.reducing') A

@[aesop safe apply (rule_sets := [sem])]
theorem Statement.listReducing'_nil {g : Bool} :
    Statement.listReducing' (V := V) (g := g) [] = Relation.Idle := rfl

@[aesop safe apply (rule_sets := [sem])]
theorem Statement.listReducing'_cons {g : Bool} {S : ComputableGuardedPlusCal.Statement g false}
    {A : List (ComputableGuardedPlusCal.Statement g false)} :
    Statement.listReducing' (V := V) (S :: A) =
      Statement.reducing' S ∘ᵣ₂ Statement.listReducing' A := rfl

@[aesop safe apply (rule_sets := [sem])]
theorem Statement.listAborting'_nil {g : Bool} :
    Statement.listAborting' (V := V) (g := g) [] = ∅ := rfl

@[aesop safe apply (rule_sets := [sem])]
theorem Statement.listAborting'_cons {g : Bool} {S : ComputableGuardedPlusCal.Statement g false}
    {A : List (ComputableGuardedPlusCal.Statement g false)} :
    Statement.listAborting' (V := V) (S :: A) =
      Statement.aborting' S ∪ Statement.reducing' S ∘ᵣ₁ Statement.listAborting' A := rfl

/-- A run splits wherever its list does. Named at this instantiation because that is how the
walk meets it — one statement appended at a time — while the content is
`Block.listReducing_append`. -/
theorem Statement.listReducing'_append {g : Bool}
    {A B : List (ComputableGuardedPlusCal.Statement g false)} :
    Statement.listReducing' (V := V) (A ++ B) =
      Statement.listReducing' A ∘ᵣ₂ Statement.listReducing' B :=
  Block.listReducing_append _

@[inherit_doc Statement.listReducing'_append]
theorem Statement.listAborting'_append {g : Bool}
    {A B : List (ComputableGuardedPlusCal.Statement g false)} :
    Statement.listAborting' (V := V) (A ++ B) =
      Statement.listAborting' A ∪ Statement.listReducing' A ∘ᵣ₁ Statement.listAborting' B :=
  Block.listAborting_append _ _

/-- No *list* of statements diverges either — `Statement.diverging'_eq_empty` propagated through the
fold. What makes a block-level refinement's diverging component `StrongRefinement.Diverging.Empty`
rather than an argument. -/
@[simp] theorem Statement.listDiverging'_eq_empty {g : Bool}
    {A : List (ComputableGuardedPlusCal.Statement g false)} :
    Statement.listDiverging' (V := V) A = ∅ := by
  induction A with
  | nil => rfl
  | cons S A IH =>
    show Statement.diverging' S ∪ Statement.reducing' S ∘ᵣ₁ Statement.listDiverging' A = ∅
    rw [Statement.diverging'_eq_empty, IH, Relation.lcomp₁.right_empty_eq_empty, Set.union_self]

/-- No *block* diverges either — the same fact at block shape, which is how a branch-level
refinement gets its diverging component as `∅` rather than as something to carry. -/
@[simp] theorem Block.diverging'_eq_empty {g b : Bool}
    {B : Block (ComputableGuardedPlusCal.Statement g) b} :
    Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
        (λ ⦃_⦄ ↦ Statement.reducing') B = ∅ := by
  show Statement.listDiverging' B.begin ∪ _ ∘ᵣ₁ Statement.diverging' B.last = ∅
  rw [Statement.listDiverging'_eq_empty, Statement.diverging'_eq_empty,
    Relation.lcomp₁.right_empty_eq_empty, Set.union_self]

private theorem Statement.reducing'_eq_map {b b' : Bool}
    (S : ComputableGuardedPlusCal.Statement b b') :
    Statement.reducing' (V := V) S =
      Prod.map₃ LocalState.toLocalState' id LocalState.toLocalState' '' Statement.reducing S := by
  ext ⟨⟨M, F, l⟩, e, ⟨M', F', l'⟩⟩
  constructor
  · cases b' with
    | false =>
      rintro ⟨⟨M'', F''⟩, rfl, sem, _|_, rfl⟩
      exists _, sem
    | true =>
      rintro ⟨⟨M'', F'', l''⟩, rfl, sem, _, _|_, rfl⟩
      exists _, sem
  · cases b' with
    | false =>
      rintro ⟨⟨⟨_, _⟩, _, ⟨_, _⟩⟩, sem, _|_⟩
      exists _, rfl, sem
    | true =>
      rintro ⟨⟨⟨_, _⟩, _, _|⟨_, _, l⟩⟩, sem, _|_⟩
      exists _, rfl, sem, l

private theorem Statement.aborting'_eq_map {b b' : Bool}
    (S : ComputableGuardedPlusCal.Statement b b') :
    Statement.aborting' (V := V) S =
      Prod.map LocalState.toLocalState' id '' Statement.aborting S := by
  ext ⟨⟨M, F, l⟩, e⟩
  iff_rintro ⟨rfl, sem⟩ ⟨⟨⟨_⟩, _⟩, _, _|_⟩
  · exists _, sem
  · trivial

-- `Statement.diverging` is `∅` regardless of the expression semantics, so this one does not use it.
omit [ExprSemantics V] in
private theorem Statement.diverging'_eq_map {b b' : Bool}
    (S : ComputableGuardedPlusCal.Statement b b') :
    Statement.diverging' (V := V) S =
      Prod.map LocalState.toLocalState' id '' Statement.diverging S := by
  ext ⟨⟨M, F, l⟩, e⟩
  iff_rintro ⟨rfl, sem⟩ ⟨⟨⟨_⟩, _⟩, _, _|_⟩
  · exists _, sem
  · trivial

theorem Block.reducing'_eq_map {g b : Bool}
    {B : Block (ComputableGuardedPlusCal.Statement g) b} :
    Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B =
      Prod.map₃ LocalState.toLocalState' id LocalState.toLocalState' ''
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B := by
  rw [Block.reducing_map _ _ LocalState.toLocalState'_inj]
  conv_rhs => enter [1, b, S]; rw [← Statement.reducing'_eq_map S]

theorem Block.aborting'_eq_map {g b : Bool}
    {B : Block (ComputableGuardedPlusCal.Statement g) b} :
    Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
        (λ ⦃_⦄ ↦ Statement.reducing') B =
      Prod.map LocalState.toLocalState' id ''
        Block.aborting (λ ⦃_⦄ ↦ Statement.aborting) (λ ⦃_⦄ ↦ Statement.reducing) B := by
  rw [Block.aborting_map _ _ _ LocalState.toLocalState'_inj]
  conv_rhs => enter [1, b, S]; rw [← Statement.aborting'_eq_map S]
  conv_rhs => enter [2, b, S]; rw [← Statement.reducing'_eq_map S]

theorem Block.diverging'_eq_map {g b : Bool}
    {B : Block (ComputableGuardedPlusCal.Statement g) b} :
    Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
        (λ ⦃_⦄ ↦ Statement.reducing') B =
      Prod.map LocalState.toLocalState' id ''
        Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) B := by
  rw [Block.diverging_map _ _ _ LocalState.toLocalState'_inj]
  conv_rhs => enter [1, b, S]; rw [← Statement.diverging'_eq_map S]
  conv_rhs => enter [2, b, S]; rw [← Statement.reducing'_eq_map S]

/-! The four membership-level corollaries item 7 rewrites with. Each says that a concrete indexed
step is the same fact as the corresponding flat one — the direction that matters is `mp`, which
lets an indexed hypothesis be fed to a `StrongRefinement` goal stated over `LocalState'`. -/

theorem LocalState.sem_glue₁ {g : Bool} {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V} {l : String}
    {ε : Trace V} {B : Block (ComputableGuardedPlusCal.Statement g) true} :
    ⟨LocalState.running M₁ F₁, ε, LocalState.done M₂ F₂ l⟩ ∈
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε, (M₂, F₂, some l)⟩ ∈
        Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.reducing'_eq_map, Set.mem_image]
  iff_rintro sem ⟨⟨⟨_, _⟩, _, _|⟨_, _⟩⟩, sem, _|_⟩
  · exists _, sem
  · exact sem

theorem LocalState.sem_glue₂ {g : Bool} {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V}
    {ε : Trace V} {B : Block (ComputableGuardedPlusCal.Statement g) false} :
    ⟨LocalState.running M₁ F₁, ε, LocalState.running M₂ F₂⟩ ∈
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε, (M₂, F₂, none)⟩ ∈
        Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.reducing'_eq_map, Set.mem_image]
  iff_rintro sem ⟨⟨⟨_, _⟩, _, _|⟨_, _⟩⟩, sem, _|_⟩
  · exists _, sem
  · exact sem

theorem LocalState.abort_glue {g b : Bool} {M₁ : Memory V} {F₁ : FIFOs V}
    {ε : Trace V} {B : Block (ComputableGuardedPlusCal.Statement g) b} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈
        Block.aborting (λ ⦃_⦄ ↦ Statement.aborting) (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε⟩ ∈
        Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
          (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.aborting'_eq_map, Set.mem_image]
  iff_rintro sem ⟨⟨⟨_, _⟩, _⟩, sem, _|_⟩
  · exists _, sem
  · exact sem

theorem LocalState.div_glue {g b : Bool} {M₁ : Memory V} {F₁ : FIFOs V}
    {ε : Trace V} {B : Block (ComputableGuardedPlusCal.Statement g) b} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈
        Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε⟩ ∈
        Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
          (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.diverging'_eq_map, Set.mem_image]
  iff_rintro sem ⟨⟨⟨_, _⟩, _⟩, sem, _|_⟩
  · exists _, sem
  · exact sem

-- Leaf discharge for `sem_side` (T1). `simp` builder, not `apply`: these are `↔`, and aesop's own
-- apply-builder linter is right that an iff wants `simp`, not `apply` (which only ever tries one
-- direction and is what the plan's own draft literally said — deviated from it here).
attribute [aesop norm simp (rule_sets := [sem])]
  LocalState.sem_glue₁ LocalState.sem_glue₂ LocalState.abort_glue LocalState.div_glue

/-! # `AtomicBranch`, flat

  Mirrors `AtomicBranch.reducing`/`.aborting`/`.diverging` (`Semantics/Denotational.lean`) at the
  flat encoding, built from the primed leaf functions above rather than proved equal to an image of
  the indexed version after the fact — the indexed ones are already exactly "precondition, then
  action" by definition, so there is nothing to transport.

  No `AtomicBlock` layer here, for the reason `Core/NetworkPlusCal/Semantics/Denotational.lean`'s
  module doc gives: a source block is only ever existentially quantified, never required to match a
  target's type.
-/

/-- `AtomicBranch.reducing` in the flat encoding. -/
def AtomicBranch.reducing' (B : ComputableGuardedPlusCal.AtomicBranch) :
    Set (LocalState' V × Trace V × LocalState' V) :=
  B.precondition.elim Relation.Idle
    (Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing')) ∘ᵣ₂
    Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B.action

@[inherit_doc AtomicBranch.reducing']
def AtomicBranch.aborting' (B : ComputableGuardedPlusCal.AtomicBranch) :
    Set (LocalState' V × Trace V) :=
  match B.precondition with
  | .none => Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
      (λ ⦃_⦄ ↦ Statement.reducing') B.action
  | .some B' =>
    Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
        (λ ⦃_⦄ ↦ Statement.reducing') B' ∪
      Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B' ∘ᵣ₁
        Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
          (λ ⦃_⦄ ↦ Statement.reducing') B.action

@[inherit_doc AtomicBranch.reducing']
def AtomicBranch.diverging' (B : ComputableGuardedPlusCal.AtomicBranch) :
    Set (LocalState' V × Trace V) :=
  match B.precondition with
  | .none => Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
      (λ ⦃_⦄ ↦ Statement.reducing') B.action
  | .some B' =>
    Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
        (λ ⦃_⦄ ↦ Statement.reducing') B' ∪
      Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B' ∘ᵣ₁
        Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
          (λ ⦃_⦄ ↦ Statement.reducing') B.action

/-- The `match` on the precondition, discharged: `.none` composes with the identity relation and
contributes no aborting runs of its own, which is exactly what `Option.elim` says. The uniform form
is what a `StrongRefinement.Comp` of the two halves produces, so this is the bridge between the
definition above and every proof about it. -/
theorem AtomicBranch.aborting'_eq (B : ComputableGuardedPlusCal.AtomicBranch) :
    AtomicBranch.aborting' (V := V) B =
      B.precondition.elim ∅ (Block.aborting (β := λ _ ↦ LocalState' V)
          (λ ⦃_⦄ ↦ Statement.aborting') (λ ⦃_⦄ ↦ Statement.reducing')) ∪
        B.precondition.elim Relation.Idle (Block.reducing (β := λ _ ↦ LocalState' V)
            (λ ⦃_⦄ ↦ Statement.reducing')) ∘ᵣ₁
          Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
            (λ ⦃_⦄ ↦ Statement.reducing') B.action := by
  rw [AtomicBranch.aborting']
  cases B.precondition with
  | none => rw [Option.elim, Option.elim, Relation.lcomp₁.left_id_eq, Set.empty_union]
  | some => rfl

@[inherit_doc AtomicBranch.aborting'_eq]
theorem AtomicBranch.diverging'_eq (B : ComputableGuardedPlusCal.AtomicBranch) :
    AtomicBranch.diverging' (V := V) B =
      B.precondition.elim ∅ (Block.diverging (β := λ _ ↦ LocalState' V)
          (λ ⦃_⦄ ↦ Statement.diverging') (λ ⦃_⦄ ↦ Statement.reducing')) ∪
        B.precondition.elim Relation.Idle (Block.reducing (β := λ _ ↦ LocalState' V)
            (λ ⦃_⦄ ↦ Statement.reducing')) ∘ᵣ₁
          Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
            (λ ⦃_⦄ ↦ Statement.reducing') B.action := by
  rw [AtomicBranch.diverging']
  cases B.precondition with
  | none => rw [Option.elim, Option.elim, Relation.lcomp₁.left_id_eq, Set.empty_union]
  | some => rfl

/-- No `GuardedPlusCal` statement diverges, so no branch does either. -/
@[simp] theorem AtomicBranch.diverging'_eq_empty (B : ComputableGuardedPlusCal.AtomicBranch) :
    AtomicBranch.diverging' (V := V) B = ∅ := by
  rw [AtomicBranch.diverging'_eq, Block.diverging'_eq_empty, Relation.lcomp₁.right_empty_eq_empty,
    Set.union_empty]
  cases B.precondition with
  | none => rfl
  | some => exact Block.diverging'_eq_empty

/-! The same membership-level corollaries one level up, at `AtomicBranch` rather than `Block`.
Twins of `NetworkPlusCal`'s `sem_glue₃`/`abort_glue₂` and needed for the same reason: the process
layer states a step against the *indexed* `AtomicBranch.reducing`, while every refinement lemma is
stated against the flat `reducing'`.

The extra work over the `Block`-level glue is the composition boundary. A branch is its precondition
composed with its action, and the intermediate state is a `.running` constructor on the indexed side
against a flat triple on the other — whose label field has to be known to be `none` before the two
can be matched up. `LocalState'.sem_label_eq` is what supplies that. -/

/-- Every flat `Block.reducing` membership has `none` in both endpoints' label fields: that field
changes only at the `AtomicBranch`-composition boundary, never inside a `Block` built from
`Statement.reducing'`. -/
theorem LocalState'.sem_label_eq {g : Bool} {B : Block (ComputableGuardedPlusCal.Statement g) false}
    {σ σ' : LocalState' V} {ε : Trace V}
    (h : ⟨σ, ε, σ'⟩ ∈ Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B) :
    σ.2.2 = none ∧ σ'.2.2 = none := by
  rw [Block.reducing'_eq_map, Set.mem_image] at h
  obtain ⟨⟨⟨_, _⟩, _, ⟨_, _⟩⟩, _, rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem LocalState.sem_glue₃ {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V} {l : String}
    {ε : Trace V} {Br : ComputableGuardedPlusCal.AtomicBranch} :
    ⟨LocalState.running M₁ F₁, ε, LocalState.done M₂ F₂ l⟩ ∈ AtomicBranch.reducing Br ↔
      ⟨(M₁, F₁, none), ε, (M₂, F₂, some l)⟩ ∈ AtomicBranch.reducing' (V := V) Br := by
  unfold AtomicBranch.reducing AtomicBranch.reducing' Statement.blockReducing
  cases hpre : Br.precondition with
  | none =>
    simp only [Option.elim]
    rw [Relation.lcomp₂.left_id_eq, Relation.lcomp₂.left_id_eq]
    exact LocalState.sem_glue₁
  | some B' =>
    simp only [Option.elim]
    iff_rintro ⟨⟨M', F'⟩, ε₁, ε₂, red_pre, red_act, rfl⟩
      ⟨⟨M', F', l'⟩, ε₁, ε₂, red_pre, red_act, rfl⟩
    · exact ⟨(M', F', none), ε₁, ε₂, (LocalState.sem_glue₂ (B := B')).mp red_pre,
        (LocalState.sem_glue₁ (B := Br.action)).mp red_act, rfl⟩
    · obtain rfl : l' = none :=
        (LocalState'.sem_label_eq (B := B') (σ := ((M₁, F₁, none) : LocalState' V))
          (σ' := (M', F', l')) red_pre).2
      exact ⟨LocalState.running M' F', ε₁, ε₂, (LocalState.sem_glue₂ (B := B')).mpr red_pre,
        (LocalState.sem_glue₁ (B := Br.action)).mpr red_act, rfl⟩

@[inherit_doc LocalState.sem_glue₃]
theorem LocalState.abort_glue₂ {M₁ : Memory V} {F₁ : FIFOs V} {ε : Trace V}
    {Br : ComputableGuardedPlusCal.AtomicBranch} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈ AtomicBranch.aborting Br ↔
      ⟨(M₁, F₁, none), ε⟩ ∈ AtomicBranch.aborting' (V := V) Br := by
  unfold AtomicBranch.aborting AtomicBranch.aborting' Statement.blockReducing
    Statement.blockAborting
  cases hpre : Br.precondition with
  | none => exact LocalState.abort_glue
  | some B' =>
    iff_rintro (h|⟨⟨M', F'⟩, ε₁, ε₂, red_pre, abort_act, rfl⟩)
      (h|⟨⟨M', F', l'⟩, ε₁, ε₂, red_pre, abort_act, rfl⟩)
    · exact .inl ((LocalState.abort_glue (B := B')).mp h)
    · exact .inr ⟨(M', F', none), ε₁, ε₂, (LocalState.sem_glue₂ (B := B')).mp red_pre,
        (LocalState.abort_glue (B := Br.action)).mp abort_act, rfl⟩
    · exact .inl ((LocalState.abort_glue (B := B')).mpr h)
    · obtain rfl : l' = none :=
        (LocalState'.sem_label_eq (B := B') (σ := ((M₁, F₁, none) : LocalState' V))
          (σ' := (M', F', l')) red_pre).2
      exact .inr ⟨LocalState.running M' F', ε₁, ε₂, (LocalState.sem_glue₂ (B := B')).mpr red_pre,
        (LocalState.abort_glue (B := Br.action)).mpr abort_act, rfl⟩

end Flat

end GuardedPlusCal

end
