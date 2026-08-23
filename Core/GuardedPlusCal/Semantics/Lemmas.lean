module

meta import CustomPrelude
public import Core.GuardedPlusCal.Semantics.Denotational
public import Core.GuardedPlusCal.Syntax.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
  Semantic equations for Guarded PlusCal: how `Block.reducing`/`.aborting`/`.diverging` decompose
  along `Block`'s list-like interface (`end`/`cons`/`concat`/`prepend`), and how they commute with an
  injective relabelling of the state type.

  Everything here is about *this* language's own semantics, not about the relationship between
  Guarded and Network PlusCal.

  Nothing in this file mentions values or the expression layer: the `Block` combinators are generic
  over the statement family `α`, the state family `β`, and the behavior monoid `γ`, so
  `NetworkPlusCal`'s own semantics reuses these lemmas verbatim rather than restating them.

  There are no `Reduce`/`Abort`/`Diverge` instances resolving the semantics behind a notation, so
  each lemma takes the step relation explicitly.
-/

namespace GuardedPlusCal

open ComputableTLAPlus (Memory ExprSemantics OperatorEnv Model)

/-! # How much is queued

  The measure a divergence argument needs. A receiving thread's relay moves one message out of a
  channel and into a process's `inbox`, so it strictly decreases the total; only a `send` increases
  it. A target run that relays forever without ever sending is therefore impossible — which is what
  says a target cannot diverge on `.rx` steps alone, and so what lets a source answering those steps
  with no step of its own still be said to diverge.
-/

/-- How many messages are queued, across every channel at once. -/
def FIFOs.size {V : Type} [ExprSemantics V] (F : FIFOs V) : ℕ :=
  ∑ k ∈ F.keys, ((F.lookup k).getD []).length

/-- **Popping the head of one queue drops the count by exactly one.** The relay's effect on the
measure, and the only fact about `FIFOs.size` anything needs. -/
theorem FIFOs.size_insert_tail {V : Type} [ExprSemantics V] {F : FIFOs V} {k : ChanKey V} {v : V}
    {vs : List V} (h : F.lookup k = .some (v :: vs)) :
    FIFOs.size (F.insert k vs) + 1 = FIFOs.size F := by
  have hmem : k ∈ F := Finmap.mem_of_lookup_eq_some h
  have hkeys : (F.insert k vs).keys = F.keys := by
    ext k'
    simp only [Finmap.mem_keys, Finmap.mem_insert]
    iff_rintro (rfl | h') h'
    · exact hmem
    · exact h'
    · exact .inr h'
  -- the two sums agree away from `k`, and at `k` one queue is the other's tail
  have hoff : ∀ k' ∈ F.keys.erase k,
      (((F.insert k vs).lookup k').getD []).length = ((F.lookup k').getD []).length := by
    intro k' hk'
    rw [Finmap.lookup_insert_of_ne _ (Finset.ne_of_mem_erase hk')]
  unfold FIFOs.size
  rw [hkeys,
    ← Finset.add_sum_erase _ _ (Finmap.mem_keys.mpr hmem),
    ← Finset.add_sum_erase _ _ (Finmap.mem_keys.mpr hmem),
    Finset.sum_congr rfl hoff, Finmap.lookup_insert, h]
  simp only [Option.getD_some, List.length_cons]
  omega

/-! # Path resolution is deterministic

  `Ref.args` resolves to a `List (PathStep V)` through `EvalStep`, and a `ChanKey` is a channel's
  name paired with that list — so a reference names *the* FIFO it reads only if the resolution is
  unique. It is, because `ExprSemantics.evalUnique` says an expression has at most one value; the
  two lemmas below are that fact lifted over one segment and over a whole path.
-/

section Resolution

variable {V : Type} [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V} {M : Memory V}

/-- One path segment resolves to at most one `PathStep`. -/
theorem EvalStep.inj {a : String ⊕ ComputablePlusCal.Expression} {p q : ComputableTLAPlus.PathStep V}
    (h₁ : EvalStep Ξ Ω M a p) (h₂ : EvalStep Ξ Ω M a q) : p = q := by
  cases h₁ with
  | field f => cases h₂; rfl
  | index hv =>
    cases h₂ with
    | index hw => rw [ExprSemantics.evalUnique hv hw]

/-- A whole `Ref.args` resolves to at most one path. -/
theorem EvalStep.path_inj {args : List (String ⊕ ComputablePlusCal.Expression)}
    {p q : List (ComputableTLAPlus.PathStep V)}
    (h₁ : List.Forall₂ (EvalStep Ξ Ω M) args p) (h₂ : List.Forall₂ (EvalStep Ξ Ω M) args q) : p = q := by
  induction h₁ generalizing q with
  | nil => cases h₂; rfl
  | cons hhd _ ih =>
    cases h₂ with
    | cons hhd' htl' => rw [EvalStep.inj hhd hhd', ih htl']

/-- `List.Forall₂ (EvalStep Ξ Ω M)` and `ComputableTLAPlus.ResolvesPath` are one relation in two shapes.
The statement semantics resolves a `Ref.args` with the former; `ExprSemantics.evalExcept` states the
`EXCEPT` law against the latter, having been declared before `EvalStep` exists. Nothing else bridges
them, so anything relating an `assign` to the substitution standing for it
(`Guarded2Network/Lemmas/Reorder.lean`) passes through here. -/
theorem EvalStep.resolvesPath_iff {args : List (String ⊕ ComputablePlusCal.Expression)}
    {path : List (ComputableTLAPlus.PathStep V)} :
    List.Forall₂ (EvalStep Ξ Ω M) args path ↔
      ComputableTLAPlus.ResolvesPath (ExprSemantics.Eval Ξ Ω) M args path := by
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
    (∃ path, List.Forall₂ (EvalStep Ξ Ω M) args path) ↔ ∀ e, Sum.inr e ∈ args → ∃ v, ExprSemantics.Eval Ξ Ω M e v := by
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
    Ref.pathAborts Ξ Ω M r ↔ ∃ e, Sum.inr e ∈ r.args ∧ (ExprSemantics.Aborts Ξ Ω M e) := by
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
    ¬ Ref.pathAborts Ξ Ω M r ↔ ∃ path, List.Forall₂ (EvalStep Ξ Ω M) r.args path := by classical
  simp only [EvalStep.exists_forall₂_iff, Ref.pathAborts_iff, not_exists, not_and,
    ExprSemantics.Aborts, not_forall_not]

end Resolution

/-! # Constructor-intro lemmas

  Restate each constructor's `Statement.reducing`/`.aborting` case as a named lemma whose
  hypothesis is exactly that case's own body — proved by `trivial` (the two sides are defeq).
  Exist so a caller can `apply` a fixed name per constructor instead of unfolding the raw
  `Set`-membership definition inline. `multicast` has no semantics yet, and no aborting counterpart
  for `skip`/`goto` exists, since both are always `∅` there.

  Duplicated between `GuardedPlusCal`/`NetworkPlusCal` rather than stated once generically:
  `Statement.reducing`/`.aborting` are two separate `def`s (one per language, on two separate
  inductives), and the proof is `trivial` either way — not worth a shared-`idle`/`test` refactor
  of `Semantics/Denotational.lean` for.
-/

section Intro

variable {V : Type} [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}

theorem Statement.reducing.with.intro {σ σ' : LocalState V} {ε : Trace V}
    {name ann bound e}
    (h : ∃ M F v, ExprSemantics.Eval Ξ Ω M e v ∧ Finmap.lookup name M = none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
      match bound with
        | true => σ' = ⟨M.insert name v, F, .none⟩
        | false => ∃ v', ExprSemantics.mem v' v ∧ σ' = ⟨M.insert name v', F, .none⟩) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (GuardedPlusCal.Statement.with name ann bound e) :=
  h

theorem Statement.reducing.await.intro {σ σ' : LocalState V} {ε : Trace V} {e}
    (h : ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ExprSemantics.Eval Ξ Ω M e ExprSemantics.tru ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (GuardedPlusCal.Statement.await e) :=
  h

theorem Statement.reducing.receive.intro {σ σ' : LocalState V} {ε : Trace V}
    {c r coe}
    (h : ∃ M F M' cpath rpath v v' vs,
      List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
      List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧
      ExprSemantics.coerce coe v v' ∧
      Memory.update M r.name rpath v' = .some M' ∧
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M', F.insert ⟨c.name, cpath⟩ vs, .none⟩ ∧
      ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (GuardedPlusCal.Statement.receive c r coe) :=
  h

theorem Statement.reducing.skip.intro {σ σ' : LocalState V} {ε : Trace V}
    (h : ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω GuardedPlusCal.Statement.skip :=
  h

theorem Statement.reducing.goto.intro {σ : LocalState V} {σ' : LocalState V}
    {ε : Trace V} {label}
    (h : ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .some label⟩ ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (GuardedPlusCal.Statement.goto label) :=
  h

theorem Statement.reducing.print.intro {σ σ' : LocalState V} {ε : Trace V} {e}
    (h : ∃ M F v p, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ExprSemantics.Eval Ξ Ω M e v ∧ M.lookup selfName = .some p ∧
      ε = Stream'.Seq.cons (.print p v) 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (GuardedPlusCal.Statement.print e) :=
  h

theorem Statement.reducing.assert.intro {σ σ' : LocalState V} {ε : Trace V} {e}
    (h : ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ExprSemantics.Eval Ξ Ω M e ExprSemantics.tru ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (GuardedPlusCal.Statement.assert e) :=
  h

theorem Statement.reducing.send.intro {σ σ' : LocalState V} {ε : Trace V} {c e}
    (h : ∃ M F v cpath vs p,
      ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some vs ∧ M.lookup selfName = .some p ∧
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F.insert ⟨c.name, cpath⟩ (vs.concat v), .none⟩ ∧
      ε = Stream'.Seq.cons (.send p ⟨c.name, cpath⟩ v) 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (GuardedPlusCal.Statement.send c e) :=
  h

theorem Statement.reducing.assign.intro {σ σ' : LocalState V} {ε : Trace V} {r e}
    (h : ∃ M F M' v rpath,
      ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
      Memory.update M r.name rpath v = .some M' ∧
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M', F, .none⟩ ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (GuardedPlusCal.Statement.assign r e) :=
  h

theorem Statement.aborting.with.intro {σ : LocalState V} {ε : Trace V}
    {name ann bound e}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ match bound with
          | true => False
          | false => ¬ ExprSemantics.isSet v}) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (GuardedPlusCal.Statement.with name ann bound e) :=
  h

theorem Statement.aborting.await.intro {σ : LocalState V} {ε : Trace V} {e}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, ¬ ExprSemantics.isBool v ∧ ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (GuardedPlusCal.Statement.await e) :=
  h

theorem Statement.aborting.receive.intro {σ : LocalState V} {ε : Trace V} {c r coe}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ ({⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
        ∪ {⟨σ, ε⟩ | ∃ M F, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ Ref.pathAborts Ξ Ω M c}
        ∪ {⟨σ, ε⟩ | ∃ M F, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ Ref.pathAborts Ξ Ω M r}
        ∪ {⟨σ, ε⟩ | ∃ M F cpath, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
            List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧ F.lookup ⟨c.name, cpath⟩ = .none}
        ∪ {⟨σ, ε⟩ | ∃ M F cpath v vs, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
            List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
            F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧ ¬ ∃ v', ExprSemantics.coerce coe v v'}
        ∪ {⟨σ, ε⟩ | ∃ M F cpath rpath v v' vs, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
            List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
            List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
            F.lookup ⟨c.name, cpath⟩ = .some (v :: vs) ∧ ExprSemantics.coerce coe v v' ∧
            Memory.update M r.name rpath v' = .none})) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (GuardedPlusCal.Statement.receive c r coe) :=
  h

theorem Statement.aborting.print.intro {σ : LocalState V} {ε : Trace V} {e}
    (h : ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (GuardedPlusCal.Statement.print e) :=
  h

theorem Statement.aborting.assert.intro {σ : LocalState V} {ε : Trace V} {e}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, v ≠ ExprSemantics.tru ∧ ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (GuardedPlusCal.Statement.assert e) :=
  h

theorem Statement.aborting.send.intro {σ : LocalState V} {ε : Trace V} {c e}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts Ξ Ω M c ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
          F.lookup ⟨c.name, cpath⟩ = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (GuardedPlusCal.Statement.send c e) :=
  h

theorem Statement.aborting.assign.intro {σ : LocalState V} {ε : Trace V} {r e}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts Ξ Ω M r ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v rpath,
          ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
          Memory.update M r.name rpath v = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (GuardedPlusCal.Statement.assign r e) :=
  h

end Intro

/-! # Reduction -/

section Reducing

variable {α : Bool → Type} {β γ : Type} [Monoid γ]
  (f : ⦃b : Bool⦄ → α b → Set (β × γ × β))

theorem Block.listReducing_nil : Block.listReducing f [] = Relation.Idle := rfl

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

/-! # Abortion and divergence

  `aborting` and `diverging` share their shape exactly — both are "this element goes wrong, or it
  steps and the rest does" — so the two families of lemmas below are literal mirrors of each other.
-/

section Aborting

variable {α : Bool → Type} {β γ : Type} [Monoid γ]
  (g : ⦃b : Bool⦄ → α b → Set (β × γ))
  (f : ⦃b : Bool⦄ → α b → Set (β × γ × β))

theorem Block.listAborting_nil : Block.listAborting g f [] = ∅ := rfl

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

variable {α : Bool → Type} {β γ : Type} [Monoid γ]
  (d : ⦃b : Bool⦄ → α b → Set (β × γ))
  (f : ⦃b : Bool⦄ → α b → Set (β × γ × β))

/-- **`Block.diverging` *is* `Block.aborting`.** "This element goes wrong, or it steps and the rest
does" is one shape, and the two definitions spell it identically. Saying it as an equation is what
keeps the two families of lemmas below
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

/-- If nothing at the leaf diverges, nothing built from it does either — propagated through the
fold. What lets a language whose statements never diverge (`Statement.diverging = ∅`, both
`GuardedPlusCal` and `NetworkPlusCal`) conclude the same fact at block shape without restating the
induction once per language. -/
theorem Block.diverging_eq_empty {b : Bool} {B : Block α b} (hd : ∀ ⦃b⦄ (x : α b), d x = ∅) :
    Block.diverging d f B = ∅ := by
  rw [Block.diverging_eq_aborting]
  induction B using Block.cons_end_induct with
  | «end» S => rw [Block.aborting_end, hd]
  | cons S B IH =>
    rw [Block.aborting_cons, hd, IH, Set.empty_union, Relation.lcomp₁.right_empty_eq_empty]

end Diverging

/-! # What the flat encoding used to bridge

  Now that `LocalState` itself is flat, a refinement proof needs no translation between an indexed
  and a flat state — `Statement.reducing`/`.aborting` already are the shape `StrongRefinement` wants.
  What survives from the old bridging section are the facts genuinely about this language: no
  statement or block diverges, and a branch's `aborting` in the uniform composed shape a
  `StrongRefinement.Comp` produces. -/

section Unprimed

variable {V : Type} [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}

omit [ExprSemantics V] in
/-- No statement diverges. -/
@[simp] theorem Statement.diverging_eq_empty {b b' : Bool}
    (S : ComputableGuardedPlusCal.Statement b b') : Statement.diverging (V := V) S = ∅ := rfl

/-- No block diverges either — `Statement.diverging_eq_empty` propagated through the fold. -/
@[simp] theorem Statement.blockDiverging_eq_empty {g b : Bool}
    {B : Block (ComputableGuardedPlusCal.Statement g) b} :
    Block.diverging (λ ⦃_⦄ ↦ (Statement.diverging (V := V))) (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) B = ∅ := by
  apply Block.diverging_eq_empty
  intro _ _; rfl

/-- A possibly-empty *list* of Guarded statements — see `NetworkPlusCal.Statement.listReducing`,
which this mirrors. `Guarded2Network`'s per-statement reorder lemmas lift to a list of consumption
assignments through this wrapper, on the Guarded side exactly as on the Network one. -/
def Statement.listReducing (Ξ : OperatorEnv) (Ω : Model V) {g : Bool}
    (A : List (ComputableGuardedPlusCal.Statement g false)) :
    Set (LocalState V × Trace V × LocalState V) :=
  Block.listReducing (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) A

@[inherit_doc Statement.listReducing]
def Statement.listAborting (Ξ : OperatorEnv) (Ω : Model V) {g : Bool}
    (A : List (ComputableGuardedPlusCal.Statement g false)) :
    Set (LocalState V × Trace V) :=
  Block.listAborting (λ ⦃_⦄ ↦ Statement.aborting Ξ Ω) (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) A

theorem Statement.listReducing_nil {g : Bool} :
    Statement.listReducing (V := V) Ξ Ω (g := g) [] = Relation.Idle := rfl

theorem Statement.listReducing_cons {g : Bool} {S : ComputableGuardedPlusCal.Statement g false}
    {A : List (ComputableGuardedPlusCal.Statement g false)} :
    Statement.listReducing (V := V) Ξ Ω (S :: A) =
      Statement.reducing Ξ Ω S ∘ᵣ₂ Statement.listReducing Ξ Ω A := rfl

/-- A statement run splits wherever its list does — `Block.listReducing_append` at a statement
list. -/
theorem Statement.listReducing_append {g : Bool}
    {A B : List (ComputableGuardedPlusCal.Statement g false)} :
    Statement.listReducing (V := V) Ξ Ω (A ++ B) =
      Statement.listReducing Ξ Ω A ∘ᵣ₂ Statement.listReducing Ξ Ω B :=
  Block.listReducing_append _

theorem Statement.listAborting_nil {g : Bool} :
    Statement.listAborting (V := V) Ξ Ω (g := g) [] = ∅ := rfl

theorem Statement.listAborting_cons {g : Bool} {S : ComputableGuardedPlusCal.Statement g false}
    {A : List (ComputableGuardedPlusCal.Statement g false)} :
    Statement.listAborting (V := V) Ξ Ω (S :: A) =
      Statement.aborting Ξ Ω S ∪ Statement.reducing Ξ Ω S ∘ᵣ₁ Statement.listAborting Ξ Ω A := rfl

@[inherit_doc Statement.listReducing_append]
theorem Statement.listAborting_append {g : Bool}
    {A B : List (ComputableGuardedPlusCal.Statement g false)} :
    Statement.listAborting (V := V) Ξ Ω (A ++ B) =
      Statement.listAborting Ξ Ω A ∪ Statement.listReducing Ξ Ω A ∘ᵣ₁ Statement.listAborting Ξ Ω B :=
  Block.listAborting_append _ _

/-- The `match` on the precondition, discharged: `.none` composes with the identity relation and
contributes no aborting runs of its own, which is exactly what `Option.elim` says. The uniform form
is what a `StrongRefinement.Comp` of a precondition half and an action half produces, so this is the
bridge between the definition and every proof about it. -/
theorem AtomicBranch.aborting_eq (B : ComputableGuardedPlusCal.AtomicBranch) :
    AtomicBranch.aborting (V := V) Ξ Ω B =
      B.precondition.elim ∅ (Statement.blockAborting Ξ Ω) ∪
        B.precondition.elim Relation.Idle (Statement.blockReducing Ξ Ω) ∘ᵣ₁
          Statement.blockAborting Ξ Ω B.action := by
  rw [AtomicBranch.aborting]
  cases B.precondition with
  | none => rw [Option.elim, Option.elim, Relation.lcomp₁.left_id_eq, Set.empty_union]
  | some => rfl

end Unprimed

end GuardedPlusCal

end
