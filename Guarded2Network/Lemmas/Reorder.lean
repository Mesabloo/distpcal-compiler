module

meta import CustomPrelude
public import Guarded2Network.PlusCal
public import Guarded2Network.Lemmas.Statement
public import Core.NetworkPlusCal.Semantics.Lemmas

@[expose] public section

/-!
  Commuting an assignment past a guard.

  `processPrecondition` compiles a `receive` into an `await` on the inbox plus two consumption
  assignments, and those assignments are *not* emitted where the `receive` was: they are prepended to
  the branch's action block, so they end up after every guard the precondition still has to run
  (`stepBranch`). What keeps that sound is that each guard is rewritten on the way past —
  `substGuards` substitutes every already-processed assignment's effect into it. This file says
  those two moves cancel.

  The guard constructor is not split on: `with` and `await` differ only in which field carries the
  guard expression. The split that remains is the real one — reducing and aborting are different
  statements, and only the first is an equation.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Expression Memory PathStep OperatorEnv Model)
open GuardedPlusCal (EvalStep FIFOs LocalState Trace)

variable {V : Type} [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}

/-! ## The pass's substitution, and what it does to evaluation -/

/-- `substGuardStmt`'s `with` case. Stated here rather than in `Guarded2Network/PlusCal.lean` for the
same reason `convertActionStmt`'s semantic equations are (`Guarded2Network/Lemmas/Statement.lean`):
the pass file holds the pass, the proof files hold what is proved about it. -/
theorem substGuardStmt_with {r : ComputableGuardedPlusCal.Ref}
    {rhs : ComputablePlusCal.Expression} {x ann bound e} :
    substGuardStmt r rhs (.with x ann bound e) =
      .with x ann bound (Expression.substRef r rhs e) :=
  rfl

@[inherit_doc substGuardStmt_with]
theorem substGuardStmt_await {r : ComputableGuardedPlusCal.Ref}
    {rhs : ComputablePlusCal.Expression} {e} :
    substGuardStmt r rhs (.await e) = .await (Expression.substRef r rhs e) :=
  rfl

/-- No assignments accumulated yet, so nothing is substituted. -/
theorem substGuards_nil {S : ComputableNetworkPlusCal.Statement true false} :
    substGuards [] S = S :=
  rfl

/-- `substGuards` peels its head first — it is a `foldr`, so the *first* accumulated assignment is
the outermost substitution. That direction is what makes the iterated reorder below come out: the
assignments run left to right, and each one is pushed past the guard in the order it was emitted. -/
theorem substGuards_cons {a : ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan}
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {S : ComputableNetworkPlusCal.Statement true false} :
    substGuards (a :: A) S = substGuardStmt a.1 a.2.1 (substGuards A S) := by
  obtain ⟨_, _, _⟩ := a
  rfl

/-- The consumption assignments `processPrecondition` emits for an accumulated `newInstrs` —
`Guarded2Network/PlusCal.lean`'s own `st.newInstrs.map …`, named so that the reorder lemma and the
precondition spec talk about one list rather than two spellings of it. -/
def consumptions
    (A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)) :
    List (ComputableNetworkPlusCal.Statement false false) :=
  A.map λ (r, e, pos) ↦ .assign r e @@ pos

@[inherit_doc consumptions]
theorem consumptions_nil : consumptions [] = [] := rfl

@[inherit_doc consumptions]
theorem consumptions_cons {a : ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan}
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)} :
    consumptions (a :: A) = .assign a.1 a.2.1 :: consumptions A := by
  obtain ⟨_, _, _⟩ := a
  rfl

/-- Every statement `consumptions` emits is an assignment — the trivial reading of its definition,
in the shape `NetworkPlusCal.Statement.listReducing_fifos_of_assigns` asks for. -/
theorem consumptions_all_assign
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)} :
    ∀ S ∈ consumptions A, ∃ r e, S = NetworkPlusCal.Statement.assign r e := by
  intro S hS
  simp only [consumptions, List.mem_map] at hS
  obtain ⟨⟨r, e, pos⟩, -, rfl⟩ := hS
  exact ⟨r, e, rfl⟩

/-- `ExprSemantics.evalSubstRef` at the shape the statement semantics writes reference paths in —
`List.Forall₂ (EvalStep M)` rather than `ResolvesPath`, bridged by `EvalStep.resolvesPath_iff`. Every
branch of the two reorder lemmas needs the transfer in this form, so the conversion happens once. -/
theorem evalSubstRef {r : ComputableGuardedPlusCal.Ref}
    {rhs e : ComputablePlusCal.Expression} {M M' : Memory V} {v w : V}
    {rpath : List (PathStep V)} (hv : ExprSemantics.Eval Ξ Ω M rhs v) (hpath : Ref.EvalArgs Ξ Ω M r rpath)
    (hupd : ComputableTLAPlus.Memory.update M r.name rpath v = some M') :
    ExprSemantics.Eval Ξ Ω M' e w ↔ ExprSemantics.Eval Ξ Ω M (Expression.substRef r rhs e) w :=
  ExprSemantics.evalSubstRef hv (EvalStep.resolvesPath_iff.mp hpath) hupd

/-- The same transfer for a guard that has no value at all: an assignment cannot make an expression
start or stop aborting, once the substitution has been applied to it. -/
theorem abortsSubstRef {r : ComputableGuardedPlusCal.Ref}
    {rhs e : ComputablePlusCal.Expression} {M M' : Memory V} {v : V}
    {rpath : List (PathStep V)} (hv : ExprSemantics.Eval Ξ Ω M rhs v) (hpath : Ref.EvalArgs Ξ Ω M r rpath)
    (hupd : ComputableTLAPlus.Memory.update M r.name rpath v = some M') :
    ExprSemantics.Aborts Ξ Ω M' e ↔ ExprSemantics.Aborts Ξ Ω M (Expression.substRef r rhs e) :=
  ExprSemantics.aborts_congr λ _ ↦ evalSubstRef hv hpath hupd

/-! ## Freshness

  Only the `with` case has a side condition, and only one: the name it binds. The bound name is
  written into the memory the assignment also writes, so unless the two names are distinct the writes
  do not commute; and it is in scope for the assignment's own right-hand side on one side of the
  equation but not the other. `await` binds nothing and needs neither.
-/

/-- What a guard statement must avoid for an assignment to commute past it. Phrased as an
implication from `S`'s shape rather than by cases on `S`, so a caller that does not know which
constructor it has can still discharge it — the same shape `Guarded2Network/Lemmas/Statement.lean`'s
`Fresh` uses for the mailbox. -/
def GuardFresh (r : ComputableGuardedPlusCal.Ref) (rhs : ComputablePlusCal.Expression)
    (S : ComputableNetworkPlusCal.Statement true false) : Prop :=
  ∀ x ann bound e, S = .with x ann bound e →
    x ∉ GuardedPlusCal.Ref.freeVars r ∧ Expression.FreshIn x rhs

/-- Substitution leaves a guard's freshness alone: `substGuardStmt` rewrites the guard *expression*
and nothing else, so the bound name a `with` carries — the only thing `GuardFresh` looks at — comes
through unchanged. What lets the iterated reorder discharge each step's side condition from the
hypothesis about the original statement. -/
theorem GuardFresh.substGuardStmt {r r' : ComputableGuardedPlusCal.Ref}
    {rhs rhs' : ComputablePlusCal.Expression} {S : ComputableNetworkPlusCal.Statement true false}
    (h : GuardFresh r rhs S) : GuardFresh r rhs (Guarded2Network.substGuardStmt r' rhs' S) := by
  cases S with
  | «with» x ann bound e =>
    rintro x' ann' bound' e' heq
    rw [substGuardStmt_with] at heq
    injection heq with hx _ _ _
    subst hx
    exact h x ann bound e rfl
  | await e =>
    rintro _ _ _ _ heq
    rw [substGuardStmt_await] at heq
    contradiction

@[inherit_doc GuardFresh.substGuardStmt]
theorem GuardFresh.substGuards {r : ComputableGuardedPlusCal.Ref}
    {rhs : ComputablePlusCal.Expression}
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {S : ComputableNetworkPlusCal.Statement true false} (h : GuardFresh r rhs S) :
    GuardFresh r rhs (Guarded2Network.substGuards A S) := by
  induction A with
  | nil => exact h
  | cons _ _ IH => rw [substGuards_cons]; exact IH.substGuardStmt

omit [ExprSemantics V] in
/-- Two memories differing only at `x` agree away from `x` — `Ref.EvalArgs.congr_of_fresh`'s
hypothesis, at the one shape a `with` produces it in. -/
theorem lookup_insert_agree {M : Memory V} {x : String} {u : V} :
    ∀ y ≠ x, M.lookup y = (M.insert x u).lookup y :=
  λ _ hy ↦ (Finmap.lookup_insert_of_ne _ hy).symm

omit [ExprSemantics V] in
/-- A reference's own name is one of the names it reads, so freshness against the whole reference
already says the bound name is not the one being written. -/
theorem ne_name_of_fresh {r : ComputableGuardedPlusCal.Ref} {x : String}
    (hx : x ∉ GuardedPlusCal.Ref.freeVars r) : x ≠ r.name :=
  λ h ↦ hx (h ▸ GuardedPlusCal.Ref.name_mem_freeVars r)

/-- Memories agreeing away from a name the reference does not read cannot disagree about whether its
path resolves. Every index expression of the reference reads only names the reference reads
(`Ref.freeVars_of_mem_args`), so `evalLocal` applies segment by segment. -/
theorem pathAborts_congr {M₁ M₂ : Memory V} {r : ComputableGuardedPlusCal.Ref} {x : String}
    (agree : ∀ y ≠ x, M₁.lookup y = M₂.lookup y) (hx : x ∉ GuardedPlusCal.Ref.freeVars r) :
    GuardedPlusCal.Ref.pathAborts Ξ Ω M₁ r ↔ GuardedPlusCal.Ref.pathAborts Ξ Ω M₂ r := by
  rw [GuardedPlusCal.Ref.pathAborts_iff, GuardedPlusCal.Ref.pathAborts_iff]
  refine exists_congr λ e ↦ and_congr_right λ hmem ↦ ?_
  exact ExprSemantics.aborts_congr λ _ ↦ ExprSemantics.evalLocal λ y hy ↦
    agree y λ heq ↦ hx (heq ▸ Ref.freeVars_of_mem_args hmem hy)

@[inherit_doc pathAborts_congr]
theorem pathAborts_insert_iff {M : Memory V} {r : ComputableGuardedPlusCal.Ref} {x : String}
    {u : V} (hx : x ∉ GuardedPlusCal.Ref.freeVars r) :
    GuardedPlusCal.Ref.pathAborts Ξ Ω (M.insert x u) r ↔ GuardedPlusCal.Ref.pathAborts Ξ Ω M r :=
  (pathAborts_congr lookup_insert_agree hx).symm

/-- An assignment either aborts or takes a step. The four aborting clauses are jointly the exact
complement of "the reference resolves, the right-hand side has a value, and the update succeeds", so
`assign` has no third, *blocking* outcome — unlike a guard, which is why the aborting reorder below
is an inclusion where the reducing one is an equation. Classical, twice over: `Aborts` and
`Ref.not_pathAborts_iff` both turn "no derivation exists" into a value. -/
theorem assign_aborts_or_steps {r : ComputableGuardedPlusCal.Ref}
    {rhs : ComputablePlusCal.Expression} {M : Memory V} {F : FIFOs V} :
    (⟨⟨M, F, .none⟩, 1⟩ : LocalState V × Trace V) ∈
        NetworkPlusCal.Statement.aborting Ξ Ω (.assign r rhs) ∨
      ∃ v rpath M', (ExprSemantics.Eval Ξ Ω M rhs v) ∧ Ref.EvalArgs Ξ Ω M r rpath ∧
        ComputableTLAPlus.Memory.update M r.name rpath v = some M' := by classical
  by_cases hname : r.name ∈ M
  · by_cases habort : ExprSemantics.Aborts Ξ Ω M rhs
    · exact .inl (NetworkPlusCal.Statement.aborting.assign.iff.mpr
        ⟨M, F, rfl, rfl, .inr (.inl habort)⟩)
    · by_cases hpath : GuardedPlusCal.Ref.pathAborts Ξ Ω M r
      · exact .inl (NetworkPlusCal.Statement.aborting.assign.iff.mpr
          ⟨M, F, rfl, rfl, .inr (.inr (.inl hpath))⟩)
      · obtain ⟨v, hv⟩ := not_not.mp habort
        obtain ⟨rpath, hrpath⟩ := GuardedPlusCal.Ref.not_pathAborts_iff.mp hpath
        by_cases hupd : ComputableTLAPlus.Memory.update M r.name rpath v = none
        · exact .inl (NetworkPlusCal.Statement.aborting.assign.iff.mpr
            ⟨M, F, rfl, rfl, .inr (.inr (.inr ⟨v, rpath, hv, hrpath, hupd⟩))⟩)
        · obtain ⟨M', hM'⟩ := Option.ne_none_iff_exists'.mp hupd
          exact .inr ⟨v, rpath, M', hv, hrpath, hM'⟩
  · exact .inl (NetworkPlusCal.Statement.aborting.assign.iff.mpr ⟨M, F, rfl, rfl, .inl hname⟩)

/-- Binding a name the assignment neither reads nor writes cannot make it abort — each of the four
clauses transfers back to the unbound memory. Only this direction is needed: the aborting reorder
moves an abort that happened *after* a `with`'s bind to before it. -/
theorem assign_aborting_of_insert {r : ComputableGuardedPlusCal.Ref}
    {rhs : ComputablePlusCal.Expression} {M : Memory V} {F : FIFOs V} {x : String} {u : V}
    {ε : Trace V} (hx : x ∉ GuardedPlusCal.Ref.freeVars r) (hrhs : Expression.FreshIn x rhs)
    (h : (⟨⟨(M.insert x u), F, .none⟩, ε⟩ : LocalState V × Trace V) ∈
      NetworkPlusCal.Statement.aborting Ξ Ω (.assign r rhs)) :
    (⟨⟨M, F, .none⟩, ε⟩ : LocalState V × Trace V) ∈
      NetworkPlusCal.Statement.aborting Ξ Ω (.assign r rhs) := by
  have hne : x ≠ r.name := ne_name_of_fresh hx
  obtain ⟨M₀, F₀, hstate, rfl, hd⟩ := NetworkPlusCal.Statement.aborting.assign.iff.mp h
  injection hstate with hM hF'
  subst hM
  injection hF' with hF _
  subst hF
  refine NetworkPlusCal.Statement.aborting.assign.iff.mpr ⟨M, F, rfl, rfl, ?_⟩
  rcases hd with hname | habort | hpath | ⟨v, rpath, hv, hrpath, hupd⟩
  · exact .inl λ hmem ↦ hname (Finmap.mem_insert.mpr (.inr hmem))
  · exact .inr (.inl ((ExprSemantics.aborts_congr λ _ ↦ eval_insert_of_fresh hrhs).mp habort))
  · exact .inr (.inr (.inl ((pathAborts_insert_iff hx).mp hpath)))
  · refine .inr (.inr (.inr ⟨v, rpath, (eval_insert_of_fresh hrhs).mp hv,
      (Ref.EvalArgs.congr_of_fresh lookup_insert_agree hx).mpr hrpath, ?_⟩))
    exact Memory.update_none_transfer (lookup_insert_agree r.name (Ne.symm hne)) hupd

/-! ## The pair -/

/-- **Reducing.** An assignment commutes with a following guard, provided the guard's
substituted form is what runs on the other side. An equation, not an inclusion: every run of one side
is a run of the other, with the same trace — both sides take two silent steps.

The `with` case is where `Memory` being a `Finmap` is load-bearing. The two sides bind the same two
names to the same two values in opposite orders, so the memories they reach are equal only once
insertion order stops being observable (`ComputableTLAPlus.Memory`). -/
theorem reorder_assign_guard {r : ComputableGuardedPlusCal.Ref}
    {rhs : ComputablePlusCal.Expression} {S : ComputableNetworkPlusCal.Statement true false}
    (fresh : GuardFresh r rhs S) :
    NetworkPlusCal.Statement.reducing (V := V) Ξ Ω (.assign r rhs) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing Ξ Ω S =
      NetworkPlusCal.Statement.reducing Ξ Ω (substGuardStmt r rhs S) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing (V := V) Ξ Ω (.assign r rhs) := by
  cases S with
  | «with» x ann bound e =>
    obtain ⟨hx, hrhs⟩ := fresh x ann bound e rfl
    have hne : x ≠ r.name := ne_name_of_fresh hx
    rw [substGuardStmt_with]
    ext ⟨σ, ε, σ''⟩
    iff_rintro ⟨mid, ε₁, ε₂, hassign, hguard, rfl⟩ ⟨mid, ε₁, ε₂, hguard, hassign, rfl⟩
    · obtain ⟨M, F, M', v, rpath, hv, hpath, hupd, rfl, rfl, rfl⟩ :=
        NetworkPlusCal.Statement.reducing.assign.elim hassign
      obtain ⟨M₀, F₀, w, u, hw, hxnone, hbv, hstate, rfl, rfl⟩ :=
        NetworkPlusCal.Statement.reducing.with.iff.mp hguard
      injection hstate with hM hF'
      subst hM
      injection hF' with hF _
      subst hF
      refine ⟨⟨(M.insert x u), F, .none⟩, 1, 1, ?_, ?_, rfl⟩
      · refine NetworkPlusCal.Statement.reducing.with.iff.mpr
          ⟨M, F, w, u, (evalSubstRef hv hpath hupd).mp hw, ?_, hbv, rfl, rfl, rfl⟩
        exact (Memory.lookup_update_ne hupd hne).symm.trans hxnone
      · exact NetworkPlusCal.Statement.reducing.assign.intro
          ⟨M.insert x u, F, M'.insert x u, v, rpath, (eval_insert_of_fresh hrhs).mpr hv,
            (Ref.EvalArgs.congr_of_fresh lookup_insert_agree hx).mp hpath,
            (ComputableTLAPlus.Memory.update_insert_iff hne).mp ⟨M', hupd, rfl⟩, rfl, rfl, rfl⟩
    · obtain ⟨M, F, w, u, hw, hxnone, hbv, rfl, rfl, rfl⟩ :=
        NetworkPlusCal.Statement.reducing.with.iff.mp hguard
      obtain ⟨M₀, F₀, M₂, v, rpath, hv, hpath, hupd, hstate, rfl, rfl⟩ :=
        NetworkPlusCal.Statement.reducing.assign.elim hassign
      injection hstate with hM hF'
      subst hM
      injection hF' with hF _
      subst hF
      obtain ⟨M', hupd', rfl⟩ := (ComputableTLAPlus.Memory.update_insert_iff hne).mpr hupd
      have hv' : ExprSemantics.Eval Ξ Ω M rhs v := (eval_insert_of_fresh hrhs).mp hv
      have hpath' : Ref.EvalArgs Ξ Ω M r rpath :=
        (Ref.EvalArgs.congr_of_fresh lookup_insert_agree hx).mpr hpath
      refine ⟨⟨M', F, .none⟩, 1, 1, ?_, ?_, rfl⟩
      · exact NetworkPlusCal.Statement.reducing.assign.intro
          ⟨M, F, M', v, rpath, hv', hpath', hupd', rfl, rfl, rfl⟩
      · refine NetworkPlusCal.Statement.reducing.with.iff.mpr
          ⟨M', F, w, u, (evalSubstRef hv' hpath' hupd').mpr hw, ?_, hbv, rfl, rfl, rfl⟩
        exact (Memory.lookup_update_ne hupd' hne).trans hxnone
  | await e =>
    rw [substGuardStmt_await]
    ext ⟨σ, ε, σ''⟩
    iff_rintro ⟨mid, ε₁, ε₂, hassign, hguard, rfl⟩ ⟨mid, ε₁, ε₂, hguard, hassign, rfl⟩
    · obtain ⟨M, F, M', v, rpath, hv, hpath, hupd, rfl, rfl, rfl⟩ :=
        NetworkPlusCal.Statement.reducing.assign.elim hassign
      obtain ⟨M₀, F₀, hstate, rfl, htru, rfl⟩ :=
        NetworkPlusCal.Statement.reducing.await.elim hguard
      injection hstate with hM hF'
      subst hM
      injection hF' with hF _
      subst hF
      refine ⟨⟨M, F, .none⟩, 1, 1, ?_, ?_, rfl⟩
      · exact NetworkPlusCal.Statement.reducing.await.intro
          ⟨M, F, rfl, rfl, (evalSubstRef hv hpath hupd).mp htru, rfl⟩
      · exact NetworkPlusCal.Statement.reducing.assign.intro
          ⟨M, F, M', v, rpath, hv, hpath, hupd, rfl, rfl, rfl⟩
    · obtain ⟨M, F, rfl, rfl, htru, rfl⟩ :=
        NetworkPlusCal.Statement.reducing.await.elim hguard
      obtain ⟨M₀, F₀, M', v, rpath, hv, hpath, hupd, hstate, rfl, rfl⟩ :=
        NetworkPlusCal.Statement.reducing.assign.elim hassign
      injection hstate with hM hF'
      subst hM
      injection hF' with hF _
      subst hF
      refine ⟨⟨M', F, .none⟩, 1, 1, ?_, ?_, rfl⟩
      · exact NetworkPlusCal.Statement.reducing.assign.intro
          ⟨M, F, M', v, rpath, hv, hpath, hupd, rfl, rfl, rfl⟩
      · exact NetworkPlusCal.Statement.reducing.await.intro
          ⟨M', F, rfl, rfl, (evalSubstRef hv hpath hupd).mpr htru, rfl⟩

/-- **Iterated.** The pass never substitutes one assignment: `substGuards` folds *every*
consumption assignment accumulated so far into the guard, and emits them, in list order, after it. So
the single-assignment equation lifts to the whole list — which is the form
`stepPrecondition`'s proof needs, `substGuards` being what `stepStatement` applies.

The `foldr` in `substGuards` is what makes the induction come out: its head is the *outermost*
substitution and the *first* assignment to run, so peeling one entry peels one factor off each side
at once. -/
theorem reorder_assigns_guard
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {S : ComputableNetworkPlusCal.Statement true false}
    (fresh : ∀ a ∈ A, GuardFresh a.1 a.2.1 S) :
    NetworkPlusCal.Statement.listReducing (V := V) Ξ Ω (consumptions A) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing Ξ Ω S =
      NetworkPlusCal.Statement.reducing Ξ Ω (substGuards A S) ∘ᵣ₂
        NetworkPlusCal.Statement.listReducing (V := V) Ξ Ω (consumptions A) := by
  induction A with
  | nil =>
    rw [consumptions_nil, NetworkPlusCal.Statement.listReducing_nil, substGuards_nil,
      Relation.lcomp₂.left_id_eq, Relation.lcomp₂.right_id_eq]
  | cons a A IH =>
    rw [consumptions_cons, NetworkPlusCal.Statement.listReducing_cons,
      ← Relation.lcomp₂.assoc, IH λ b hb ↦ fresh b (List.mem_cons_of_mem _ hb),
      Relation.lcomp₂.assoc, reorder_assign_guard (fresh a List.mem_cons_self).substGuards,
      ← Relation.lcomp₂.assoc, substGuards_cons]

/-- An `await` binds nothing, so nothing can clash with it. `GuardFresh`'s whole content is about a
`with`'s binder; on the other guard constructor it holds outright. -/
theorem GuardFresh.await {r : ComputableGuardedPlusCal.Ref} {rhs e : ComputablePlusCal.Expression} :
    GuardFresh r rhs (.await e) := by
  intro _ _ _ _ h
  nomatch h

/-- `reorder_assign_guard`, restated under its old "flat encoding" name. Now that `LocalState`
itself is flat, the two statements are the same fact word for word — nothing to bridge. Kept as a
separate name only because `reorder_assigns_guard'` below still calls it that; not worth a rename
sweep across every call site in this phase. -/
theorem reorder_assign_guard' {r : ComputableGuardedPlusCal.Ref}
    {rhs : ComputablePlusCal.Expression} {S : ComputableNetworkPlusCal.Statement true false}
    (fresh : GuardFresh r rhs S) :
    NetworkPlusCal.Statement.reducing (V := V) Ξ Ω (.assign r rhs) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing Ξ Ω S =
      NetworkPlusCal.Statement.reducing Ξ Ω (substGuardStmt r rhs S) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing (V := V) Ξ Ω (.assign r rhs) :=
  reorder_assign_guard fresh

/-- `reorder_assigns_guard` in the flat encoding. The list induction is redone rather than
transported: the unprimed-to-primed bridge is stated for a *composition of two statements*, and a
list has no such shape at its `nil` end — `Relation.Idle` on `LocalState` relates states carrying a
label, which no image of an unprimed relation ever does. Each *step* of the induction does have the
shape, which is why this proof is the unprimed one verbatim with `reorder_assign_guard'` swapped
in. -/
theorem reorder_assigns_guard'
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {S : ComputableNetworkPlusCal.Statement true false}
    (fresh : ∀ a ∈ A, GuardFresh a.1 a.2.1 S) :
    NetworkPlusCal.Statement.listReducing (V := V) Ξ Ω (consumptions A) ∘ᵣ₂
        NetworkPlusCal.Statement.reducing Ξ Ω S =
      NetworkPlusCal.Statement.reducing Ξ Ω (substGuards A S) ∘ᵣ₂
        NetworkPlusCal.Statement.listReducing (V := V) Ξ Ω (consumptions A) := by
  induction A with
  | nil =>
    rw [consumptions_nil, NetworkPlusCal.Statement.listReducing_nil, substGuards_nil,
      Relation.lcomp₂.left_id_eq, Relation.lcomp₂.right_id_eq]
  | cons a A IH =>
    rw [consumptions_cons, NetworkPlusCal.Statement.listReducing_cons,
      ← Relation.lcomp₂.assoc, IH λ b hb ↦ fresh b (List.mem_cons_of_mem _ hb),
      Relation.lcomp₂.assoc, reorder_assign_guard' (fresh a List.mem_cons_self).substGuards,
      ← Relation.lcomp₂.assoc, substGuards_cons]

/-- **Aborting.** The same commutation for the runs that fail — and here only an inclusion. Every
way the compiled order `guard[subst] ; assign` can abort is a way the source order `assign ; guard`
can, but not conversely: a guard has a third outcome an assignment does not, since it can *block*. A
state where the assignment aborts and the substituted guard blocks is a source abort and not a target
one, so the two sets are not equal.

Each union member is handled once. A target abort *in the guard* becomes a source assignment step
followed by the same abort, or an abort of that assignment (`assign_aborts_or_steps` — there is no
third case). A target abort *in the assignment* becomes an immediate source abort, the guard having
no way to change whether the assignment fails. -/
theorem reorder_assign_guard_abort {r : ComputableGuardedPlusCal.Ref}
    {rhs : ComputablePlusCal.Expression} {S : ComputableNetworkPlusCal.Statement true false}
    (fresh : GuardFresh r rhs S) :
    NetworkPlusCal.Statement.aborting Ξ Ω (substGuardStmt r rhs S) ∪
        NetworkPlusCal.Statement.reducing Ξ Ω (substGuardStmt r rhs S) ∘ᵣ₁
          NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (.assign r rhs) ≤
      NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (.assign r rhs) ∪
        NetworkPlusCal.Statement.reducing (V := V) Ξ Ω (.assign r rhs) ∘ᵣ₁
          NetworkPlusCal.Statement.aborting Ξ Ω S := by
  cases S with
  | «with» x ann bound e =>
    obtain ⟨hx, hrhs⟩ := fresh x ann bound e rfl
    rw [substGuardStmt_with]
    rintro ⟨σ, ε⟩ (hguard | ⟨mid, ε₁, ε₂, hred, habort, rfl⟩)
    · obtain ⟨M, F, rfl, rfl, hd⟩ := NetworkPlusCal.Statement.aborting.with.iff.mp hguard
      rcases assign_aborts_or_steps (r := r) (rhs := rhs) (M := M) (F := F) with
        hab | ⟨v, rpath, M', hv, hpath, hupd⟩
      · exact .inl hab
      · refine .inr ⟨⟨M', F, .none⟩, 1, 1, NetworkPlusCal.Statement.reducing.assign.intro
          ⟨M, F, M', v, rpath, hv, hpath, hupd, rfl, rfl, rfl⟩, ?_, (one_mul 1).symm⟩
        refine NetworkPlusCal.Statement.aborting.with.iff.mpr ⟨M', F, rfl, rfl, ?_⟩
        rcases hd with hab | ⟨w, hw, hbound, hset⟩
        · exact .inl ((abortsSubstRef hv hpath hupd).mpr hab)
        · exact .inr ⟨w, (evalSubstRef hv hpath hupd).mpr hw, hbound, hset⟩
    · obtain ⟨M, F, w, u, -, -, -, rfl, rfl, rfl⟩ :=
        NetworkPlusCal.Statement.reducing.with.iff.mp hred
      rw [one_mul]
      exact .inl (assign_aborting_of_insert hx hrhs habort)
  | await e =>
    rw [substGuardStmt_await]
    rintro ⟨σ, ε⟩ (hguard | ⟨mid, ε₁, ε₂, hred, habort, rfl⟩)
    · obtain ⟨M, F, rfl, rfl, hd⟩ := NetworkPlusCal.Statement.aborting.await.iff.mp hguard
      rcases assign_aborts_or_steps (r := r) (rhs := rhs) (M := M) (F := F) with
        hab | ⟨v, rpath, M', hv, hpath, hupd⟩
      · exact .inl hab
      · refine .inr ⟨⟨M', F, .none⟩, 1, 1, NetworkPlusCal.Statement.reducing.assign.intro
          ⟨M, F, M', v, rpath, hv, hpath, hupd, rfl, rfl, rfl⟩, ?_, (one_mul 1).symm⟩
        refine NetworkPlusCal.Statement.aborting.await.iff.mpr ⟨M', F, rfl, rfl, ?_⟩
        rcases hd with hab | ⟨w, hw, hbool⟩
        · exact .inl ((abortsSubstRef hv hpath hupd).mpr hab)
        · exact .inr ⟨w, (evalSubstRef hv hpath hupd).mpr hw, hbool⟩
    · obtain ⟨M, F, rfl, rfl, -, rfl⟩ := NetworkPlusCal.Statement.reducing.await.elim hred
      rw [one_mul]
      exact .inl habort

/-- `reorder_assign_guard_abort`, restated under its old "flat encoding" name — see
`reorder_assign_guard'` for why the name survives unrenamed. -/
theorem reorder_assign_guard_abort' {r : ComputableGuardedPlusCal.Ref}
    {rhs : ComputablePlusCal.Expression} {S : ComputableNetworkPlusCal.Statement true false}
    (fresh : GuardFresh r rhs S) :
    NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (substGuardStmt r rhs S) ∪
        NetworkPlusCal.Statement.reducing Ξ Ω (substGuardStmt r rhs S) ∘ᵣ₁
          NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (.assign r rhs) ≤
      NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (.assign r rhs) ∪
        NetworkPlusCal.Statement.reducing (V := V) Ξ Ω (.assign r rhs) ∘ᵣ₁
          NetworkPlusCal.Statement.aborting Ξ Ω S :=
  reorder_assign_guard_abort fresh

/-- **The whole accumulator past one source-written guard, for the runs that fail.**
`reorder_assigns_guard'`'s aborting twin, and an inclusion for the same reason the one-assignment
case is: the compiled order can only abort where the source order can.

The induction is `reorder_assigns_guard'`'s, with `Relation.lcomp₁.commute_step` in place of the
`rw` chain — the algebra of moving an abort set past a composition is the same at every step, and
saying it once is what keeps the two orderings' bookkeeping out of this proof. -/
theorem reorder_assigns_guard_abort'
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {S : ComputableNetworkPlusCal.Statement true false}
    (fresh : ∀ a ∈ A, GuardFresh a.1 a.2.1 S) :
    NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (substGuards A S) ∪
        NetworkPlusCal.Statement.reducing Ξ Ω (substGuards A S) ∘ᵣ₁
          NetworkPlusCal.Statement.listAborting Ξ Ω (consumptions A) ≤
      NetworkPlusCal.Statement.listAborting (V := V) Ξ Ω (consumptions A) ∪
        NetworkPlusCal.Statement.listReducing Ξ Ω (consumptions A) ∘ᵣ₁
          NetworkPlusCal.Statement.aborting Ξ Ω S := by
  induction A with
  | nil =>
    rw [consumptions_nil, substGuards_nil, NetworkPlusCal.Statement.listAborting_nil,
      NetworkPlusCal.Statement.listReducing_nil, Relation.lcomp₁.right_empty_eq_empty,
      Relation.lcomp₁.left_id_eq, Set.union_empty, Set.empty_union]
  | cons a A IH =>
    rw [consumptions_cons, substGuards_cons, NetworkPlusCal.Statement.listAborting_cons,
      NetworkPlusCal.Statement.listReducing_cons, Relation.lcomp₁.union_lcomp₂]
    refine Relation.lcomp₁.commute_step
      (reorder_assign_guard' (fresh a List.mem_cons_self).substGuards).symm
      (reorder_assign_guard_abort' (fresh a List.mem_cons_self).substGuards) le_rfl ?_
    exact IH λ b hb ↦ fresh b (List.mem_cons_of_mem _ hb)

/-- **One consumption pair past a source-written guard, for the runs that *block*.**
`reorder_assign_guard_abort`'s blocking twin. Blocking is terminal — the guard never reaches the
assignment — so the only input is the substituted guard blocking, and it becomes either the
assignment aborting (it could not run) or the assignment running and the plain guard blocking after
(`assign_aborts_or_steps` — the substitution *is* the assignment). -/
theorem reorder_assign_guard_block {r : ComputableGuardedPlusCal.Ref}
    {rhs : ComputablePlusCal.Expression} {S : ComputableNetworkPlusCal.Statement true false}
    (fresh : GuardFresh r rhs S) :
    NetworkPlusCal.Statement.blocking Ξ Ω (substGuardStmt r rhs S) ≤
      NetworkPlusCal.Statement.aborting (V := V) Ξ Ω (.assign r rhs) ∪
        NetworkPlusCal.Statement.reducing (V := V) Ξ Ω (.assign r rhs) ∘ᵣ₁
          NetworkPlusCal.Statement.blocking Ξ Ω S := by
  cases S with
  | «with» x ann bound e =>
    rw [substGuardStmt_with]
    rintro ⟨σ, ε⟩ ⟨M, F, v, hv, rfl, rfl, hbound⟩
    rcases assign_aborts_or_steps (r := r) (rhs := rhs) (M := M) (F := F) with
      hab | ⟨w, rpath, M', hw, hpath, hupd⟩
    · exact .inl hab
    · exact .inr ⟨⟨M', F, .none⟩, 1, 1, NetworkPlusCal.Statement.reducing.assign.intro
        ⟨M, F, M', w, rpath, hw, hpath, hupd, rfl, rfl, rfl⟩,
        ⟨M', F, v, (evalSubstRef hw hpath hupd).mpr hv, rfl, rfl, hbound⟩, (one_mul 1).symm⟩
  | await e =>
    rw [substGuardStmt_await]
    rintro ⟨σ, ε⟩ ⟨M, F, v, hbool, hne, hv, rfl, rfl⟩
    rcases assign_aborts_or_steps (r := r) (rhs := rhs) (M := M) (F := F) with
      hab | ⟨w, rpath, M', hw, hpath, hupd⟩
    · exact .inl hab
    · exact .inr ⟨⟨M', F, .none⟩, 1, 1, NetworkPlusCal.Statement.reducing.assign.intro
        ⟨M, F, M', w, rpath, hw, hpath, hupd, rfl, rfl, rfl⟩,
        ⟨M', F, v, hbool, hne, (evalSubstRef hw hpath hupd).mpr hv, rfl, rfl⟩, (one_mul 1).symm⟩

/-- **The whole accumulator past one source-written guard, for the runs that block.**
`reorder_assigns_guard_abort'`'s blocking twin — the accumulated pairs either abort somewhere or run
in full and leave the plain guard blocking. -/
theorem reorder_assigns_guard_block
    {A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan)}
    {S : ComputableNetworkPlusCal.Statement true false}
    (fresh : ∀ a ∈ A, GuardFresh a.1 a.2.1 S) :
    NetworkPlusCal.Statement.blocking (V := V) Ξ Ω (substGuards A S) ≤
      NetworkPlusCal.Statement.listAborting (V := V) Ξ Ω (consumptions A) ∪
        NetworkPlusCal.Statement.listReducing Ξ Ω (consumptions A) ∘ᵣ₁
          NetworkPlusCal.Statement.blocking Ξ Ω S := by
  induction A with
  | nil =>
    rw [consumptions_nil, substGuards_nil, NetworkPlusCal.Statement.listAborting_nil,
      NetworkPlusCal.Statement.listReducing_nil, Relation.lcomp₁.left_id_eq, Set.empty_union]
  | cons a A IH =>
    rw [consumptions_cons, substGuards_cons, NetworkPlusCal.Statement.listAborting_cons,
      NetworkPlusCal.Statement.listReducing_cons, Relation.lcomp₁.union_lcomp₂]
    refine le_trans (reorder_assign_guard_block (fresh a List.mem_cons_self).substGuards) ?_
    exact Set.union_subset_union le_rfl
      (Relation.lcomp₁.mono le_rfl (IH λ b hb ↦ fresh b (List.mem_cons_of_mem _ hb)))

/-- **The consumption assignments are total.** From any state, the whole list either reduces to some
state or aborts — an `assign` has no third outcome (`assign_aborts_or_steps`), and the fifo map is
untouched throughout. What the blocking walk feeds `WalkInv`'s reducing/aborting refinement: at the
point a compiled guard blocks, the pending pairs have not run, and this is how they are completed so
the refinement applies. -/
theorem consumptions_total
    (A : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan))
    (M : Memory V) (F : FIFOs V) :
    (⟨(⟨M, F, .none⟩ : LocalState V), (1 : Trace V)⟩ : LocalState V × Trace V) ∈
        NetworkPlusCal.Statement.listAborting Ξ Ω (consumptions A) ∨
      ∃ M', (⟨(⟨M, F, .none⟩ : LocalState V), (1 : Trace V), (⟨M', F, .none⟩ : LocalState V)⟩ :
        LocalState V × Trace V × LocalState V) ∈
          NetworkPlusCal.Statement.listReducing Ξ Ω (consumptions A) := by
  induction A generalizing M with
  | nil =>
    exact .inr ⟨M, by rw [consumptions_nil, NetworkPlusCal.Statement.listReducing_nil]; exact ⟨rfl, rfl⟩⟩
  | cons a A IH =>
    rw [consumptions_cons, NetworkPlusCal.Statement.listAborting_cons,
      NetworkPlusCal.Statement.listReducing_cons]
    rcases assign_aborts_or_steps (r := a.1) (rhs := a.2.1) (M := M) (F := F) with
      hab | ⟨v, rpath, M', hv, hpath, hupd⟩
    · exact .inl (Set.mem_union_left _ hab)
    · have hstep : (⟨(⟨M, F, .none⟩ : LocalState V), (1 : Trace V), (⟨M', F, .none⟩ : LocalState V)⟩ :
          LocalState V × Trace V × LocalState V) ∈
            NetworkPlusCal.Statement.reducing Ξ Ω (.assign a.1 a.2.1) :=
        NetworkPlusCal.Statement.reducing.assign.intro ⟨M, F, M', v, rpath, hv, hpath, hupd, rfl, rfl, rfl⟩
      rcases IH M' with hab' | ⟨M'', hred'⟩
      · exact .inl (Set.mem_union_right _ ⟨_, 1, 1, hstep, hab', (one_mul 1).symm⟩)
      · exact .inr ⟨M'', _, 1, 1, hstep, hred', (one_mul 1).symm⟩

end Guarded2Network

end
