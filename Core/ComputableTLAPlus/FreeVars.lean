module

meta import CustomPrelude
public import Core.ComputableTLAPlus.Syntax
public import Core.ComputableTLAPlus.Subst
public import Core.GuardedPlusCal.Syntax
public import Mathlib.Data.Finset.Basic

@[expose] public section


/-!
  Metatheory for `Expression.freeVars` (defined in `Subst.lean`): membership lemmas that unfold
  `freeVars`'s `foldl (· ∪ ·)` list cases to plain `∃ e ∈ es, …`, plus the same `freeVars`
  vocabulary lifted over `ComputableGuardedPlusCal`.
-/

namespace ComputableTLAPlus

/-- `x` does not occur free in `e` — the freshness side condition every binder-introducing
lemma needs. -/
def Expression.FreshIn {α} (x : String) (e : Expression α) : Prop := x ∉ e.freeVars

/-- If `x` avoids every name `e` could possibly read, `x` isn't one of them. The bridge from a
scope-membership fact (`WellFormedness.WellScoped`'s vocabulary) to an actual freshness fact
(`ExprSemantics.evalSubst`'s vocabulary): a `with`'s bound name is fresh against `inScope` by
construction, and a substituted-in expression's free variables are always a subset of `inScope`
(it can only mention already-declared names), so the two never collide. -/
theorem Expression.not_mem_of_fresh {α} {x : String} {inScope : List String} {e : Expression α}
    (fresh : x ∉ inScope) (sub : ∀ z ∈ e.freeVars, z ∈ inScope) : x ∉ e.freeVars :=
  λ h ↦ fresh (sub x h)

/-! ### Membership lemmas

`freeVars`'s list cases fold `(· ∪ ·)` over `es.attach.map (…)`; these unfold that fold to a plain
`∃ e ∈ es, …`, so `evalLocal`/`evalSubst`'s inductions can move a memory-agreement hypothesis from
a compound expression down to its components. -/

private theorem mem_foldl_union {z : String} :
    ∀ {l : List (Finset String)} {s : Finset String},
      z ∈ l.foldl (· ∪ ·) s ↔ z ∈ s ∨ ∃ t ∈ l, z ∈ t
  | [], _ => by simp
  | hd :: tl, s => by
    rw [List.foldl_cons, mem_foldl_union, Finset.mem_union]
    constructor
    · rintro ((hs | hhd) | ⟨t, ht, hz⟩)
      · exact .inl hs
      · exact .inr ⟨hd, List.mem_cons_self, hhd⟩
      · exact .inr ⟨t, List.mem_cons_of_mem _ ht, hz⟩
    · rintro (hs | ⟨t, ht, hz⟩)
      · exact .inl (.inl hs)
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact .inl (.inr hz)
        · exact .inr ⟨t, ht, hz⟩

private theorem mem_foldl_union_attach {α} {z : String} {l : List α}
    {g : {x // x ∈ l} → Finset String} :
    z ∈ (l.attach.map g).foldl (· ∪ ·) ∅ ↔ ∃ x, z ∈ g x := by
  simp only [mem_foldl_union, Finset.notMem_empty, false_or, List.mem_map, List.mem_attach,
    true_and]
  exact ⟨fun ⟨_, ⟨a, rfl⟩, hz⟩ ↦ ⟨a, hz⟩, fun ⟨a, hz⟩ ↦ ⟨g a, ⟨a, rfl⟩, hz⟩⟩

namespace Expression

variable {α : Type} {z : String}

theorem mem_freeVars_opCall {f : Expression α} {es : List (Expression α)} :
    z ∈ (Expression.opCall f es).freeVars ↔ z ∈ f.freeVars ∨ ∃ e ∈ es, z ∈ e.freeVars := by
  rw [freeVars, Finset.mem_union, mem_foldl_union_attach, Subtype.exists]; simp only [exists_prop]

theorem mem_freeVars_set {es : List (Expression α)} {τ : α} :
    z ∈ (Expression.set es τ).freeVars ↔ ∃ e ∈ es, z ∈ e.freeVars := by
  rw [freeVars, mem_foldl_union_attach, Subtype.exists]; simp only [exists_prop]

theorem mem_freeVars_seq {es : List (Expression α)} {τ : α} :
    z ∈ (Expression.seq es τ).freeVars ↔ ∃ e ∈ es, z ∈ e.freeVars := by
  rw [freeVars, mem_foldl_union_attach, Subtype.exists]; simp only [exists_prop]

theorem mem_freeVars_tuple {es : List (α × Expression α)} :
    z ∈ (Expression.tuple es).freeVars ↔ ∃ e ∈ es, z ∈ e.2.freeVars := by
  rw [freeVars, mem_foldl_union_attach, Subtype.exists]; simp only [exists_prop, Prod.exists]

theorem mem_freeVars_record {fs : List (α × String × Expression α)} :
    z ∈ (Expression.record fs).freeVars ↔ ∃ f ∈ fs, z ∈ f.2.2.freeVars := by
  rw [freeVars, mem_foldl_union_attach, Subtype.exists]; simp only [exists_prop, Prod.exists]

theorem mem_freeVars_case {bs : List (Expression α × Expression α)}
    {other : Option (Expression α)} {τ : α} :
    z ∈ (Expression.case bs other τ).freeVars ↔
      (∃ b ∈ bs, z ∈ b.1.freeVars ∨ z ∈ b.2.freeVars) ∨
      ∃ e, other = some e ∧ z ∈ e.freeVars := by
  rewrite [freeVars.eq_def]
  simp only []
  rewrite [Finset.mem_union, mem_foldl_union_attach, Subtype.exists]
  simp only [exists_prop, Finset.mem_union]
  refine or_congr Iff.rfl ?_
  cases other with
  | none => simp
  | some e => simp

theorem mem_freeVars_except {f : Expression α} {τ : α}
    {upds : List (List (String ⊕ Expression α) × Expression α)} :
    z ∈ (Expression.except f τ upds).freeVars ↔
      z ∈ f.freeVars ∨ ∃ u ∈ upds,
        (∃ e, Sum.inr e ∈ u.1 ∧ z ∈ e.freeVars) ∨ z ∈ u.2.freeVars := by
  rewrite [freeVars.eq_def]
  simp only [Finset.mem_union, mem_foldl_union_attach, Subtype.exists]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨u, hu, hbody⟩
    refine ⟨u, hu, ?_⟩
    rcases hbody with ⟨s, hs, hzs⟩ | hr
    · cases s with
      | inl => simp at hzs
      | inr e => exact .inl ⟨e, hs, by simpa using hzs⟩
    · exact .inr hr
  · rintro ⟨u, hu, hbody⟩
    refine ⟨u, hu, ?_⟩
    rcases hbody with ⟨e, he, hze⟩ | hr
    · exact .inl ⟨Sum.inr e, he, by simpa using hze⟩
    · exact .inr hr

theorem mem_freeVars_except_single {f : Expression α} {τ : α}
    {path : List (String ⊕ Expression α)} {rhs : Expression α} :
    z ∈ (Expression.except f τ [(path, rhs)]).freeVars ↔
      z ∈ f.freeVars ∨ (∃ e, Sum.inr e ∈ path ∧ z ∈ e.freeVars) ∨ z ∈ rhs.freeVars := by
  simp only [mem_freeVars_except, List.mem_singleton, exists_eq_left]

end Expression

end ComputableTLAPlus

/-!
  Lifted over `ComputableGuardedPlusCal` — flat by construction (module doc,
  `Core/GuardedPlusCal/Syntax.lean`), so every `Expr` field is a direct component, not a nested
  `Block`: no well-founded recursion is needed here, unlike `Expression.freeVars` above.
-/

/-- Every name a `Ref`'s base variable and index expressions read. The base name itself is a
use, same as any other `Expression.var` occurrence — a `Ref` is how a statement spells "read/write
this variable", not a binder. -/
def GuardedPlusCal.Ref.freeVars (r : ComputableGuardedPlusCal.Ref) : Finset String :=
  {r.name} ∪
    ((r.args.map λ seg ↦ match seg with | .inl _ => (∅ : Finset String) | .inr e => e.freeVars).foldl (· ∪ ·) ∅)

/-- The base name is one of them — the `{r.name} ∪ …` above, named, so that a freshness hypothesis
stated over a whole `Ref` yields the inequality against `r.name` that memory lemmas need. -/
theorem GuardedPlusCal.Ref.name_mem_freeVars (r : ComputableGuardedPlusCal.Ref) :
    r.name ∈ GuardedPlusCal.Ref.freeVars r :=
  Finset.mem_union_left _ (Finset.mem_singleton_self _)

/-- `set`'s recipients are read in the enclosing scope; `recipient` then binds inside `val`, same
shape as `Expression.fn`/`.map'`. -/
def GuardedPlusCal.Multicast.freeVars (m : ComputableGuardedPlusCal.Multicast) : Finset String :=
  m.set.freeVars ∪ m.val.freeVars.erase m.recipient

/-- Every name a statement reads — every `Expr`/`Ref` field's free variables, unioned. A `with`'s
own bound `name` is not included (it's introduced, not read); its domain/bound expression `e` is.
-/
def GuardedPlusCal.Statement.freeVars {b b'} (S : ComputableGuardedPlusCal.Statement b b') :
    Finset String :=
  match S with
  | .with _ _ _ e => e.freeVars
  | .await e => e.freeVars
  | .receive c r _ => c.freeVars ∪ r.freeVars
  | .skip => ∅
  | .print e => e.freeVars
  | .assert e => e.freeVars
  | .send c e => c.freeVars ∪ e.freeVars
  | .multicast _ filter => filter.freeVars
  | .assign r e => r.freeVars ∪ e.freeVars
  | .goto _ => ∅

/-- Every name any statement in `B` reads. -/
def GuardedPlusCal.Block.freeVars {g b} (B : Block (ComputableGuardedPlusCal.Statement g) b) :
    Finset String :=
  (B.begin.map GuardedPlusCal.Statement.freeVars).foldl (· ∪ ·) ∅ ∪ B.last.freeVars

/-- `x` is read nowhere in `Br` — precondition guard list (if any) and action block alike. The
`AtomicBranch`-level freshness side condition the `reorder_assign_guard` pair needs: a preceding
action's assigned name must stay fresh in every later guard for the substitution `𝒞_reord`
performs to be sound. -/
def GuardedPlusCal.AtomicBranch.FreshIn (x : String) (Br : ComputableGuardedPlusCal.AtomicBranch) :
    Prop :=
  x ∉ ((match Br.precondition with | none => ∅ | some B => B.freeVars) ∪ Br.action.freeVars)

end
