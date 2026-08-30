module

meta import CustomPrelude
public import Core.ComputableTLAPlus.Syntax
public import Core.ComputableTLAPlus.Subst
public import Core.GuardedPlusCal.Syntax
public import Mathlib.Data.Finset.Basic

@[expose] public section


/-!
  Metatheory for `Expression.freeVars` and `Expression.subst` (both defined in `Subst.lean`):
  membership lemmas that unfold `freeVars`'s `foldl (· ∪ ·)` list cases to plain `∃ e ∈ es, …`, the
  `freeVars_subst_subset` bound on what substitution can leave free, plus the same `freeVars`
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

/-- The trace of a free variable `z` of a substitution back to a name `y` of the source: `ρ`
renamed `y` to `z`, or `ρ` left `y` alone and `σ` either kept it (`z = y`) or replaced it by an
expression `z` is free in. -/
def SubstTrace {α} (σ : String → Option (Expression α)) (ρ : String → Option String)
    (z y : String) : Prop :=
  ρ y = some z ∨
    (ρ y = none ∧ ((σ y = none ∧ z = y) ∨ ∃ ez, σ y = some ez ∧ z ∈ ez.freeVars))

/-- `SubstTrace` is unaffected by a rename of a name it does not mention. -/
theorem SubstTrace.update_of_ne {α} {σ : String → Option (Expression α)} {ρ : String → Option String}
    {z y w : String} {v : Option String} (hw : w ≠ y) :
    SubstTrace σ (Function.update ρ w v) z y ↔ SubstTrace σ ρ z y := by
  rw [SubstTrace, SubstTrace, Function.update_of_ne (Ne.symm hw)]

/-- `SubstTrace` lifts along a list of sub-expressions: a free variable of a substituted element
traces to a source name of the same element. -/
private theorem substTrace_list_step {α} {σ : String → Option (Expression α)} {z : String}
    {es : List (Expression α)} {ρ' : String → Option String} {av : Finset String} {E : Expression α}
    (ih : ∀ e ∈ es, z ∈ (e.substAux σ ρ' av).freeVars → ∃ y ∈ e.freeVars, SubstTrace σ ρ' z y)
    (hE : E ∈ es.attach.map (λ w ↦ w.1.substAux σ ρ' av)) (hzE : z ∈ E.freeVars) :
    ∃ e ∈ es, ∃ y ∈ e.freeVars, SubstTrace σ ρ' z y := by
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hE
  obtain ⟨e', he', rfl⟩ := hE
  exact ⟨e', he', ih e' he' hzE⟩

/-- `SubstTrace` lifts across a binder: a free variable of the substituted `dom ∪ body∖ye` traces
to a source name of `dom ∪ body∖yb`, the renamed binder `ye` being erased on both sides. -/
private theorem substTrace_binder_step {α} {σ : String → Option (Expression α)} {z : String}
    {ρ : String → Option String} {avoid av' : Finset String} {yb ye : String}
    {dom body : Expression α}
    (ihdom : z ∈ (dom.substAux σ ρ avoid).freeVars → ∃ y ∈ dom.freeVars, SubstTrace σ ρ z y)
    (ihbody : z ∈ (body.substAux σ (Function.update ρ yb (some ye)) av').freeVars →
      ∃ y ∈ body.freeVars, SubstTrace σ (Function.update ρ yb (some ye)) z y)
    (hmem : z ∈ (dom.substAux σ ρ avoid).freeVars ∪
      (body.substAux σ (Function.update ρ yb (some ye)) av').freeVars.erase ye) :
    ∃ y ∈ dom.freeVars ∪ body.freeVars.erase yb, SubstTrace σ ρ z y := by
  rw [Finset.mem_union] at hmem
  rcases hmem with hd | hb
  · obtain ⟨y, hy, htr⟩ := ihdom hd
    exact ⟨y, Finset.mem_union_left _ hy, htr⟩
  · rw [Finset.mem_erase] at hb
    obtain ⟨hzye, hb⟩ := hb
    obtain ⟨y, hy, htr⟩ := ihbody hb
    have hyyb : y ≠ yb := by
      rintro rfl
      rw [SubstTrace, Function.update_self] at htr
      rcases htr with h | ⟨h, -⟩
      · exact hzye (Option.some.inj h).symm
      · simp at h
    refine ⟨y, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hyyb, hy⟩), ?_⟩
    rwa [SubstTrace.update_of_ne hyyb.symm] at htr

private theorem origin_eq_binder {o : TypedTLAPlus.Origin}
    (h : (o == TypedTLAPlus.Origin.binder) = Bool.true) : o = .binder := by
  cases o with | binder => rfl | intrinsic => nomatch h | «module» => nomatch h

private theorem origin_ne_binder {o : TypedTLAPlus.Origin}
    (h : ¬(o == TypedTLAPlus.Origin.binder) = Bool.true) : o ≠ .binder := by
  intro heq; subst heq; exact h (by decide)

/-- Where a free variable of a capture-avoiding substitution's result comes from. -/
theorem freeVars_substAux_subset {α} {z : String}
    (σ : String → Option (Expression α)) (ρ : String → Option String) (avoid : Finset String)
    (t : Expression α) (hz : z ∈ (t.substAux σ ρ avoid).freeVars) :
    ∃ y ∈ t.freeVars, SubstTrace σ ρ z y := by
  fun_induction Expression.substAux σ ρ avoid t with
  | case1 ρ avoid y τ o h y' hρy pos =>
      obtain rfl := origin_eq_binder h
      simp only [registerSource, Expression.freeVars, Finset.mem_singleton] at hz
      exact ⟨y, by simp [Expression.freeVars], .inl (hz.symm ▸ hρy)⟩
  | case2 ρ avoid y τ o h hρy pos =>
      obtain rfl := origin_eq_binder h
      rcases hσy : σ y with _ | ey
      · simp only [hσy, Option.getD_none, registerSource, Expression.freeVars,
          Finset.mem_singleton] at hz
        exact ⟨y, by simp [Expression.freeVars], .inr ⟨hρy, .inl ⟨hσy, hz⟩⟩⟩
      · simp only [hσy, Option.getD_some] at hz
        exact ⟨y, by simp [Expression.freeVars], .inr ⟨hρy, .inr ⟨ey, hσy, hz⟩⟩⟩
  | case3 ρ avoid y τ o h pos =>
      have ho := origin_ne_binder h
      rw [registerSource] at hz
      cases o with
      | binder => exact (ho rfl).elim
      | intrinsic => simp [Expression.freeVars] at hz
      | «module» => simp [Expression.freeVars] at hz
  | case4 ρ avoid f es pos ihf ihes =>
      rw [registerSource, mem_freeVars_opCall] at hz
      rcases hz with hf | ⟨E, hE, hzE⟩
      · obtain ⟨y, hy, htr⟩ := ihf hf
        exact ⟨y, mem_freeVars_opCall.mpr (.inl hy), htr⟩
      · obtain ⟨e', he', y, hy, htr⟩ := substTrace_list_step ihes hE hzE
        exact ⟨y, mem_freeVars_opCall.mpr (.inr ⟨e', he', hy⟩), htr⟩
  | case5 ρ avoid y ann dom body dom' h y' pos ihd ihb
  | case7 ρ avoid y ann dom body dom' h y' pos ihd ihb
  | case9 ρ avoid y ann dom body dom' h y' pos ihd ihb
  | case11 ρ avoid y ann dom body dom' h y' pos ihd ihb
  | case6 ρ avoid y ann dom body dom' h pos ihd ihb
  | case8 ρ avoid y ann dom body dom' h pos ihd ihb
  | case10 ρ avoid y ann dom body dom' h pos ihd ihb
  | case12 ρ avoid y ann dom body dom' h pos ihd ihb
  | case13 ρ avoid body y ann cod dom dom' h y' pos ihd ihb
  | case14 ρ avoid body y ann cod dom dom' h pos ihd ihb
  | case15 ρ avoid y ann cod dom body dom' h y' pos ihd ihb
  | case16 ρ avoid y ann cod dom body dom' h pos ihd ihb =>
      rw [registerSource, Expression.freeVars] at hz
      rw [Expression.freeVars]
      exact substTrace_binder_step ihd ihb hz
  | case17 ρ avoid es τ pos ihes =>
      rw [registerSource, mem_freeVars_set] at hz
      obtain ⟨E, hE, hzE⟩ := hz
      obtain ⟨e', he', y, hy, htr⟩ := substTrace_list_step ihes hE hzE
      exact ⟨y, mem_freeVars_set.mpr ⟨e', he', hy⟩, htr⟩
  | case18 ρ avoid f fnTyp e' pos ihf ihe =>
      rw [registerSource, Expression.freeVars, Finset.mem_union] at hz
      rw [Expression.freeVars]
      rcases hz with hf | he
      · obtain ⟨y, hy, htr⟩ := ihf hf
        exact ⟨y, Finset.mem_union_left _ hy, htr⟩
      · obtain ⟨y, hy, htr⟩ := ihe he
        exact ⟨y, Finset.mem_union_right _ hy, htr⟩
  | case19 ρ avoid fs pos ihfs =>
      rw [registerSource, mem_freeVars_record] at hz
      obtain ⟨E, hE, hzE⟩ := hz
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, Prod.exists] at hE
      obtain ⟨ann, name, v, hv, rfl⟩ := hE
      obtain ⟨y, hy, htr⟩ := ihfs ann name v hv hzE
      exact ⟨y, mem_freeVars_record.mpr ⟨(ann, name, v), hv, hy⟩, htr⟩
  | case20 ρ avoid f τ upds pos ihf ihpath ihv =>
      rw [registerSource, mem_freeVars_except] at hz
      rcases hz with hf | ⟨U, hU, hbody⟩
      · obtain ⟨y, hy, htr⟩ := ihf hf
        exact ⟨y, mem_freeVars_except.mpr (.inl hy), htr⟩
      · simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, Prod.exists] at hU
        obtain ⟨path, v, hpv, rfl⟩ := hU
        rcases hbody with ⟨s, hs, hzs⟩ | hv2
        · simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hs
          obtain ⟨seg, hseg, hseq⟩ := hs
          cases seg with
          | inl field => simp at hseq
          | inr e0 =>
              simp only [Sum.inr.injEq] at hseq; subst hseq
              obtain ⟨y, hy, htr⟩ := ihpath path v hpv e0 hseg hzs
              exact ⟨y, mem_freeVars_except.mpr (.inr ⟨(path, v), hpv, .inl ⟨e0, hseg, hy⟩⟩), htr⟩
        · obtain ⟨y, hy, htr⟩ := ihv path v hpv hv2
          exact ⟨y, mem_freeVars_except.mpr (.inr ⟨(path, v), hpv, .inr hy⟩), htr⟩
  | case21 ρ avoid f name pos ihf =>
      rw [registerSource, Expression.freeVars] at hz
      rw [Expression.freeVars]
      exact ihf hz
  | case22 ρ avoid es pos ihes =>
      rw [registerSource, mem_freeVars_tuple] at hz
      obtain ⟨E, hE, hzE⟩ := hz
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, Prod.exists] at hE
      obtain ⟨τ0, v, hv, rfl⟩ := hE
      obtain ⟨y, hy, htr⟩ := ihes τ0 v hv hzE
      exact ⟨y, mem_freeVars_tuple.mpr ⟨(τ0, v), hv, hy⟩, htr⟩
  | case23 ρ avoid es τ pos ihes =>
      rw [registerSource, mem_freeVars_seq] at hz
      obtain ⟨E, hE, hzE⟩ := hz
      obtain ⟨e', he', y, hy, htr⟩ := substTrace_list_step ihes hE hzE
      exact ⟨y, mem_freeVars_seq.mpr ⟨e', he', hy⟩, htr⟩
  | case24 ρ avoid e₁ e₂ e₃ τ pos ih1 ih2 ih3 =>
      rw [registerSource, Expression.freeVars, Finset.mem_union, Finset.mem_union] at hz
      rw [Expression.freeVars]
      rcases hz with (h | h) | h
      · obtain ⟨y, hy, htr⟩ := ih1 h
        exact ⟨y, Finset.mem_union_left _ (Finset.mem_union_left _ hy), htr⟩
      · obtain ⟨y, hy, htr⟩ := ih2 h
        exact ⟨y, Finset.mem_union_left _ (Finset.mem_union_right _ hy), htr⟩
      · obtain ⟨y, hy, htr⟩ := ih3 h
        exact ⟨y, Finset.mem_union_right _ hy, htr⟩
  | case25 ρ avoid bs other τ pos ihp ihq ihother =>
      rw [registerSource, mem_freeVars_case] at hz
      rcases hz with ⟨B, hB, hzB⟩ | ⟨e0, hoe, hze⟩
      · simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, Prod.exists] at hB
        obtain ⟨p, q, hpq, rfl⟩ := hB
        rcases hzB with hp | hq
        · obtain ⟨y, hy, htr⟩ := ihp p q hpq hp
          exact ⟨y, mem_freeVars_case.mpr (.inl ⟨(p, q), hpq, .inl hy⟩), htr⟩
        · obtain ⟨y, hy, htr⟩ := ihq p q hpq hq
          exact ⟨y, mem_freeVars_case.mpr (.inl ⟨(p, q), hpq, .inr hy⟩), htr⟩
      · cases other with
        | none => simp at hoe
        | some e1 =>
            simp only [Option.some.injEq] at hoe; subst hoe
            obtain ⟨y, hy, htr⟩ := ihother hze
            exact ⟨y, mem_freeVars_case.mpr (.inr ⟨e1, rfl, hy⟩), htr⟩
  | case26 | case27 | case28 | case29 => simp [registerSource, Expression.freeVars] at hz

/-- Substituting `e'` for `x` in `t` can only leave free what was free in `t` before (other than
`x` itself) or what is free in `e'`. Bounds `substParams`, and hence the free variables of the body
a `var_op0`/`opCall_op` step evaluates. -/
theorem freeVars_subst_subset (x : String) (e' t : Expression α) :
    z ∈ (Expression.subst x e' t).freeVars → z ∈ t.freeVars.erase x ∨ z ∈ e'.freeVars := by
  intro hz
  obtain ⟨y, hy, hcase⟩ := freeVars_substAux_subset _ _ _ t hz
  rw [SubstTrace] at hcase
  by_cases hyx : y = x
  · subst hyx
    rcases hcase with h | ⟨-, ⟨h, -⟩ | ⟨ez, hez, hzez⟩⟩
    · nomatch h
    · simp at h
    · simp only [beq_self_eq_true, if_true, Option.some.injEq] at hez
      exact .inr (hez ▸ hzez)
  · rcases hcase with h | ⟨-, ⟨-, rfl⟩ | ⟨ez, hez, -⟩⟩
    · nomatch h
    · exact .inl (Finset.mem_erase.mpr ⟨hyx, hy⟩)
    · simp [hyx] at hez

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
