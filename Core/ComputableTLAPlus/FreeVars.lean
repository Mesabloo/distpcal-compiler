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

/-! ### De Bruijn traversals

`liftBound`/`openVar`/`close`/`subst`/`instantiate` are each `mapVars f 0` for a specific per-node
`f`. `freeVars_mapVars_subset` bounds the free names of a `mapVars` result once — every other
free-variable fact about those operations is a corollary. -/

/-- Every free name of `e.mapVars f k` is either a free name `f` keeps at some `.var _ (.free _)`
node of `e`, or a name in `S` — the extra set `f` may introduce at `.bound` nodes. -/
theorem freeVars_mapVars_subset {f : Nat → α → Origin → SourceSpan → Expression α}
    {S : Finset String}
    (hf : ∀ k τ o pos z, z ∈ (f k τ o pos).freeVars →
      z ∈ (match o with | .free n => ({n} : Finset String) | _ => ∅) ∨ z ∈ S) :
    ∀ (k : Nat) (e : Expression α) {z}, z ∈ (e.mapVars f k).freeVars → z ∈ e.freeVars ∨ z ∈ S := by
  intro k e
  fun_induction Expression.mapVars f k e with
  | case1 => next k' τ o pos =>
    intro z hz
    rcases hf k' τ o pos z hz with h | h
    · left; cases o <;> simp_all [Expression.freeVars]
    · right; exact h
  | case12 => next k' g τ upds pos ihg ihpath ihv =>
    intro z hz
    rw [Expression.mem_freeVars_except] at hz ⊢
    rcases hz with hg | ⟨u, hu, hbody⟩
    · exact (ihg hg).imp Or.inl id
    · rw [List.mem_map] at hu
      obtain ⟨⟨⟨path, v⟩, hpv⟩, -, rfl⟩ := hu
      rcases hbody with ⟨e', he', hze'⟩ | hv
      · rw [List.mem_map] at he'
        obtain ⟨⟨s, hsp⟩, -, hga⟩ := he'
        cases s with
        | inl fld => nomatch hga
        | inr e'' =>
          have hga' : Expression.mapVars f k' e'' = e' := Sum.inr.inj hga
          subst hga'
          exact (ihpath path v hpv e'' hsp hze').imp
            (fun h ↦ .inr ⟨(path, v), hpv, .inl ⟨e'', hsp, h⟩⟩) id
      · exact (ihv path v hpv hv).imp (fun h ↦ .inr ⟨(path, v), hpv, .inr h⟩) id
  | _ =>
    intro z hz
    simp only [Expression.freeVars, Finset.mem_union, mem_foldl_union, Finset.notMem_empty,
      false_or, List.mem_map, List.mem_attach, true_and, Subtype.exists, Prod.exists,
      Expression.mem_freeVars_case] at hz ⊢ <;> grind

/-- `liftBound` shifts `.bound` indices and never touches a `.free` name. -/
theorem freeVars_liftBound_subset {d : Nat} {e : Expression α} :
    (e.liftBound d).freeVars ⊆ e.freeVars := by
  intro z hz
  have := freeVars_mapVars_subset (S := (∅ : Finset String))
    (fun k τ o pos w hw ↦ by
      cases o <;> simp_all [Expression.freeVars, Expression.liftBoundLam]) 0 e hz
  simpa using this

/-- `openVar` turns the removed binder's index into the free name `x`, and moves no other name in
or out. -/
theorem freeVars_openVar_subset {x : String} {e : Expression α} :
    (e.openVar x).freeVars ⊆ insert x e.freeVars := by
  intro z hz
  have := freeVars_mapVars_subset (S := ({x} : Finset String))
    (fun k τ o pos w hw ↦ by
      cases o with
      | bound i =>
        refine .inr ?_
        simp only [Expression.openVarLam] at hw
        split_ifs at hw with h1 h2 <;> simp_all [Expression.freeVars]
      | _ => exact .inl (by simpa [Expression.freeVars, Expression.openVarLam] using hw)) 0 e hz
  rcases this with h | h
  · exact Finset.mem_insert_of_mem h
  · exact Finset.mem_singleton.mp h ▸ Finset.mem_insert_self x e.freeVars

/-- A name free in `e.openVar x`, other than `x` itself, was already free in `e`. -/
theorem freeVars_openVar_erase {x : String} {e : Expression α} :
    (e.openVar x).freeVars.erase x ⊆ e.freeVars := by
  intro z hz
  obtain ⟨hzx, hz⟩ := Finset.mem_erase.mp hz
  rcases Finset.mem_insert.mp (freeVars_openVar_subset hz) with h | h
  · exact (hzx h).elim
  · exact h

/-- A name free after instantiating the outermost binders is free in the body or in one of the
instantiated arguments. -/
theorem freeVars_instantiate {args : List (Expression α)} {body : Expression α} {z : String}
    (hz : z ∈ (body.instantiate args).freeVars) :
    z ∈ body.freeVars ∨ ∃ a ∈ args, z ∈ a.freeVars := by
  have hS : ∀ w, w ∈ ((args.map Expression.freeVars).foldl (· ∪ ·) ∅ : Finset String) ↔
      ∃ a ∈ args, w ∈ a.freeVars := fun w ↦ by
    rw [mem_foldl_union]; simp [List.mem_map]
  rcases freeVars_mapVars_subset (S := (args.map Expression.freeVars).foldl (· ∪ ·) ∅)
    (fun k τ o pos w hw ↦ by
      cases o with
      | bound i =>
        simp only [Expression.instLam] at hw
        split_ifs at hw with h1 h2
        · simp_all [Expression.freeVars]
        · rw [getElem!_pos args (i - k) h2] at hw
          exact .inr ((hS w).mpr
            ⟨args[i - k]'h2, List.getElem_mem h2, freeVars_liftBound_subset hw⟩)
        · simp_all [Expression.freeVars]
      | _ => exact .inl (by simpa [Expression.instLam, Expression.freeVars] using hw)) 0 body hz
    with h | h
  · exact .inl h
  · exact .inr ((hS z).mp h)

/-- `l.attach.map f = l` once each element maps back to itself. -/
private theorem attach_map_id_of {β : Type} {l : List β} {f : {x // x ∈ l} → β}
    (h : ∀ a : {x // x ∈ l}, f a = a.1) : l.attach.map f = l :=
  (List.map_congr_left fun a _ ↦ h a).trans (List.attach_map_subtype_val l)

set_option maxHeartbeats 1000000 in
/-- `subst` of a name not free in the target is the identity. -/
theorem subst_fresh {x : String} {e' : Expression α} :
    ∀ (t : Expression α), x ∉ t.freeVars → Expression.subst x e' t = t := by
  intro t
  rw [Expression.subst_eq_mapVars]
  fun_induction Expression.mapVars (Expression.substLam x e') 0 t with
  | case1 k' τ o pos =>
    intro h
    cases o with
    | free n =>
      rewrite [Expression.freeVars, Finset.mem_singleton] at h
      simp only [Expression.substLam]
      rw [if_neg (Ne.symm h)]
    | _ => simp only [Expression.substLam]
  | case2 k' g_ es pos ihg ihes =>
    intro h
    rw [Expression.mem_freeVars_opCall, not_or] at h
    obtain ⟨hg, hes'⟩ := h
    simp only [not_exists, not_and] at hes'
    simp only [registerSource]
    congr 1
    · exact ihg hg
    · exact attach_map_id_of fun a ↦ ihes a.1 a.2 (hes' a.1 a.2)
  | case3 k' xh ann dom body pos ihd ihb =>
    intro h
    rewrite [Expression.freeVars, Finset.notMem_union] at h
    simp only [registerSource]; rw [ihd h.1, ihb h.2]
  | case4 k' xh ann dom body pos ihd ihb =>
    intro h
    rewrite [Expression.freeVars, Finset.notMem_union] at h
    simp only [registerSource]; rw [ihd h.1, ihb h.2]
  | case5 k' xh ann dom body pos ihd ihb =>
    intro h
    rewrite [Expression.freeVars, Finset.notMem_union] at h
    simp only [registerSource]; rw [ihd h.1, ihb h.2]
  | case6 k' es τ pos ihes =>
    intro h
    rewrite [Expression.mem_freeVars_set] at h
    simp only [not_exists, not_and] at h
    simp only [registerSource]
    congr 1
    exact attach_map_id_of fun a ↦ ihes a.1 a.2 (h a.1 a.2)
  | case7 k' xh ann dom body pos ihd ihb =>
    intro h
    rewrite [Expression.freeVars, Finset.notMem_union] at h
    simp only [registerSource]; rw [ihd h.1, ihb h.2]
  | case8 k' body xh ann cod dom pos ihb ihd =>
    intro h
    rewrite [Expression.freeVars, Finset.notMem_union] at h
    simp only [registerSource]; rw [ihb h.2, ihd h.1]
  | case9 k' g_ fnTyp e'' pos ihg ihe =>
    intro h
    rewrite [Expression.freeVars, Finset.notMem_union] at h
    simp only [registerSource]; rw [ihg h.1, ihe h.2]
  | case10 k' xh ann cod dom body pos ihd ihb =>
    intro h
    rewrite [Expression.freeVars, Finset.notMem_union] at h
    simp only [registerSource]; rw [ihd h.1, ihb h.2]
  | case11 k' fs pos ihfs =>
    intro h
    rewrite [Expression.mem_freeVars_record] at h
    simp only [not_exists, not_and] at h
    simp only [registerSource]
    congr 1
    refine attach_map_id_of fun a ↦ ?_
    obtain ⟨⟨ann, nm, v⟩, hm⟩ := a
    exact congr_arg₂ Prod.mk rfl (congr_arg₂ Prod.mk rfl (ihfs ann nm v hm (h _ hm)))
  | case12 k' g_ τ upds pos ih3 ih2 ih1 =>
    intro h
    rw [Expression.mem_freeVars_except, not_or] at h
    obtain ⟨hg, hu⟩ := h
    simp only [not_exists, not_and, not_or] at hu
    simp only [registerSource]
    congr 1
    · exact ih3 hg
    · refine attach_map_id_of fun a ↦ ?_
      obtain ⟨⟨path, v⟩, hpv⟩ := a
      obtain ⟨hpath, hv⟩ := hu _ hpv
      refine congr_arg₂ Prod.mk ?_ (ih1 path v hpv hv)
      refine attach_map_id_of fun s ↦ ?_
      obtain ⟨s, hsp⟩ := s
      cases s with
      | inl fld => rfl
      | inr e'' => exact congrArg Sum.inr (ih2 path v hpv e'' hsp (hpath e'' hsp))
  | case13 k' g_ nm pos ihg =>
    intro h
    rewrite [Expression.freeVars] at h
    simp only [registerSource]; rw [ihg h]
  | case14 k' es pos ihes =>
    intro h
    rewrite [Expression.mem_freeVars_tuple] at h
    simp only [not_exists, not_and] at h
    simp only [registerSource]
    congr 1
    refine attach_map_id_of fun a ↦ ?_
    obtain ⟨⟨t, v⟩, hm⟩ := a
    exact congr_arg₂ Prod.mk rfl (ihes t v hm (h _ hm))
  | case15 k' es τ pos ihes =>
    intro h
    rewrite [Expression.mem_freeVars_seq] at h
    simp only [not_exists, not_and] at h
    simp only [registerSource]
    congr 1
    exact attach_map_id_of fun a ↦ ihes a.1 a.2 (h a.1 a.2)
  | case16 k' e₁ e₂ e₃ τ pos ih₁ ih₂ ih₃ =>
    intro h
    rewrite [Expression.freeVars, Finset.notMem_union, Finset.notMem_union] at h
    simp only [registerSource]; rw [ih₁ h.1.1, ih₂ h.1.2, ih₃ h.2]
  | case17 k' bs other τ pos ih3 ih2 ih1 =>
    intro h
    rw [Expression.mem_freeVars_case, not_or] at h
    obtain ⟨hb, ho⟩ := h
    simp only [not_exists, not_and, not_or] at hb ho
    simp only [registerSource]
    congr 1
    · refine attach_map_id_of fun a ↦ ?_
      obtain ⟨⟨p, q⟩, hpq⟩ := a
      obtain ⟨hp, hq⟩ := hb _ hpq
      exact congr_arg₂ Prod.mk (ih3 p q hpq hp) (ih2 p q hpq hq)
    · cases other with
      | none => rfl
      | some e'' => exact congrArg some (ih1 (ho e'' rfl))
  | case18 => intro _; rfl
  | case19 => intro _; rfl
  | case20 => intro _; rfl
  | case21 => intro _; rfl

/-- `subst` distributes over `instantiate` when the substituend is locally closed and the body is
closed (`Ξ.WellScoped` gives operator bodies `freeVars = ∅`). -/
theorem subst_instantiate {x : String} {e' : Expression α}
    (hlc : e'.LC) {body : Expression α} (hbody : x ∉ body.freeVars) (args : List (Expression α)) :
    Expression.subst x e' (body.instantiate args)
      = body.instantiate (args.map (Expression.subst x e')) := by
  rw [Expression.instantiate, Expression.instantiate, Expression.subst_eq_mapVars]
  refine Eq.trans (Expression.mapVars_comm (g := Expression.substLam x e')
    (gf := Expression.instLam (args.map (Expression.subst x e')))
    (f := Expression.instLam args) (fg := Expression.substLam x e')
    (fun k' τ o pos ↦ ?_) 0 body) ?_
  · cases o with
    | bound i =>
      simp only [Expression.instLam, Expression.substLam, Expression.mapVars, List.length_map]
      split_ifs with h1 h2
      · simp only [Expression.mapVars, Expression.substLam]
      · rw [hlc.mapVars_substLam_eq k' _, Expression.subst_liftBound_comm hlc,
          getElem!_pos args (i - k') h2,
          getElem!_pos (args.map (Expression.subst x e')) (i - k') (by simpa using h2),
          List.getElem_map]
      · simp only [Expression.mapVars, Expression.substLam]
    | free n =>
      simp only [Expression.instLam, Expression.substLam, Expression.mapVars]
      split_ifs with hn
      · rw [hlc.liftBound_eq k', hlc.mapVars_instLam_eq]
      · simp only [Expression.instLam, Expression.mapVars]
    | «module» m n =>
      simp only [Expression.instLam, Expression.substLam, Expression.mapVars]
    | intrinsic n =>
      simp only [Expression.instLam, Expression.substLam, Expression.mapVars]
  · rw [← Expression.subst_eq_mapVars, subst_fresh _ hbody]

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
