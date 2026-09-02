module

meta import CustomPrelude
public import Core.ComputableTLAPlus.Syntax
public import Core.TypedPlusCal.Syntax
public import Mathlib.Data.Finset.Basic

@[expose] public section


/-!
  Free variables of, and de Bruijn index manipulation for, a `ComputableTLAPlus.Expression` under
  locally-nameless binding.

  `Expression.freeVars` collects every `.var _ (.free name)` node: a `Memory`-keyed name (PlusCal
  `variable`/`channel`/`fifo`, `self`, a statement `with`). `.bound` occurrences resolve to an
  enclosing expression binder and `.module`/`.intrinsic` occurrences resolve through `Ξ`/`Ω` — none
  of them read memory, so none contribute.

  `Origin.bound` uses standard de Bruijn indices: `.bound 0` is the nearest enclosing
  expression-level binder. `liftBound`/`openVar`/`close`/`subst`/`instantiate` are all one
  depth-tracking traversal, `mapVars`. `.bound` and `.free` are disjoint namespaces, so `subst` of
  a free name captures nothing and needs no freshness side condition.
-/

namespace ComputableTLAPlus

/-- Every name a `target` reads from memory: every `.var _ (.free name)` node. `.bound` and
`.module`/`.intrinsic` occurrences resolve elsewhere and contribute nothing. -/
def Expression.freeVars {α} (target : Expression α) : Finset String := match target with
  | .var _ (.free n) => {n}
  | .var _ _ => ∅
  | .opCall f es => f.freeVars ∪ (es.attach.map λ ⟨e', _hes⟩ ↦ e'.freeVars).foldl (· ∪ ·) ∅
  | .forall _ _ dom body => dom.freeVars ∪ body.freeVars
  | .exists _ _ dom body => dom.freeVars ∪ body.freeVars
  | .choose _ _ dom body => dom.freeVars ∪ body.freeVars
  | .set es _ => (es.attach.map λ ⟨e', _hes⟩ ↦ e'.freeVars).foldl (· ∪ ·) ∅
  | .collect _ _ dom pred => dom.freeVars ∪ pred.freeVars
  | .map' body _ _ _ dom => dom.freeVars ∪ body.freeVars
  | .fnCall f _ e' => f.freeVars ∪ e'.freeVars
  | .fn _ _ _ dom body => dom.freeVars ∪ body.freeVars
  | .record fs => (fs.attach.map λ ⟨(_, _, v), _hfs⟩ ↦ v.freeVars).foldl (· ∪ ·) ∅
  | .except f _ upds =>
    f.freeVars ∪
      (upds.attach.map λ ⟨(path, v), _hupds⟩ ↦
        (path.attach.map λ ⟨s, _hpath⟩ ↦ match s with | .inl _ => ∅ | .inr e' => e'.freeVars).foldl (· ∪ ·) ∅
          ∪ v.freeVars).foldl (· ∪ ·) ∅
  | .recordAccess f _ => f.freeVars
  | .tuple es => (es.attach.map λ ⟨(_, e'), _hes⟩ ↦ e'.freeVars).foldl (· ∪ ·) ∅
  | .seq es _ => (es.attach.map λ ⟨e', _hes⟩ ↦ e'.freeVars).foldl (· ∪ ·) ∅
  | .if e₁ e₂ e₃ _ => e₁.freeVars ∪ e₂.freeVars ∪ e₃.freeVars
  | .case bs other _ =>
    (bs.attach.map λ ⟨(p, q), _hbs⟩ ↦ p.freeVars ∪ q.freeVars).foldl (· ∪ ·) ∅
      ∪ (match other with | none => ∅ | some e' => e'.freeVars)
  | .nat _ => ∅
  | .str _ => ∅
  | .true => ∅
  | .false => ∅
termination_by sizeOf target
decreasing_by
  all: simp_wf
  all: first
    | omega
    | (have h := List.sizeOf_lt_of_mem _hes
       try simp only [Prod.mk.sizeOf_spec] at h
       omega)
    | (have h := List.sizeOf_lt_of_mem _hfs
       simp only [Prod.mk.sizeOf_spec] at h
       omega)
    | (have h := List.sizeOf_lt_of_mem _hbs
       simp only [Prod.mk.sizeOf_spec] at h
       omega)
    | (have h := List.sizeOf_lt_of_mem _hupds
       simp only [Prod.mk.sizeOf_spec] at h
       omega)
    | (have h1 := List.sizeOf_lt_of_mem _hupds
       have h2 := List.sizeOf_lt_of_mem _hpath
       simp only [Prod.mk.sizeOf_spec, Sum.inr.sizeOf_spec] at h1 h2
       omega)

/-- Rebuild every `.var` node knowing the number of expression-level binders enclosing it: `f k τ o
pos` is the replacement for a `.var τ o` at binder depth `k`. Each binder arm recurses into its
scoped body at `k + 1`; domain and annotation positions stay at `k`. -/
def Expression.mapVars {α} (f : Nat → α → Origin → SourceSpan → Expression α) (k : Nat)
    (target : Expression α) : Expression α := match_source target with
  | .var τ o, pos => f k τ o pos
  | .opCall g es, pos =>
    .opCall (mapVars f k g) (es.attach.map λ ⟨e', _hes⟩ ↦ mapVars f k e') @@ pos
  | .forall x ann dom body, pos =>
    .forall x ann (mapVars f k dom) (mapVars f (k + 1) body) @@ pos
  | .exists x ann dom body, pos =>
    .exists x ann (mapVars f k dom) (mapVars f (k + 1) body) @@ pos
  | .choose x ann dom body, pos =>
    .choose x ann (mapVars f k dom) (mapVars f (k + 1) body) @@ pos
  | .set es τ, pos => .set (es.attach.map λ ⟨e', _hes⟩ ↦ mapVars f k e') τ @@ pos
  | .collect x ann dom pred, pos =>
    .collect x ann (mapVars f k dom) (mapVars f (k + 1) pred) @@ pos
  | .map' body x ann cod dom, pos =>
    .map' (mapVars f (k + 1) body) x ann cod (mapVars f k dom) @@ pos
  | .fnCall g fnTyp e', pos => .fnCall (mapVars f k g) fnTyp (mapVars f k e') @@ pos
  | .fn x ann cod dom body, pos =>
    .fn x ann cod (mapVars f k dom) (mapVars f (k + 1) body) @@ pos
  | .record fs, pos =>
    .record (fs.attach.map λ ⟨(ann, nm, v), _hfs⟩ ↦ (ann, nm, mapVars f k v)) @@ pos
  | .except g τ upds, pos =>
    .except (mapVars f k g) τ
      (upds.attach.map λ ⟨(path, v), _hupds⟩ ↦
        (path.attach.map λ ⟨s, _hpath⟩ ↦
            match s with | .inl fld => .inl fld | .inr e' => .inr (mapVars f k e'),
         mapVars f k v)) @@ pos
  | .recordAccess g nm, pos => .recordAccess (mapVars f k g) nm @@ pos
  | .tuple es, pos => .tuple (es.attach.map λ ⟨(τ, e'), _hes⟩ ↦ (τ, mapVars f k e')) @@ pos
  | .seq es τ, pos => .seq (es.attach.map λ ⟨e', _hes⟩ ↦ mapVars f k e') τ @@ pos
  | .if e₁ e₂ e₃ τ, pos =>
    .if (mapVars f k e₁) (mapVars f k e₂) (mapVars f k e₃) τ @@ pos
  | .case bs other τ, pos =>
    .case (bs.attach.map λ ⟨(p, q), _hbs⟩ ↦ (mapVars f k p, mapVars f k q))
      (match other with | none => none | some e' => some (mapVars f k e')) τ @@ pos
  | .nat n, pos => .nat n @@ pos
  | .str s, pos => .str s @@ pos
  | .true, pos => .true @@ pos
  | .false, pos => .false @@ pos
termination_by sizeOf target
decreasing_by
  all: simp_wf
  all: first
    | omega
    | (have h := List.sizeOf_lt_of_mem _hes
       try simp only [Prod.mk.sizeOf_spec] at h
       omega)
    | (have h := List.sizeOf_lt_of_mem _hfs
       simp only [Prod.mk.sizeOf_spec] at h
       omega)
    | (have h := List.sizeOf_lt_of_mem _hbs
       simp only [Prod.mk.sizeOf_spec] at h
       omega)
    | (have h := List.sizeOf_lt_of_mem _hupds
       simp only [Prod.mk.sizeOf_spec] at h
       omega)
    | (have h1 := List.sizeOf_lt_of_mem _hupds
       have h2 := List.sizeOf_lt_of_mem _hpath
       simp only [Prod.mk.sizeOf_spec, Sum.inr.sizeOf_spec] at h1 h2
       omega)

/-- The `mapVars` action `liftBound d` runs at every `.var` node: add `d` to a `.bound` index that
sits at or past the current binder depth, leave everything else. Named so lemmas can talk about the
traversal without re-inlining it. -/
def Expression.liftBoundLam {α} (d : Nat) : Nat → α → Origin → SourceSpan → Expression α :=
  λ k τ o pos ↦ match o with
    | .bound i => .var τ (.bound (if k ≤ i then i + d else i)) @@ pos
    | _ => .var τ o @@ pos

/-- Add `d` to every `.bound` index that refers past `e`'s own binders. -/
def Expression.liftBound {α} (d : Nat) (e : Expression α) : Expression α :=
  e.mapVars (Expression.liftBoundLam d) 0

/-- The `mapVars` action `openVar name` runs at every `.var` node: the `.bound` index equal to the
current depth becomes `.free name`, deeper indices shift down by one, shallower ones stay. Named so
lemmas can talk about the traversal without re-inlining it. -/
def Expression.openVarLam {α} (name : String) : Nat → α → Origin → SourceSpan → Expression α :=
  λ k τ o pos ↦ match o with
    | .bound i =>
      if i = k then .var τ (.free name) @@ pos
      else if k < i then .var τ (.bound (i - 1)) @@ pos
      else .var τ (.bound i) @@ pos
    | _ => .var τ o @@ pos

/-- In a binder's body — already stripped of that binder — turn the reference to the removed binder
into the free name `name`, and shift every deeper free index down by one. -/
def Expression.openVar {α} (name : String) (e : Expression α) : Expression α :=
  e.mapVars (Expression.openVarLam name) 0

/-- Bind every free occurrence of `name` as a new outermost `.bound`, shifting every deeper free
index up by one. Inverse of `openVar`. -/
def Expression.close {α} (name : String) (e : Expression α) : Expression α :=
  e.mapVars (λ k τ o pos ↦ match o with
    | .free n => if n = name then .var τ (.bound k) @@ pos else .var τ o @@ pos
    | .bound i => .var τ (.bound (if k ≤ i then i + 1 else i)) @@ pos
    | _ => .var τ o @@ pos) 0

/-- `(l.attach.map f).attach.map g = l` when `g` reads a `l.attach.map f` element back to the
`l`-element `f` was applied to. The shape `mapVars`' `except` and `case` arms produce when composed
with themselves. -/
private theorem doubleAttach_collapse {β : Type} {l : List β} (f : {x // x ∈ l} → β)
    {g : {y // y ∈ l.attach.map f} → β}
    (hgf : ∀ (a : {x // x ∈ l}) (hm : f a ∈ l.attach.map f), g ⟨f a, hm⟩ = a.1) :
    (l.attach.map f).attach.map g = l := by
  simp only [List.map_attach_eq_pmap, List.pmap_pmap]
  rw [List.pmap_congr_left (q := λ _ ↦ True) (H₂ := λ _ _ ↦ trivial)
        (g := λ a _ ↦ (a.1 : β)) l.attach (λ a _ _ _ ↦ hgf a _)]
  simp [List.pmap_eq_map]

/-- Congruence for the doubly-attached maps that `mapVars`' list arms produce when composed with
themselves: if the inner element functions `f`/`f'` land in step and the outer readers `g`/`g'`
agree on every element, the two `(l.attach.map _).attach.map _` towers are equal. Companion to
`doubleAttach_collapse`, for the `_ = _` (rather than `_ = l`) shape. -/
private theorem doubleAttach_map_congr {β : Type} {l : List β} {f f' : {x // x ∈ l} → β}
    {g : {y // y ∈ l.attach.map f} → β} {g' : {y // y ∈ l.attach.map f'} → β}
    (h : ∀ (a : {x // x ∈ l}) (hm : f a ∈ l.attach.map f) (hm' : f' a ∈ l.attach.map f'),
      g ⟨f a, hm⟩ = g' ⟨f' a, hm'⟩) :
    (l.attach.map f).attach.map g = (l.attach.map f').attach.map g' := by
  simp only [List.map_attach_eq_pmap, List.pmap_pmap]
  refine List.pmap_congr_left _ (λ a _ _ _ ↦ ?_)
  exact h ⟨a, ‹_›⟩ _ _

/-- Collapse the outer `attach ∘ map` a second `mapVars` (or `applyComputable`) traversal wraps
around a list arm: `(l.attach.map f).attach.map g` matches the single-layer `l.attach.map h` when
`g` on each element `f a` agrees with `h a`. The `applyComputable` list arms
(`tuple`/`record`) need this — the source term carries one `attach.map`, the traversed term two. -/
theorem Expression.doubleAttach_map_eq {β γ : Type} {l : List β} {f : {x // x ∈ l} → γ}
    {g : {y // y ∈ l.attach.map f} → γ} {h : {x // x ∈ l} → γ}
    (H : ∀ (a : {x // x ∈ l}) (hm : f a ∈ l.attach.map f), g ⟨f a, hm⟩ = h a) :
    (l.attach.map f).attach.map g = l.attach.map h := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_attach]
    rw [H]

/-- Two `mapVars` traversals at the same depth that undo one another at every `.var` node cancel
over the whole term. Used to state `.liftBound`/`.openVar` cancellations. -/
theorem Expression.mapVars_mapVars_id {α} {g h : Nat → α → Origin → SourceSpan → Expression α}
    (H : ∀ k τ o pos, Expression.mapVars h k (g k τ o pos) = Expression.var τ o @@ pos) :
    ∀ (k : Nat) (e : Expression α), Expression.mapVars h k (Expression.mapVars g k e) = e := by
  intro k e
  fun_induction Expression.mapVars g k e with
  | case1 k' τ o pos => exact H k' τ o pos
  | case11 k' fs pos ih1 =>
    simp only [Expression.mapVars, registerSource, List.map_attach_eq_pmap, List.pmap_eq_map,
      List.map_map, Function.comp_def]
    congr 1
    refine (List.map_congr_left (g := id) λ a ha ↦ ?_).trans (List.map_id _)
    obtain ⟨ann, nm, v⟩ := a
    simp only [id_eq, Prod.mk.injEq, true_and]
    exact ih1 ann nm v ha
  | case14 k' es pos ih1 =>
    simp only [Expression.mapVars, registerSource, List.map_attach_eq_pmap, List.pmap_eq_map,
      List.map_map, Function.comp_def]
    congr 1
    refine (List.map_congr_left (g := id) λ a ha ↦ ?_).trans (List.map_id _)
    obtain ⟨t, v⟩ := a
    simp only [id_eq, Prod.mk.injEq, true_and]
    exact ih1 t v ha
  | case12 k' g_ τ upds pos ih3 ih2 ih1 =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    all_goals first
    | exact ih3
    | · refine doubleAttach_collapse _ ?_
        rintro ⟨⟨path, v⟩, hpv⟩ hm
        refine Prod.ext ?_ (ih1 path v hpv)
        refine doubleAttach_collapse _ ?_
        rintro ⟨s, hs⟩ hm2
        cases s with
        | inl fld => rfl
        | inr e'' => exact congrArg Sum.inr (ih2 path v hpv e'' hs)
  | case17 k' bs other τ pos ih3 ih2 ih1 =>
    cases other with
    | none =>
      simp only [Expression.mapVars, registerSource, List.map_attach_eq_pmap, List.pmap_eq_map,
        List.map_map, Function.comp_def]
      congr 1
      refine (List.map_congr_left (g := id) λ a ha ↦ ?_).trans (List.map_id _)
      obtain ⟨p, q⟩ := a
      exact Prod.ext (ih3 p q ha) (ih2 p q ha)
    | some e' =>
      simp only [Expression.mapVars, registerSource, List.map_attach_eq_pmap, List.pmap_eq_map,
        List.map_map, Function.comp_def]
      congr 1
      · refine (List.map_congr_left (g := id) λ a ha ↦ ?_).trans (List.map_id _)
        obtain ⟨p, q⟩ := a
        exact Prod.ext (ih3 p q ha) (ih2 p q ha)
      · exact congrArg some (by simpa using ih1)
  | _ =>
    simp only [Expression.mapVars, registerSource, List.map_attach_eq_pmap, List.pmap_eq_map,
      List.map_map, Function.comp_def]
    all_goals
      ((try congr 1) <;>
        first
          | rfl
          | assumption
          | (refine (List.map_congr_left (g := id) λ a ha ↦ ?_).trans (List.map_id _)
             exact by simp_all))

set_option maxHeartbeats 1000000 in
/-- Two `mapVars` traversals commute when the left one runs `n + 1` binder levels deeper than the
right: applying `f` at depth `j` then `g` at `n + 1 + j` equals applying `fg` at `n + j` then `gf`
at `j`, provided the four `.var`-node actions satisfy that identity pointwise. The `n` offset is
what a splice under `n + 1` binders (an operator/function body) needs — e.g. `openVar` at depth
`n + 1` past a `liftBound 1` at depth `0` matches `liftBound 1` past `openVar` at depth `n`
(`openVar_liftBound_one_comm`). `applyComputable` never builds `except`/`case`, but those arms are
discharged too so the lemma holds for every term. -/
theorem Expression.mapVars_shift_comm {α}
    {g gf f fg : Nat → α → Origin → SourceSpan → Expression α} (n : Nat)
    (H : ∀ j τ o pos, Expression.mapVars g (n + 1 + j) (f j τ o pos)
            = Expression.mapVars gf j (fg (n + j) τ o pos)) :
    ∀ (j : Nat) (e : Expression α),
      Expression.mapVars g (n + 1 + j) (Expression.mapVars f j e)
        = Expression.mapVars gf j (Expression.mapVars fg (n + j) e) := by
  intro j e
  fun_induction Expression.mapVars f j e with
  | case1 k' τ o pos => simp only [Expression.mapVars]; exact H k' τ o pos
  | case2 k' g_ es pos ihg ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    exact doubleAttach_map_congr λ a _ _ ↦ ihes _ a.2
  | case6 k' es τ pos ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    exact doubleAttach_map_congr λ a _ _ ↦ ihes _ a.2
  | case15 k' es τ pos ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    exact doubleAttach_map_congr λ a _ _ ↦ ihes _ a.2
  | case11 k' fs pos ihfs =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    refine doubleAttach_map_congr λ a _ _ ↦ ?_
    obtain ⟨⟨ann, nm, v⟩, hm⟩ := a
    exact Prod.ext rfl (Prod.ext rfl (ihfs ann nm v hm))
  | case14 k' es pos ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    refine doubleAttach_map_congr λ a _ _ ↦ ?_
    obtain ⟨⟨t, v⟩, hm⟩ := a
    exact Prod.ext rfl (ihes t v hm)
  | case12 k' g_ τ upds pos ih3 ih2 ih1 =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    refine doubleAttach_map_congr λ a _ _ ↦ ?_
    obtain ⟨⟨path, v⟩, hpv⟩ := a
    refine Prod.ext ?_ (ih1 path v hpv)
    refine doubleAttach_map_congr λ s _ _ ↦ ?_
    obtain ⟨s, hsp⟩ := s
    cases s with
    | inl fld => rfl
    | inr e'' => exact congrArg Sum.inr (ih2 path v hpv e'' hsp)
  | case17 k' bs other τ pos ih3 ih2 ih1 =>
    cases other with
    | none =>
      simp only [Expression.mapVars, registerSource]
      congr 1
      refine doubleAttach_map_congr λ a _ _ ↦ ?_
      obtain ⟨⟨p, q⟩, hpq⟩ := a
      exact Prod.ext (ih3 p q hpq) (ih2 p q hpq)
    | some e' =>
      simp only [Expression.mapVars, registerSource]
      congr 1
      · refine doubleAttach_map_congr λ a _ _ ↦ ?_
        obtain ⟨⟨p, q⟩, hpq⟩ := a
        exact Prod.ext (ih3 p q hpq) (ih2 p q hpq)
      · exact congrArg some ih1
  | _ =>
    simp only [Expression.mapVars, registerSource]
    all: congr 1

set_option maxHeartbeats 1000000 in
/-- Two `mapVars` traversals at the *same* depth commute when the four `.var`-node actions commute
pointwise. The zero-offset companion of `mapVars_shift_comm` — needed where a splice happens
directly under the binder being opened, not one level deeper (`subst_openVar_comm`). -/
theorem Expression.mapVars_comm {α}
    {g gf f fg : Nat → α → Origin → SourceSpan → Expression α}
    (H : ∀ k τ o pos, Expression.mapVars g k (f k τ o pos)
            = Expression.mapVars gf k (fg k τ o pos)) :
    ∀ (k : Nat) (e : Expression α),
      Expression.mapVars g k (Expression.mapVars f k e)
        = Expression.mapVars gf k (Expression.mapVars fg k e) := by
  intro k e
  fun_induction Expression.mapVars f k e with
  | case1 k' τ o pos => simp only [Expression.mapVars]; exact H k' τ o pos
  | case2 k' g_ es pos ihg ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    exact doubleAttach_map_congr λ a _ _ ↦ ihes _ a.2
  | case6 k' es τ pos ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    exact doubleAttach_map_congr λ a _ _ ↦ ihes _ a.2
  | case15 k' es τ pos ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    exact doubleAttach_map_congr λ a _ _ ↦ ihes _ a.2
  | case11 k' fs pos ihfs =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    refine doubleAttach_map_congr λ a _ _ ↦ ?_
    obtain ⟨⟨ann, nm, v⟩, hm⟩ := a
    exact Prod.ext rfl (Prod.ext rfl (ihfs ann nm v hm))
  | case14 k' es pos ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    refine doubleAttach_map_congr λ a _ _ ↦ ?_
    obtain ⟨⟨t, v⟩, hm⟩ := a
    exact Prod.ext rfl (ihes t v hm)
  | case12 k' g_ τ upds pos ih3 ih2 ih1 =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    refine doubleAttach_map_congr λ a _ _ ↦ ?_
    obtain ⟨⟨path, v⟩, hpv⟩ := a
    refine Prod.ext ?_ (ih1 path v hpv)
    refine doubleAttach_map_congr λ s _ _ ↦ ?_
    obtain ⟨s, hsp⟩ := s
    cases s with
    | inl fld => rfl
    | inr e'' => exact congrArg Sum.inr (ih2 path v hpv e'' hsp)
  | case17 k' bs other τ pos ih3 ih2 ih1 =>
    cases other with
    | none =>
      simp only [Expression.mapVars, registerSource]
      congr 1
      refine doubleAttach_map_congr λ a _ _ ↦ ?_
      obtain ⟨⟨p, q⟩, hpq⟩ := a
      exact Prod.ext (ih3 p q hpq) (ih2 p q hpq)
    | some e' =>
      simp only [Expression.mapVars, registerSource]
      congr 1
      · refine doubleAttach_map_congr λ a _ _ ↦ ?_
        obtain ⟨⟨p, q⟩, hpq⟩ := a
        exact Prod.ext (ih3 p q hpq) (ih2 p q hpq)
      · exact congrArg some ih1
  | _ =>
    simp only [Expression.mapVars, registerSource]
    all: congr 1

/-- Opening the binder `n + 1` levels out (`openVar name` at depth `n + 1`) commutes with the
`liftBound 1` a splice under that binder carries: doing the lift first and opening at `n + 1`
matches opening at `n` first and lifting. The instance of `mapVars_shift_comm` that
`openVar_applyComputable` needs for every arm of `applyComputable` that puts `e` under a binder. -/
theorem Expression.openVar_liftBound_one_comm {α} (name : String) (n : Nat) (e : Expression α) :
    Expression.mapVars (Expression.openVarLam name) (n + 1) (Expression.liftBound 1 e)
      = Expression.liftBound 1 (Expression.mapVars (Expression.openVarLam name) n e) := by
  simpa only [Expression.liftBound, Nat.add_zero] using
    Expression.mapVars_shift_comm (g := Expression.openVarLam name)
      (gf := Expression.liftBoundLam 1) (f := Expression.liftBoundLam 1)
      (fg := Expression.openVarLam name) n
      (λ j τ o pos ↦ by
        cases o with
        | bound i =>
          simp only [Expression.liftBoundLam, Expression.openVarLam]
          split_ifs <;> simp only [Expression.mapVars, Expression.openVarLam,
            Expression.liftBoundLam] <;> (try split_ifs) <;>
            first
              | rfl
              | (exfalso; omega)
              | (simp only [registerSource, Expression.var.injEq,
                  TypedTLAPlus.Origin.bound.injEq, true_and]; omega)
        | _ => simp only [Expression.liftBoundLam, Expression.openVarLam, Expression.mapVars]) 0 e

/-- Lifting every de Bruijn index up by one and then opening the (now vacant) innermost binder
with `name` is the identity: the lift moves every index past the cutoff, so `openVar` finds
nothing bound at depth 0 to rename and shifts everything back down. No freshness needed. -/
theorem Expression.openVar_liftBound_one {α} (name : String) (e : Expression α) :
    (e.liftBound 1).openVar name = e := by
  refine Expression.mapVars_mapVars_id (λ k τ o pos ↦ ?_) 0 e
  cases o with
  | bound i =>
    simp only [Expression.liftBoundLam]
    by_cases hik : k ≤ i
    · rw [if_pos hik, Expression.mapVars, Expression.openVarLam]
      have h1 : ¬ i + 1 = k := by omega
      have h2 : k < i + 1 := by omega
      simp [h1, h2]
    · rw [if_neg hik, Expression.mapVars, Expression.openVarLam]
      have h1 : ¬ i = k := by omega
      have h2 : ¬ k < i := by omega
      simp [h1, h2]
  | _ => simp only [Expression.liftBoundLam, Expression.mapVars, Expression.openVarLam]

/-- Resolve every `.bound` occurrence in `e` to the free name its binding hint carries. `outer`
names the binders enclosing `e` that are not nodes within it — operator/function parameters, a
`multicast` filter's recipient — in source order, outermost first. Afterwards `e` holds no `.bound`
node: every former bound occurrence reads as `.free` of the string its binder recorded. The inverse
the elaborator performs is `close`; consumers that only read a term (code generation, pretty
printing) use this to work with names instead of indices. -/
partial def Expression.openHints {α} (outer : List String := []) (e : Expression α) : Expression α :=
  go (outer.foldr (λ n acc ↦ acc.openVar n) e)
where
  go (e : Expression α) : Expression α := match_source e with
  | .var τ o, pos => .var τ o @@ pos
  | .opCall g es, pos => .opCall (go g) (es.map go) @@ pos
  | .forall x ann dom body, pos => .forall x ann (go dom) (go (body.openVar x)) @@ pos
  | .exists x ann dom body, pos => .exists x ann (go dom) (go (body.openVar x)) @@ pos
  | .choose x ann dom body, pos => .choose x ann (go dom) (go (body.openVar x)) @@ pos
  | .set es τ, pos => .set (es.map go) τ @@ pos
  | .collect x ann dom pred, pos => .collect x ann (go dom) (go (pred.openVar x)) @@ pos
  | .map' body x ann cod dom, pos => .map' (go (body.openVar x)) x ann cod (go dom) @@ pos
  | .fnCall g fnTyp e', pos => .fnCall (go g) fnTyp (go e') @@ pos
  | .fn x ann cod dom body, pos => .fn x ann cod (go dom) (go (body.openVar x)) @@ pos
  | .record fs, pos => .record (fs.map λ (ann, nm, v) ↦ (ann, nm, go v)) @@ pos
  | .except g τ upds, pos =>
    .except (go g) τ
      (upds.map λ (path, v) ↦
        (path.map λ s ↦ match s with | .inl fld => .inl fld | .inr e' => .inr (go e'), go v)) @@ pos
  | .recordAccess g nm, pos => .recordAccess (go g) nm @@ pos
  | .tuple es, pos => .tuple (es.map λ (τ, e') ↦ (τ, go e')) @@ pos
  | .seq es τ, pos => .seq (es.map go) τ @@ pos
  | .if e₁ e₂ e₃ τ, pos => .if (go e₁) (go e₂) (go e₃) τ @@ pos
  | .case bs other τ, pos => .case (bs.map λ (p, q) ↦ (go p, go q)) (other.map go) τ @@ pos
  | .nat n, pos => .nat n @@ pos
  | .str s, pos => .str s @@ pos
  | .true, pos => .true @@ pos
  | .false, pos => .false @@ pos

/-- The `mapVars` action `subst x e` runs at every `.var` node: a `.var _ (.free x)` becomes `e`
lifted by the current binder depth; everything else is left. Named so lemmas compose without
re-inlining it. -/
def Expression.substLam {α} (x : String) (e : Expression α) :
    Nat → α → Origin → SourceSpan → Expression α :=
  λ k τ o pos ↦ match o with
    | .free n => if n = x then e.liftBound k else .var τ o @@ pos
    | _ => .var τ o @@ pos

/-- Substitute `e` for every free occurrence of the free name `x`. Captures nothing — `.free` and
`.bound` are disjoint — with `e` `liftBound`-ed by the binder depth it is spliced under. Sound only
when `e` is locally closed (`Expression.LC`); the `liftBound` is meaningless otherwise. -/
def Expression.subst {α} (x : String) (e : Expression α) (target : Expression α) : Expression α :=
  target.mapVars (Expression.substLam x e) 0

/-- `e` has no dangling de Bruijn index: every `.bound i` node sits under more than `i` enclosing
binders. Phrased so that any depth-tracking traversal that is the identity on `.bound i` below its
own depth (and on non-`.bound` origins) leaves `e` untouched, from any base depth — which is what
`liftBound`/`openVar`/`subst` all are, on their `.bound` arms, once `i` is genuinely bound. -/
def Expression.LC {α} (e : Expression α) : Prop :=
  ∀ (g : Nat → α → Origin → SourceSpan → Expression α) (base : Nat),
    (∀ d τ i pos, i < d → g d τ (.bound i) pos = Expression.var τ (.bound i) @@ pos) →
    (∀ d τ o pos, (∀ i, o ≠ .bound i) → g d τ o pos = Expression.var τ o @@ pos) →
    Expression.mapVars g base e = e

/-- A locally-closed term is fixed by `liftBound` at any amount. -/
theorem Expression.LC.liftBound_eq {α} {e : Expression α} (h : e.LC) (k : Nat) :
    e.liftBound k = e := by
  refine h (Expression.liftBoundLam k) 0 (λ d τ i pos hi ↦ ?_) (λ d τ o pos ho ↦ ?_)
  · simp only [Expression.liftBoundLam, if_neg (by omega : ¬ d ≤ i)]
  · cases o <;> simp_all [Expression.liftBoundLam]

/-- A locally-closed term is fixed by an `openVar` traversal at any base depth: there is no
outermost `.bound` for it to rename. -/
theorem Expression.LC.mapVars_openVarLam_eq {α} {e : Expression α} (h : e.LC) (name : String)
    (k : Nat) :
    Expression.mapVars (Expression.openVarLam name) k e = e := by
  refine h (Expression.openVarLam name) k (λ d τ i pos hi ↦ ?_) (λ d τ o pos ho ↦ ?_)
  · simp only [Expression.openVarLam, if_neg (by omega : ¬ i = d), if_neg (by omega : ¬ d < i)]
  · cases o <;> simp_all [Expression.openVarLam]

/-- From `l.attach.map f = l`, every element maps to itself. -/
private theorem attach_map_eq_self_of {β : Type} {l : List β} {f : {x // x ∈ l} → β}
    (h : l.attach.map f = l) : ∀ a : {x // x ∈ l}, f a = a.1 :=
  λ a ↦ List.map_inj_left.mp (h.trans (List.attach_map_subtype_val l).symm) a (List.mem_attach l a)

set_option maxHeartbeats 1000000 in
/-- The converse of `LC.mapVars_openVarLam_eq`: a term an `openVar` traversal fixes has no dangling
`.bound`, so *every* depth-tracking `.var`-identity traversal fixes it. Depth-generalised (an
`openVar` fixed at depth `k` is `LC` "shifted by `k`") so the binder arms carry through. -/
private theorem Expression.LC.of_openVar_eq_aux {α} {name : String}
    (g : Nat → α → Origin → SourceSpan → Expression α)
    (h1 : ∀ d τ i pos, i < d → g d τ (.bound i) pos = Expression.var τ (.bound i) @@ pos)
    (h2 : ∀ d τ o pos, (∀ i, o ≠ .bound i) → g d τ o pos = Expression.var τ o @@ pos) :
    ∀ (k : Nat) (e : Expression α),
      Expression.mapVars (Expression.openVarLam name) k e = e →
      ∀ base, Expression.mapVars g (base + k) e = e := by
  intro k e
  fun_induction Expression.mapVars (Expression.openVarLam name) k e with
  | case1 k' τ o pos =>
    intro h base
    simp only [Expression.mapVars]
    cases o with
    | bound i =>
      simp only [Expression.openVarLam] at h
      split_ifs at h with hc1 hc2
      · nomatch h
      · injection (Expression.var.inj h).2 with heq; omega
      · refine h1 (base + k') τ i pos ?_
        omega
    | free n => exact h2 (base + k') τ _ pos (λ _ hi ↦ nomatch hi)
    | «module» m n => exact h2 (base + k') τ _ pos (λ _ hi ↦ nomatch hi)
    | intrinsic n => exact h2 (base + k') τ _ pos (λ _ hi ↦ nomatch hi)
  | case2 k' g_ es pos ihg ihes =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with hg hes
    rw [ihg hg base]
    congr 1
    exact Eq.trans (List.map_congr_left λ a _ ↦ ihes a.1 a.2 (attach_map_eq_self_of hes a) base)
      (List.attach_map_subtype_val es)
  | case3 k' xh ann dom body pos ihd ihb =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with _ _ hd hb
    have hbk : base + k' + 1 = base + (k' + 1) := by omega
    rw [ihd hd base, hbk, ihb hb base]
  | case4 k' xh ann dom body pos ihd ihb =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with _ _ hd hb
    have hbk : base + k' + 1 = base + (k' + 1) := by omega
    rw [ihd hd base, hbk, ihb hb base]
  | case5 k' xh ann dom body pos ihd ihb =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with _ _ hd hb
    have hbk : base + k' + 1 = base + (k' + 1) := by omega
    rw [ihd hd base, hbk, ihb hb base]
  | case6 k' es τ pos ihes =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with hes
    congr 1
    exact Eq.trans (List.map_congr_left λ a _ ↦ ihes a.1 a.2 (attach_map_eq_self_of hes a) base)
      (List.attach_map_subtype_val es)
  | case7 k' xh ann dom body pos ihd ihb =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with _ _ hd hb
    have hbk : base + k' + 1 = base + (k' + 1) := by omega
    rw [ihd hd base, hbk, ihb hb base]
  | case8 k' body xh ann cod dom pos ihb ihd =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with hb _ _ _ hd
    have hbk : base + k' + 1 = base + (k' + 1) := by omega
    rw [ihd hd base, hbk, ihb hb base]
  | case9 k' g_ fnTyp e'' pos ihg ihe =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with hg _ he
    rw [ihg hg base, ihe he base]
  | case10 k' xh ann cod dom body pos ihd ihb =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with _ _ _ hd hb
    have hbk : base + k' + 1 = base + (k' + 1) := by omega
    rw [ihd hd base, hbk, ihb hb base]
  | case11 k' fs pos ihfs =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with hfs
    congr 1
    refine Eq.trans (List.map_congr_left λ a _ ↦ ?_) (List.attach_map_subtype_val fs)
    obtain ⟨⟨ann, nm, v⟩, hm⟩ := a
    have hfix := attach_map_eq_self_of hfs ⟨(ann, nm, v), hm⟩
    simp only [Prod.mk.injEq] at hfix
    exact Prod.ext rfl (Prod.ext rfl (ihfs ann nm v hm hfix.2.2 base))
  | case12 k' g_ τ upds pos ih3 ih2 ih1 =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with hg _ hu
    rw [ih3 hg base]
    congr 1
    refine Eq.trans (List.map_congr_left λ a _ ↦ ?_) (List.attach_map_subtype_val upds)
    obtain ⟨⟨path, v⟩, hpv⟩ := a
    have hpair := attach_map_eq_self_of hu ⟨(path, v), hpv⟩
    simp only [Prod.mk.injEq] at hpair
    refine congr_arg₂ Prod.mk ?_ (ih1 path v hpv hpair.2 base)
    refine Eq.trans (List.map_congr_left λ s _ ↦ ?_) (List.attach_map_subtype_val path)
    obtain ⟨s, hsp⟩ := s
    have hs := attach_map_eq_self_of hpair.1 ⟨s, hsp⟩
    cases s with
    | inl fld => rfl
    | inr e'' =>
      simp only [Sum.inr.injEq] at hs
      exact congrArg Sum.inr (ih2 path v hpv e'' hsp hs base)
  | case13 k' g_ nm pos ihg =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with hg _
    rw [ihg hg base]
  | case14 k' es pos ihes =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with hes
    congr 1
    refine Eq.trans (List.map_congr_left λ a _ ↦ ?_) (List.attach_map_subtype_val es)
    obtain ⟨⟨t, v⟩, hm⟩ := a
    have hthis := attach_map_eq_self_of hes ⟨(t, v), hm⟩
    simp only [Prod.mk.injEq] at hthis
    exact congr_arg₂ Prod.mk rfl (ihes t v hm hthis.2 base)
  | case15 k' es τ pos ihes =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with hes
    congr 1
    exact Eq.trans (List.map_congr_left λ a _ ↦ ihes a.1 a.2 (attach_map_eq_self_of hes a) base)
      (List.attach_map_subtype_val es)
  | case16 k' e₁ e₂ e₃ τ pos ih₁ ih₂ ih₃ =>
    intro h base
    simp only [Expression.mapVars, registerSource] at h ⊢
    injection h with h₁ h₂ h₃ _
    rw [ih₁ h₁ base, ih₂ h₂ base, ih₃ h₃ base]
  | case17 k' bs other τ pos ih3 ih2 ih1 =>
    intro h base
    have hBs : ∀ (H : bs.attach.map (λ a ↦
        (Expression.mapVars (Expression.openVarLam name) k' a.1.1,
         Expression.mapVars (Expression.openVarLam name) k' a.1.2)) = bs),
        bs.attach.map (λ a ↦ (Expression.mapVars g (base + k') a.1.1,
          Expression.mapVars g (base + k') a.1.2)) = bs := by
      intro H
      refine Eq.trans (List.map_congr_left λ a _ ↦ ?_) (List.attach_map_subtype_val bs)
      obtain ⟨⟨p, q⟩, hpq⟩ := a
      have hpq2 := attach_map_eq_self_of H ⟨(p, q), hpq⟩
      simp only [Prod.mk.injEq] at hpq2
      exact congr_arg₂ Prod.mk (ih3 p q hpq hpq2.1 base) (ih2 p q hpq hpq2.2 base)
    cases other with
    | none =>
      simp only [Expression.mapVars, registerSource] at h ⊢
      injection h with hbs _
      rw [hBs hbs]
    | some e'' =>
      simp only [Expression.mapVars, registerSource] at h ⊢
      injection h with hbs hother
      rw [Option.some.injEq] at hother
      rw [hBs hbs, ih1 hother base]
  | case18 => intro _ _; simp only [Expression.mapVars]
  | case19 => intro _ _; simp only [Expression.mapVars]
  | case20 => intro _ _; simp only [Expression.mapVars]
  | case21 => intro _ _; simp only [Expression.mapVars]

/-- The converse of `LC.mapVars_openVarLam_eq`: `openVar` fixing a term certifies it locally closed. -/
theorem Expression.LC.of_openVar_eq {α} {name : String} {e : Expression α}
    (h : Expression.openVar name e = e) : e.LC :=
  λ g base c1 c2 ↦ by
    have := Expression.LC.of_openVar_eq_aux g c1 c2 0 e h base
    simpa using this

/-- Substituting a free name and opening a binder body commute, provided the opened name is
distinct from the substituted one and the substituend is locally closed. The binder case of
`evalSubst'`. -/
theorem Expression.subst_openVar_comm {α} {x : String} {e' : Expression α} {z : String}
    (hlc : e'.LC) (hzx : z ≠ x) (k : Nat) (body : Expression α) :
    Expression.mapVars (Expression.openVarLam z) k (Expression.mapVars (Expression.substLam x e') k body)
      = Expression.mapVars (Expression.substLam x e') k
          (Expression.mapVars (Expression.openVarLam z) k body) := by
  refine Expression.mapVars_comm (λ k' τ o pos ↦ ?_) k body
  cases o with
  | free n =>
    simp only [Expression.substLam]
    by_cases hn : n = x
    · subst hn
      rewrite [if_pos rfl, hlc.liftBound_eq k', hlc.mapVars_openVarLam_eq z k']
      simp only [Expression.openVarLam, Expression.mapVars, Expression.substLam, reduceIte,
        hlc.liftBound_eq k']
    · rewrite [if_neg hn]
      simp only [Expression.openVarLam, Expression.mapVars, Expression.substLam, if_neg hn]
  | bound i =>
    simp only [Expression.substLam, Expression.openVarLam, Expression.mapVars, registerSource]
    split_ifs <;>
      simp only [Expression.substLam, Expression.mapVars, registerSource, if_neg hzx]
  | «module» m n => simp only [Expression.substLam, Expression.openVarLam, Expression.mapVars]
  | intrinsic n => simp only [Expression.substLam, Expression.openVarLam, Expression.mapVars]

/-- `subst` is the `mapVars` of `substLam`. Definitional; stated so `simp` can move between the
two without unfolding `subst` to a raw lambda. -/
theorem Expression.subst_eq_mapVars {α} (x : String) (e target : Expression α) :
    Expression.subst x e target = Expression.mapVars (Expression.substLam x e) 0 target := rfl

/-- The `mapVars` action `instantiate args` runs at every `.var` node: a `.bound` index at or past
the current binder depth is replaced by the corresponding `arg` (lifted past the crossed binders)
or shifted down by `args.length` when it points past them. Named so lemmas compose without
re-inlining it. -/
def Expression.instLam {α} (args : List (Expression α)) :
    Nat → α → Origin → SourceSpan → Expression α :=
  λ k τ o pos ↦ match o with
    | .bound i =>
      if i < k then .var τ (.bound i) @@ pos
      else if i - k < args.length then (args[i - k]!).liftBound k
      else .var τ (.bound (i - args.length)) @@ pos
    | _ => .var τ o @@ pos

/-- Instantiate the outermost de Bruijn binders with `args` (`args[0]` for `.bound 0`, …), shifting
every deeper index down by `args.length`. Operator/function parameter substitution. -/
def Expression.instantiate {α} (args : List (Expression α))
    (target : Expression α) : Expression α :=
  target.mapVars (Expression.instLam args) 0

set_option maxHeartbeats 1000000 in
/-- Bumping the base depth of a `mapVars` by one is unobservable when the per-node action `f`'s
answer at depth `d + 1` matches its answer at `d`. -/
theorem Expression.mapVars_succ_base {α}
    {f : Nat → α → Origin → SourceSpan → Expression α}
    (hf : ∀ d τ o pos, f (d + 1) τ o pos = f d τ o pos) :
    ∀ (k : Nat) (e : Expression α), Expression.mapVars f (k + 1) e = Expression.mapVars f k e := by
  intro k e
  fun_induction Expression.mapVars f k e with
  | case1 k' τ o pos => simp only [Expression.mapVars]; exact hf k' τ o pos
  | case2 k' g_ es pos ihg ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    exact List.map_congr_left λ a _ ↦ ihes a.1 a.2
  | case6 k' es τ pos ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    exact List.map_congr_left λ a _ ↦ ihes a.1 a.2
  | case15 k' es τ pos ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    exact List.map_congr_left λ a _ ↦ ihes a.1 a.2
  | case11 k' fs pos ihfs =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    refine List.map_congr_left λ a _ ↦ ?_
    obtain ⟨⟨ann, nm, v⟩, hm⟩ := a
    exact Prod.ext rfl (Prod.ext rfl (ihfs ann nm v hm))
  | case14 k' es pos ihes =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    refine List.map_congr_left λ a _ ↦ ?_
    obtain ⟨⟨t, v⟩, hm⟩ := a
    exact Prod.ext rfl (ihes t v hm)
  | case12 k' g_ τ upds pos ih3 ih2 ih1 =>
    simp only [Expression.mapVars, registerSource]
    congr 1
    refine List.map_congr_left λ a _ ↦ ?_
    obtain ⟨⟨path, v⟩, hpv⟩ := a
    refine Prod.ext (List.map_congr_left λ s _ ↦ ?_) (ih1 path v hpv)
    obtain ⟨s, hsp⟩ := s
    cases s with
    | inl fld => rfl
    | inr e'' => exact congrArg Sum.inr (ih2 path v hpv e'' hsp)
  | case17 k' bs other τ pos ih3 ih2 ih1 =>
    cases other with
    | none =>
      simp only [Expression.mapVars, registerSource]
      congr 1
      refine List.map_congr_left λ a _ ↦ ?_
      obtain ⟨⟨p, q⟩, hpq⟩ := a
      exact Prod.ext (ih3 p q hpq) (ih2 p q hpq)
    | some e' =>
      simp only [Expression.mapVars, registerSource]
      congr 1
      · refine List.map_congr_left λ a _ ↦ ?_
        obtain ⟨⟨p, q⟩, hpq⟩ := a
        exact Prod.ext (ih3 p q hpq) (ih2 p q hpq)
      · exact congrArg some ih1
  | _ =>
    simp only [Expression.mapVars, registerSource]
    all: congr 1

/-- Iterated `mapVars_succ_base`: a depth-agnostic action's `mapVars` is depth-independent. -/
theorem Expression.mapVars_base_irrel {α}
    {f : Nat → α → Origin → SourceSpan → Expression α}
    (hf : ∀ d τ o pos, f (d + 1) τ o pos = f d τ o pos) (k : Nat) (e : Expression α) :
    Expression.mapVars f k e = Expression.mapVars f 0 e := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Expression.mapVars_succ_base hf, ih]

/-- A locally-closed term is fixed by a `liftBound` traversal at any base depth. -/
theorem Expression.LC.mapVars_liftBoundLam_eq {α} {e : Expression α} (h : e.LC) (d k : Nat) :
    Expression.mapVars (Expression.liftBoundLam d) k e = e :=
  h (Expression.liftBoundLam d) k
    (λ d' τ i pos hi ↦ by simp only [Expression.liftBoundLam, if_neg (by omega : ¬ d' ≤ i)])
    (λ d' τ o pos ho ↦ by cases o <;> simp_all [Expression.liftBoundLam])

/-- A locally-closed term is fixed by an `instantiate` traversal at any base depth: it has no free
`.bound` for `instLam` to replace. -/
theorem Expression.LC.mapVars_instLam_eq {α} {e : Expression α} (h : e.LC)
    (args : List (Expression α)) (k : Nat) :
    Expression.mapVars (Expression.instLam args) k e = e :=
  h (Expression.instLam args) k
    (λ d' τ i pos hi ↦ by simp only [Expression.instLam, if_pos hi])
    (λ d' τ o pos ho ↦ by cases o <;> simp_all [Expression.instLam])

/-- For a locally-closed substituend, `substLam` ignores the depth it runs at, so `subst` reads off
a `mapVars` of `substLam` at any base depth. -/
theorem Expression.LC.mapVars_substLam_eq {α} {x : String} {e' : Expression α}
    (hlc : e'.LC) (k : Nat) (t : Expression α) :
    Expression.mapVars (Expression.substLam x e') k t = Expression.subst x e' t := by
  rw [Expression.subst_eq_mapVars]
  refine Expression.mapVars_base_irrel (λ d τ o pos ↦ ?_) k t
  cases o with
  | free n =>
    by_cases hn : n = x
    · subst hn; simp only [Expression.substLam, hlc.liftBound_eq (d + 1), hlc.liftBound_eq d]
    · simp only [Expression.substLam, if_neg hn]
  | bound i => simp only [Expression.substLam]
  | «module» m n => simp only [Expression.substLam]
  | intrinsic n => simp only [Expression.substLam]

/-! ### `subst`, structurally

`subst` pushes through every constructor. The binder arms descend the body at depth `1`; under
`e'.LC` that `mapVars _ 1` is `subst` again (`LC.mapVars_substLam_eq`), so `LC.subst_*` state the
fully-recursive shape `evalSubst'` reads off. -/

section SubstStruct
variable {α : Type} {x : String} {e' : Expression α}

theorem Expression.subst_nat {s : String} :
    Expression.subst x e' (Expression.nat s) = Expression.nat s := by
  simp only [Expression.subst, Expression.mapVars, registerSource]

theorem Expression.subst_str {s : String} :
    Expression.subst x e' (Expression.str s) = Expression.str s := by
  simp only [Expression.subst, Expression.mapVars, registerSource]

theorem Expression.subst_true :
    Expression.subst x e' (Expression.true : Expression α) = Expression.true := by
  simp only [Expression.subst, Expression.mapVars, registerSource]

theorem Expression.subst_false :
    Expression.subst x e' (Expression.false : Expression α) = Expression.false := by
  simp only [Expression.subst, Expression.mapVars, registerSource]

theorem Expression.subst_var_module {τ : α} {m n : String} :
    Expression.subst x e' (Expression.var τ (.module m n)) = Expression.var τ (.module m n) := by
  simp only [Expression.subst, Expression.mapVars, Expression.substLam, registerSource]

theorem Expression.subst_var_intrinsic {τ : α} {n : String} :
    Expression.subst x e' (Expression.var τ (.intrinsic n)) = Expression.var τ (.intrinsic n) := by
  simp only [Expression.subst, Expression.mapVars, Expression.substLam, registerSource]

theorem Expression.subst_var_bound {τ : α} {i : Nat} :
    Expression.subst x e' (Expression.var τ (.bound i)) = Expression.var τ (.bound i) := by
  simp only [Expression.subst, Expression.mapVars, Expression.substLam, registerSource]

theorem Expression.subst_var_free_ne {τ : α} {n : String} (h : n ≠ x) :
    Expression.subst x e' (Expression.var τ (.free n)) = Expression.var τ (.free n) := by
  simp only [Expression.subst, Expression.mapVars, Expression.substLam, if_neg h, registerSource]

theorem Expression.LC.subst_var_free_eq {τ : α} (hlc : e'.LC) :
    Expression.subst x e' (Expression.var τ (.free x)) = e' := by
  simp only [Expression.subst, Expression.mapVars, Expression.substLam, if_true]
  exact hlc.liftBound_eq 0

theorem Expression.subst_opCall {g : Expression α} {es : List (Expression α)} :
    Expression.subst x e' (Expression.opCall g es)
      = Expression.opCall (Expression.subst x e' g) (es.map (Expression.subst x e')) := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars, registerSource, List.map_attach_eq_pmap, List.pmap_eq_map]
  rfl

theorem Expression.subst_fnCall {f e'' : Expression α} {τ : α} :
    Expression.subst x e' (Expression.fnCall f τ e'')
      = Expression.fnCall (Expression.subst x e' f) τ (Expression.subst x e' e'') := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars, registerSource]
  rfl

theorem Expression.subst_recordAccess {f : Expression α} {n : String} :
    Expression.subst x e' (Expression.recordAccess f n)
      = Expression.recordAccess (Expression.subst x e' f) n := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars, registerSource]
  rfl

theorem Expression.subst_if {a b c : Expression α} {τ : α} :
    Expression.subst x e' (Expression.if a b c τ)
      = Expression.if (Expression.subst x e' a) (Expression.subst x e' b) (Expression.subst x e' c) τ := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars, registerSource]
  rfl

theorem Expression.subst_set {es : List (Expression α)} {τ : α} :
    Expression.subst x e' (Expression.set es τ)
      = Expression.set (es.map (Expression.subst x e')) τ := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars, registerSource,
    List.map_attach_eq_pmap, List.pmap_eq_map]
  rfl

theorem Expression.subst_seq {es : List (Expression α)} {τ : α} :
    Expression.subst x e' (Expression.seq es τ)
      = Expression.seq (es.map (Expression.subst x e')) τ := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars, registerSource,
    List.map_attach_eq_pmap, List.pmap_eq_map]
  rfl

theorem Expression.subst_tuple {es : List (α × Expression α)} :
    Expression.subst x e' (Expression.tuple es)
      = Expression.tuple (es.map λ p ↦ (p.1, Expression.subst x e' p.2)) := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars, registerSource,
    List.map_attach_eq_pmap, List.pmap_eq_map]
  rfl

theorem Expression.subst_record {fs : List (α × String × Expression α)} :
    Expression.subst x e' (Expression.record fs)
      = Expression.record (fs.map λ p ↦ (p.1, p.2.1, Expression.subst x e' p.2.2)) := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars, registerSource,
    List.map_attach_eq_pmap, List.pmap_eq_map]
  rfl

theorem Expression.LC.subst_forall {x' : String} {τ : α} {dom body : Expression α} (hlc : e'.LC) :
    Expression.subst x e' (Expression.forall x' τ dom body)
      = Expression.forall x' τ (Expression.subst x e' dom) (Expression.subst x e' body) := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars]
  simp only [registerSource, hlc.mapVars_substLam_eq]

theorem Expression.LC.subst_exists {x' : String} {τ : α} {dom body : Expression α} (hlc : e'.LC) :
    Expression.subst x e' (Expression.exists x' τ dom body)
      = Expression.exists x' τ (Expression.subst x e' dom) (Expression.subst x e' body) := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars]
  simp only [registerSource, hlc.mapVars_substLam_eq]

theorem Expression.LC.subst_choose {x' : String} {τ : α} {dom body : Expression α} (hlc : e'.LC) :
    Expression.subst x e' (Expression.choose x' τ dom body)
      = Expression.choose x' τ (Expression.subst x e' dom) (Expression.subst x e' body) := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars]
  simp only [registerSource, hlc.mapVars_substLam_eq]

theorem Expression.LC.subst_collect {x' : String} {τ : α} {dom body : Expression α} (hlc : e'.LC) :
    Expression.subst x e' (Expression.collect x' τ dom body)
      = Expression.collect x' τ (Expression.subst x e' dom) (Expression.subst x e' body) := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars]
  simp only [registerSource, hlc.mapVars_substLam_eq]

theorem Expression.LC.subst_map' {x' : String} {ann cod : α} {dom body : Expression α} (hlc : e'.LC) :
    Expression.subst x e' (Expression.map' body x' ann cod dom)
      = Expression.map' (Expression.subst x e' body) x' ann cod (Expression.subst x e' dom) := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars]
  simp only [registerSource, hlc.mapVars_substLam_eq]

theorem Expression.LC.subst_fn {x' : String} {ann cod : α} {dom body : Expression α} (hlc : e'.LC) :
    Expression.subst x e' (Expression.fn x' ann cod dom body)
      = Expression.fn x' ann cod (Expression.subst x e' dom) (Expression.subst x e' body) := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars]
  simp only [registerSource, hlc.mapVars_substLam_eq]

/-- `l.attach.map f = l.map g` once each element maps like `g` on its value. -/
private theorem attach_map_of {β γ : Type} {l : List β} {f : {x // x ∈ l} → γ} {g : β → γ}
    (h : ∀ a : {x // x ∈ l}, f a = g a.1) : l.attach.map f = l.map g := by
  rw [← List.attach_map_val (f := g)]
  exact List.map_congr_left λ a _ ↦ h a

theorem Expression.subst_except_single {f : Expression α} {τ : α}
    {path : List (String ⊕ Expression α)} {rhs : Expression α} :
    Expression.subst x e' (Expression.except f τ [(path, rhs)])
      = Expression.except (Expression.subst x e' f) τ
          [(path.map λ s ↦ s.map id (Expression.subst x e'), Expression.subst x e' rhs)] := by
  rewrite [Expression.subst_eq_mapVars]
  simp only [Expression.mapVars, registerSource, List.attach_cons, List.attach_nil,
    List.map_cons, List.map_nil]
  refine congrArg (Expression.except _ τ) (congrArg (· :: [])
    (Prod.ext (attach_map_of (g := λ s : String ⊕ Expression α ↦ s.map id (Expression.subst x e'))
      λ a ↦ ?_) rfl))
  obtain ⟨s, hs⟩ := a
  cases s <;> rfl

theorem Expression.subst_case {bs : List (Expression α × Expression α)}
    {other : Option (Expression α)} {τ : α} :
    Expression.subst x e' (Expression.case bs other τ)
      = Expression.case (bs.map λ p ↦ (Expression.subst x e' p.1, Expression.subst x e' p.2))
          (other.map (Expression.subst x e')) τ := by
  rcases other with _ | o <;>
    simp only [Expression.subst, Expression.mapVars, registerSource, List.map_attach_eq_pmap,
      List.pmap_eq_map, Option.map_none, Option.map_some]

end SubstStruct

/-- Opening a binder body one level out commutes with a `subst` that descended one level into it,
when the opened name is distinct from the substituted one and the substituend is locally closed.
The `.forall`/`.exists`/… case of `evalSubst'`. -/
theorem Expression.subst_openVar_one_comm {α} {x : String} {e' : Expression α} {z : String}
    (hlc : e'.LC) (hzx : z ≠ x) (body : Expression α) :
    Expression.mapVars (Expression.openVarLam z) 0
        (Expression.mapVars (Expression.substLam x e') 1 body)
      = Expression.subst x e' (Expression.mapVars (Expression.openVarLam z) 0 body) := by
  rw [hlc.mapVars_substLam_eq 1 body, ← hlc.mapVars_substLam_eq 0 (mapVars (openVarLam z) 0 body),
    Expression.subst_eq_mapVars]
  exact Expression.subst_openVar_comm hlc hzx 0 body

/-- Opening a substituted body and substituting an opened body agree, once the opened name avoids
the substituted one and the substituend is locally closed. The `evalSubst'` binder step, phrased
directly on `subst`/`openVar`. -/
theorem Expression.LC.subst_openVar {α} {x z : String} {e' : Expression α}
    (hlc : e'.LC) (hzx : z ≠ x) (body : Expression α) :
    (Expression.subst x e' body).openVar z = Expression.subst x e' (body.openVar z) :=
  Expression.subst_openVar_comm hlc hzx 0 body

/-- `subst` commutes with `liftBound` when the substituend is locally closed. -/
theorem Expression.subst_liftBound_comm {α} {x : String} {e' t : Expression α}
    (hlc : e'.LC) (k : Nat) :
    Expression.subst x e' (t.liftBound k) = (Expression.subst x e' t).liftBound k := by
  rw [Expression.subst_eq_mapVars, Expression.subst_eq_mapVars, Expression.liftBound,
    Expression.liftBound]
  refine Expression.mapVars_comm (λ k' τ o pos ↦ ?_) 0 t
  cases o with
  | free n =>
    by_cases hn : n = x
    · subst hn
      simp only [Expression.substLam, Expression.liftBoundLam, Expression.mapVars, if_true,
        hlc.liftBound_eq, hlc.mapVars_liftBoundLam_eq]
    · simp only [Expression.liftBoundLam, Expression.substLam, if_neg hn, Expression.mapVars]
  | bound i =>
    simp only [Expression.liftBoundLam, Expression.substLam, Expression.mapVars]
  | «module» m n => simp only [Expression.liftBoundLam, Expression.substLam, Expression.mapVars]
  | intrinsic n => simp only [Expression.liftBoundLam, Expression.substLam, Expression.mapVars]

/-! ### `LC` introduction -/

/-- A `.var` at a non-`.bound` origin is locally closed. -/
theorem Expression.LC.varClosed {α} {τ : α} {o : Origin} (ho : ∀ i, o ≠ .bound i) :
    (Expression.var τ o).LC :=
  λ g base _ h2 ↦ by simpa only [Expression.mapVars] using h2 base τ o _ ho

/-- An `.opCall` of locally-closed parts is locally closed. -/
theorem Expression.LC.opCall {α} {g : Expression α} {es : List (Expression α)}
    (hg : g.LC) (hes : ∀ e ∈ es, e.LC) : (Expression.opCall g es).LC := by
  intro f base h1 h2
  simp only [Expression.mapVars, registerSource]
  congr 1
  · exact hg f base h1 h2
  · exact Eq.trans (List.map_congr_left λ a _ ↦ hes a.1 a.2 f base h1 h2)
      (List.attach_map_subtype_val es)

/-- A one-entry `except` of locally-closed parts is locally closed. -/
theorem Expression.LC.except_single {α} {g : Expression α} {τ : α}
    {path : List (String ⊕ Expression α)} {rhs : Expression α}
    (hg : g.LC) (hpath : ∀ e, Sum.inr e ∈ path → e.LC) (hrhs : rhs.LC) :
    (Expression.except g τ [(path, rhs)]).LC := by
  intro f base h1 h2
  simp only [Expression.mapVars, registerSource]
  congr 1
  · exact hg f base h1 h2
  · refine congrArg (· :: []) (Prod.ext ?_ (hrhs f base h1 h2))
    exact Eq.trans (List.map_congr_left λ s hs ↦ by
        obtain ⟨s, hsp⟩ := s
        cases s with
        | inl fld => rfl
        | inr e'' => exact congrArg Sum.inr (hpath e'' hsp f base h1 h2))
      (List.attach_map_subtype_val path)

/-- `liftBound` of a locally-closed term is locally closed (it is the term itself). -/
theorem Expression.LC.liftBound {α} {e : Expression α} (h : e.LC) (k : Nat) :
    (e.liftBound k).LC := (h.liftBound_eq k).symm ▸ h

/-- A `.fnCall` of locally-closed parts is locally closed. -/
theorem Expression.LC.fnCall {α} {g : Expression α} {fnTyp : α} {e : Expression α}
    (hg : g.LC) (he : e.LC) : (Expression.fnCall g fnTyp e).LC := by
  intro f base h1 h2
  simp only [Expression.mapVars, registerSource]
  rw [hg f base h1 h2, he f base h1 h2]

/-- A `.recordAccess` of a locally-closed part is locally closed. -/
theorem Expression.LC.recordAccess {α} {g : Expression α} {nm : String} (hg : g.LC) :
    (Expression.recordAccess g nm).LC := by
  intro f base h1 h2
  simp only [Expression.mapVars, registerSource]
  rw [hg f base h1 h2]

/-- `e'[e\r]`: substitutes a preceding `r≔e` assignment's effect into a later expression `e'`. A
bare-variable `r` (no `.args`) substitutes the name directly; a compound `r` (with field/index
segments) instead substitutes the whole variable with `[var(r) EXCEPT !path = e]`. `r.args` is
already the `List (String ⊕ Expression α)` shape `Expression.except` takes, so it is a one-entry
`except` list, no reshaping needed. -/
def Expression.substRef {α} (r : ElaboratedPlusCal.Ref α (Expression α)) (rhs e' : Expression α) :
    Expression α :=
  if r.args.isEmpty then
    Expression.subst r.name rhs e'
  else
    -- The synthesized `EXCEPT` stands for the assignment whose right-hand side `rhs` is, so it
    -- takes that expression's span.
    let pos := posOf rhs
    Expression.subst r.name
      (.except (.var r.baseType (.free r.name) @@ pos) r.baseType [(r.args, rhs)] @@ pos) e'

/-! The two branches of `substRef`, named. Both readings get used — `ExprSemantics.evalSubstRef`
(`Core/ComputableTLAPlus/Semantics/Interface.lean`) proves one case of its `↔` from each — and
neither states the `@@` tags, which are definitionally transparent (`Common/Position.lean`) and only
noise in a consumer's goal. -/

/-- At a bare reference, `substRef` is plain substitution of the right-hand side. -/
theorem Expression.substRef_of_args_nil {α} {r : ElaboratedPlusCal.Ref α (Expression α)}
    (h : r.args = []) (rhs e' : Expression α) :
    Expression.substRef r rhs e' = Expression.subst r.name rhs e' := by
  simp only [Expression.substRef, h, List.isEmpty_nil, if_true]

/-- At a compound reference, `substRef` substitutes the base variable by a one-entry `EXCEPT`
rebuilding it along the reference's own path. -/
theorem Expression.substRef_of_args_ne_nil {α} {r : ElaboratedPlusCal.Ref α (Expression α)}
    (h : r.args ≠ []) (rhs e' : Expression α) :
    Expression.substRef r rhs e' =
      Expression.subst r.name
        (.except (.var r.baseType (.free r.name)) r.baseType [(r.args, rhs)]) e' := by
  simp only [Expression.substRef, List.isEmpty_iff, h, if_false]

end ComputableTLAPlus

end
