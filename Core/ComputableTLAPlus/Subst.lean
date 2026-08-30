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

/-- Add `d` to every `.bound` index that refers past `e`'s own binders. -/
def Expression.liftBound {α} (d : Nat) (e : Expression α) : Expression α :=
  e.mapVars (λ k τ o pos ↦ match o with
    | .bound i => .var τ (.bound (if k ≤ i then i + d else i)) @@ pos
    | _ => .var τ o @@ pos) 0

/-- In a binder's body — already stripped of that binder — turn the reference to the removed binder
into the free name `name`, and shift every deeper free index down by one. -/
def Expression.openVar {α} (name : String) (e : Expression α) : Expression α :=
  e.mapVars (λ k τ o pos ↦ match o with
    | .bound i =>
      if i = k then .var τ (.free name) @@ pos
      else if k < i then .var τ (.bound (i - 1)) @@ pos
      else .var τ (.bound i) @@ pos
    | _ => .var τ o @@ pos) 0

/-- Bind every free occurrence of `name` as a new outermost `.bound`, shifting every deeper free
index up by one. Inverse of `openVar`. -/
def Expression.close {α} (name : String) (e : Expression α) : Expression α :=
  e.mapVars (λ k τ o pos ↦ match o with
    | .free n => if n = name then .var τ (.bound k) @@ pos else .var τ o @@ pos
    | .bound i => .var τ (.bound (if k ≤ i then i + 1 else i)) @@ pos
    | _ => .var τ o @@ pos) 0

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

/-- Substitute `e` for every free occurrence of the free name `x`. Captures nothing — `.free` and
`.bound` are disjoint — with `e` `liftBound`-ed by the binder depth it is spliced under. -/
def Expression.subst {α} (x : String) (e : Expression α) (target : Expression α) : Expression α :=
  target.mapVars (λ k τ o pos ↦ match o with
    | .free n => if n = x then e.liftBound k else .var τ o @@ pos
    | _ => .var τ o @@ pos) 0

/-- Instantiate the outermost de Bruijn binders with `args` (`args[0]` for `.bound 0`, …), shifting
every deeper index down by `args.length`. Operator/function parameter substitution. -/
def Expression.instantiate {α} (args : List (Expression α))
    (target : Expression α) : Expression α :=
  target.mapVars (λ k τ o pos ↦ match o with
    | .bound i =>
      if i < k then .var τ (.bound i) @@ pos
      else if i - k < args.length then (args[i - k]!).liftBound k
      else .var τ (.bound (i - args.length)) @@ pos
    | _ => .var τ o @@ pos) 0

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
