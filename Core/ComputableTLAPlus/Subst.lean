module

meta import CustomPrelude
public import Core.ComputableTLAPlus.Syntax
public import Core.TypedPlusCal.Syntax
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section


/-!
  Free variables of, and capture-avoiding substitution for, a `ComputableTLAPlus.Expression`.

  `Expression.freeVars` counts every name read from memory: an `Origin.binder` `.var` node not
  shadowed by an enclosing binder for that name. `.var` nodes of `Origin.module`/`Origin.intrinsic`
  name a module-level operator, a `CONSTANT`, or a builtin — resolved through `Ξ`/`Ω`, never memory —
  so they contribute nothing.

  `Expression.subst` is a genuine capture-avoiding substitution: a binder whose name would capture a
  free variable of the replacement expression is renamed to a fresh name (`freshFor`) before the
  substitution descends under it. It stays computable — the fresh name is chosen deterministically,
  by pigeonhole over `avoid.card + 1` distinct candidates.
-/

namespace ComputableTLAPlus

/-- Every name `target` reads from memory: every `Origin.binder` `Expression.var` node not shadowed
by an enclosing binder for that name. A `.var` of `Origin.module`/`Origin.intrinsic` names a
module-level operator, a `CONSTANT`, or a builtin — resolved through `Ξ`/`Ω`, never memory — so it
contributes nothing, exactly as `Expression.subst` (which only rewrites `Origin.binder` nodes)
treats it. -/
def Expression.freeVars {α} (target : Expression α) : Finset String := match target with
  | .var y _ .binder => {y}
  | .var _ _ _ => ∅
  | .opCall f es => f.freeVars ∪ (es.attach.map λ ⟨e', _hes⟩ ↦ e'.freeVars).foldl (· ∪ ·) ∅
  | .forall y _ dom body => dom.freeVars ∪ body.freeVars.erase y
  | .exists y _ dom body => dom.freeVars ∪ body.freeVars.erase y
  | .choose y _ dom body => dom.freeVars ∪ body.freeVars.erase y
  | .set es _ => (es.attach.map λ ⟨e', _hes⟩ ↦ e'.freeVars).foldl (· ∪ ·) ∅
  | .collect y _ dom pred => dom.freeVars ∪ pred.freeVars.erase y
  | .map' body y _ _ dom => dom.freeVars ∪ body.freeVars.erase y
  | .fnCall f _ e' => f.freeVars ∪ e'.freeVars
  | .fn y _ _ dom body => dom.freeVars ∪ body.freeVars.erase y
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

/-- There is a name of the form `base$`, `base$#`, `base$##`, … outside any finite `avoid`: the map
`n ↦ base$` followed by `n` copies of `#` is injective, so its range is infinite and cannot sit
inside `avoid`. -/
theorem freshFor_exists (avoid : Finset String) (base : String) :
    ∃ n : ℕ, (base ++ "$" ++ String.ofList (List.replicate n '#')) ∉ avoid := by
  have hinj :
      Function.Injective (λ n : ℕ ↦ base ++ "$" ++ String.ofList (List.replicate n '#')) := by
    intro a b h
    simp only at h
    have h2 : String.ofList (List.replicate a '#') = String.ofList (List.replicate b '#') :=
      (String.append_right_inj (base ++ "$")).mp h
    have h3 := congrArg String.toList h2
    rw [String.toList_ofList, String.toList_ofList] at h3
    simpa using congrArg List.length h3
  obtain ⟨_, ⟨n, rfl⟩, ha⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finset avoid
  exact ⟨n, ha⟩

/-- A name not in `avoid`, chosen deterministically: `base$` followed by the least number of `#`s
that misses `avoid`. Used to rename a binder out of the way of a capture-avoiding substitution. -/
def freshFor (avoid : Finset String) (base : String) : String :=
  base ++ "$" ++ String.ofList (List.replicate (Nat.find (freshFor_exists avoid base)) '#')

@[inherit_doc freshFor]
theorem freshFor_not_mem (avoid : Finset String) (base : String) : freshFor avoid base ∉ avoid :=
  Nat.find_spec (freshFor_exists avoid base)

-- `freshFor_not_mem` is the whole interface: nothing downstream may reason about the name's shape.
attribute [irreducible] freshFor

/-- The capture-avoiding substitution engine. `σ` maps a name to its replacement (used at a free
`Origin.binder` occurrence), `ρ` records the binders renamed on the way down (a renamed binder's
occurrences take the new name, and neither `σ` nor the fall-through applies to it), and `avoid`
collects every name a freshly renamed binder must dodge — the free variables of `σ`'s range, plus
every rename already performed. A binder whose name is in `avoid` is renamed via `freshFor`; one
that is not keeps its name but still shadows `σ`/`ρ` for that name inside its body. -/
def Expression.substAux {α} (σ : String → Option (Expression α)) (ρ : String → Option String)
    (avoid : Finset String) (target : Expression α) : Expression α := match_source target with
  | .var y τ o, pos =>
    if o == .binder then
      match ρ y with
      | some y' => .var y' τ .binder @@ pos
      | none => (σ y).getD (.var y τ o @@ pos)
    else .var y τ o @@ pos
  | .opCall f es, pos =>
    .opCall (substAux σ ρ avoid f) (es.attach.map λ ⟨e', _hes⟩ ↦ substAux σ ρ avoid e') @@ pos
  | .forall y ann dom body, pos =>
    let dom' := substAux σ ρ avoid dom
    if y ∈ avoid then
      let y' := freshFor (avoid ∪ body.freeVars) y
      .forall y' ann dom' (substAux σ (Function.update ρ y (some y')) (insert y' avoid) body) @@ pos
    else .forall y ann dom' (substAux σ (Function.update ρ y (some y)) avoid body) @@ pos
  | .exists y ann dom body, pos =>
    let dom' := substAux σ ρ avoid dom
    if y ∈ avoid then
      let y' := freshFor (avoid ∪ body.freeVars) y
      .exists y' ann dom' (substAux σ (Function.update ρ y (some y')) (insert y' avoid) body) @@ pos
    else .exists y ann dom' (substAux σ (Function.update ρ y (some y)) avoid body) @@ pos
  | .choose y ann dom body, pos =>
    let dom' := substAux σ ρ avoid dom
    if y ∈ avoid then
      let y' := freshFor (avoid ∪ body.freeVars) y
      .choose y' ann dom' (substAux σ (Function.update ρ y (some y')) (insert y' avoid) body) @@ pos
    else .choose y ann dom' (substAux σ (Function.update ρ y (some y)) avoid body) @@ pos
  | .collect y ann dom pred, pos =>
    let dom' := substAux σ ρ avoid dom
    if y ∈ avoid then
      let y' := freshFor (avoid ∪ pred.freeVars) y
      .collect y' ann dom' (substAux σ (Function.update ρ y (some y')) (insert y' avoid) pred) @@ pos
    else .collect y ann dom' (substAux σ (Function.update ρ y (some y)) avoid pred) @@ pos
  | .map' body y ann cod dom, pos =>
    let dom' := substAux σ ρ avoid dom
    if y ∈ avoid then
      let y' := freshFor (avoid ∪ body.freeVars) y
      .map' (substAux σ (Function.update ρ y (some y')) (insert y' avoid) body) y' ann cod dom' @@ pos
    else .map' (substAux σ (Function.update ρ y (some y)) avoid body) y ann cod dom' @@ pos
  | .fn y ann cod dom body, pos =>
    let dom' := substAux σ ρ avoid dom
    if y ∈ avoid then
      let y' := freshFor (avoid ∪ body.freeVars) y
      .fn y' ann cod dom' (substAux σ (Function.update ρ y (some y')) (insert y' avoid) body) @@ pos
    else .fn y ann cod dom' (substAux σ (Function.update ρ y (some y)) avoid body) @@ pos
  | .set es τ, pos => .set (es.attach.map λ ⟨e', _hes⟩ ↦ substAux σ ρ avoid e') τ @@ pos
  | .fnCall f fnTyp e', pos => .fnCall (substAux σ ρ avoid f) fnTyp (substAux σ ρ avoid e') @@ pos
  | .record fs, pos =>
    .record (fs.attach.map λ ⟨(ann, name, v), _hfs⟩ ↦ (ann, name, substAux σ ρ avoid v)) @@ pos
  | .except f τ upds, pos =>
    .except (substAux σ ρ avoid f) τ
      (upds.attach.map λ ⟨(path, v), _hupds⟩ ↦
        (path.attach.map λ ⟨s, _hpath⟩ ↦
            match s with | .inl field => .inl field | .inr e' => .inr (substAux σ ρ avoid e'),
         substAux σ ρ avoid v)) @@ pos
  | .recordAccess f name, pos => .recordAccess (substAux σ ρ avoid f) name @@ pos
  | .tuple es, pos => .tuple (es.attach.map λ ⟨(τ, e'), _hes⟩ ↦ (τ, substAux σ ρ avoid e')) @@ pos
  | .seq es τ, pos => .seq (es.attach.map λ ⟨e', _hes⟩ ↦ substAux σ ρ avoid e') τ @@ pos
  | .if e₁ e₂ e₃ τ, pos =>
    .if (substAux σ ρ avoid e₁) (substAux σ ρ avoid e₂) (substAux σ ρ avoid e₃) τ @@ pos
  | .case bs other τ, pos =>
    .case (bs.attach.map λ ⟨(p, q), _hbs⟩ ↦ (substAux σ ρ avoid p, substAux σ ρ avoid q))
      (match other with | none => none | some e' => some (substAux σ ρ avoid e')) τ @@ pos
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

/-- Substitute every free occurrence of the *lexically-bound* variable `x` with `e`, renaming any
binder that would otherwise capture a free variable of `e`, and stopping at any binder that rebinds
`x`. Only an `Origin.binder` occurrence of the name is replaced: a `.var x _ (.module _)` or
`.var x _ .intrinsic` node that happens to carry the same string names a module-level operator, a
`CONSTANT`, or a hardcoded builtin, not the bound variable, and is left untouched. -/
def Expression.subst {α} (x : String) (e : Expression α) (target : Expression α) : Expression α :=
  target.substAux (λ z ↦ if z == x then some e else none) (λ _ ↦ none) e.freeVars

/-- `e'[e\r]`: substitutes a preceding `r≔e` assignment's effect into a later expression `e'`. A
bare-variable `r` (no `.args`) substitutes directly; a compound `r` (with field/index segments)
instead substitutes the whole variable with `[var(r) EXCEPT !path = e]`. `r.args` is already the
`List (String ⊕ Expression α)` shape `Expression.except` takes, so it's just a one-entry `except`
list, no reshaping needed. -/
def Expression.substRef {α} (r : ElaboratedPlusCal.Ref α (Expression α)) (rhs e' : Expression α) :
    Expression α :=
  if r.args.isEmpty then
    Expression.subst r.name rhs e'
  else
    -- The synthesized `EXCEPT` stands for the assignment whose right-hand side `rhs` is, so it
    -- takes that expression's span.
    let pos := posOf rhs
    Expression.subst r.name
      (.except (.var r.name r.baseType .binder @@ pos) r.baseType [(r.args, rhs)] @@ pos) e'

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
        (.except (.var r.name r.baseType .binder) r.baseType [(r.args, rhs)]) e' := by
  simp only [Expression.substRef, List.isEmpty_iff, h, if_false]

end ComputableTLAPlus

end
