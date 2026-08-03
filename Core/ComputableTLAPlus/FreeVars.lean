module

public import Core.ComputableTLAPlus.Syntax
public import Core.GuardedPlusCal.Syntax
public import Mathlib.Data.Finset.Basic

@[expose] public section


/-!
  Free variables of a `ComputableTLAPlus.Expression`, mirroring `Expression.subst`'s
  (`Subst.lean`) binder handling case for case — a name is free exactly where `subst` would
  substitute into it. `x`'s own binder position (a `forall`/`exists`/`choose`/`collect`'s `dom`,
  `map'`/`fn`'s `dom`) is *not* under the bound name's scope, matching `subst`'s own asymmetry
  between the conditionally-substituted body and the unconditionally-substituted domain.

  `.record`'s field labels and `.except`'s `.inl` path segments are plain strings, not variable
  references, so they never contribute — same reading `subst` gives them (untouched).
-/

namespace ComputableTLAPlus

/-- Every name `target` reads, i.e. every `Expression.var` node not shadowed by an enclosing
binder for that name. -/
def Expression.freeVars {α} (target : Expression α) : Finset String := match target with
  | .var y _ _ => {y}
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
  all_goals simp_wf
  all_goals first
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
  fun h => fresh (sub x h)

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
`AtomicBranch`-level freshness side condition D5's `reorder_assign_guard` pair needs: a preceding
action's assigned name must stay fresh in every later guard for the substitution `𝒞_reord`
performs to be sound. -/
def GuardedPlusCal.AtomicBranch.FreshIn (x : String) (Br : ComputableGuardedPlusCal.AtomicBranch) :
    Prop :=
  x ∉ ((match Br.precondition with | none => ∅ | some B => B.freeVars) ∪ Br.action.freeVars)

end
