module

public import Common.Position
public import Core.Declaration
public import Core.TypedTLAPlus.Syntax
public import Mathlib.Control.Bifunctor
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Control.Traversable.Instances
public import Mathlib.Control.Bitraversable.Basic
public import Mathlib.Control.Bitraversable.Instances
public import Extra.Prod

@[expose] public section


/-!
  The output of `Typed2Computable` — `TypedTLAPlus.Expression` restricted to what a backend can
  actually compute. Structurally identical to `TypedTLAPlus.Expression` node-for-node except:

  - No `fnSet` (`[A -> B]`, the set of *all* functions `A → B`) or `recordSet` (`[a : A, ...]`,
    the set of *all* records shaped that way) — both denote sets with no finite representation in
    general, so no backend can compute them. `Typed2Computable` rejects any algorithm still
    referencing one of these (`ComputableError.notComputable`) rather than silently translating
    them into something wrong.
  - No `fforall`/`eexists` (`\AA`/`\EE`, temporal quantification) or `stutter` (`[A]_e`) — already
    banned from anything reachable from the algorithm by `WellFormedness/Restrictions.lean`'s
    check 3, so absent by construction from `Typed2Computable`'s input; kept out of this AST
    entirely rather than carried forward as dead constructors no producer ever emits.
  - No `mvar` — every metavariable is already resolved by the time the type checker's output is
    handed to any caller (`TypedTLAPlus.Syntax.lean`'s doc comment), so `Typed2Computable`'s input
    never contains one either.
  - `forall`/`exists`/`choose`'s domain is a required `Expression α`, not `Option (Expression
    α)` — `WellFormedness/Restrictions.lean`'s check 3 already bans an unbounded quantifier
    (`dom = none`) from anything reachable from the algorithm, so every surviving domain is `some`
    by the time `Typed2Computable` runs; tightening the field makes that invariant checked by the
    type system instead of by convention.
-/

namespace ComputableTLAPlus

/-- Reuses `TypedTLAPlus.Typ` (itself `SurfaceTLAPlus.Typ`) rather than defining a third copy —
`Typed2Computable`'s job is to restrict which `Expression` *shapes* survive, not to invent a new
type grammar. -/
abbrev Typ := TypedTLAPlus.Typ

/-- Reuses `TypedTLAPlus.Origin` — a `.var`'s provenance doesn't change across `Typed2Computable`,
only which expressions are allowed to exist at all. -/
abbrev Origin := TypedTLAPlus.Origin

/--
  Computable TLA⁺ expressions — see the module doc above for how this differs from
  `TypedTLAPlus.Expression`. `α` is always instantiated at `Typ` by `Typed2Computable`'s output —
  kept generic to match `TypedTLAPlus.Expression`'s shape.
-/
inductive Expression (α : Type) : Type
  /-- An identifier: its type resolved via `Γ` and its `Origin` recording where the name binds. A
  `.bound` node carries no name — the string hint lives on the enclosing binder. -/
  | var : α → Origin → Expression α
  /-- An operator application `f(e₁, …, eₙ)`. -/
  | opCall : Expression α → List (Expression α) → Expression α
  /-- Bounded universal quantification. -/
  | «forall» : String → α → Expression α → Expression α → Expression α
  /-- Bounded existential quantification. -/
  | «exists» : String → α → Expression α → Expression α → Expression α
  /-- Hilbert's epsilon operator, bounded. -/
  | choose : String → α → Expression α → Expression α → Expression α
  /-- A literal set `{e₁, …, eₙ}`, `α` its element type — kept since an empty `{}` gives nothing
  to reconstruct it from. -/
  | set : List (Expression α) → α → Expression α
  /-- Set filtering `{x ∈ A : P}`. -/
  | collect : String → α → Expression α → Expression α → Expression α
  /-- The image of a function by a set `{e : x ∈ A}`. `ann`/`cod` as in
  `TypedTLAPlus.Expression.map'`. -/
  | map' : Expression α → String → (ann : α) → (cod : α) → Expression α → Expression α
  /-- A function call `f[e]` — always unary, carrying its head's type so that a backend can tell a
  function application from a sequence index from a tuple projection. -/
  | fnCall : Expression α → (fnTyp : α) → Expression α → Expression α
  /-- A function literal `[x ∈ A ↦ e]`. `ann`/`cod` as in `map'`. -/
  | fn : String → (ann : α) → (cod : α) → Expression α → Expression α → Expression α
  /-- A literal record `[a |-> e₁, …, z |-> eₙ]`, each field's own `α` its (ascribed or inferred)
  type. -/
  | record : List (α × String × Expression α) → Expression α
  /-- Function update `[f EXCEPT ![e] = e₂]`, carrying the target's type — see
  `TypedTLAPlus.Expression.except`. -/
  | except : Expression α → (τ : α) → List (List (String ⊕ Expression α) × Expression α) → Expression α
  /-- Record access `r.x`. -/
  | recordAccess : Expression α → String → Expression α
  /-- A literal tuple `<<e₁, …, eₙ>>`, synthesis-mode. Each component pairs its own type with
  itself directly, since a component's type isn't a cheap pattern-match away in general. Kept
  distinct from `seq` below — the same surface syntax, but a different elaboration rule. -/
  | tuple : List (α × Expression α) → Expression α
  /-- A literal sequence `<<e₁, …, eₙ>>`, checking-mode only. `α` the element type `τ` every `eᵢ`
  was checked against — kept because an empty `<<>>` gives nothing to reconstruct it from. -/
  | seq : List (Expression α) → α → Expression α
  /-- Conditional `IF e₁ THEN e₂ ELSE e₃`, carrying its own type — see
  `TypedTLAPlus.Expression.if` for why no branch answers for it. -/
  | «if» : Expression α → Expression α → Expression α → (τ : α) → Expression α
  /-- Case distinction `CASE p₁ -> e₁ [] … [] OTHER -> eₙ₊₁`, carrying its own type. -/
  | case : List (Expression α × Expression α) → Option (Expression α) → (τ : α) → Expression α
  | nat : String → Expression α
  | str : String → Expression α
  | «true» : Expression α
  | «false» : Expression α
  deriving Repr, Inhabited, BEq

-- `partial`: the recursion is structural, but not visibly decreasing to Lean (nested
-- `List`/`Option` occurrences of `Expression`).
protected partial def Expression.map {α β} (f : α → β) (e : Expression α) : Expression β := match_source e with
  | .var τ o, pos => .var (f τ) o @@ pos
  | .nat n, pos => .nat n @@ pos
  | .str s, pos => .str s @@ pos
  | .true, pos => .true @@ pos
  | .false, pos => .false @@ pos
  | .opCall v es, pos => .opCall (Expression.map f v) (Expression.map f <$> es) @@ pos
  | .forall x ann dom e, pos => .forall x (f ann) (Expression.map f dom) (Expression.map f e) @@ pos
  | .exists x ann dom e, pos => .exists x (f ann) (Expression.map f dom) (Expression.map f e) @@ pos
  | .choose x ann dom e, pos => .choose x (f ann) (Expression.map f dom) (Expression.map f e) @@ pos
  | .set es τ, pos => .set (Expression.map f <$> es) (f τ) @@ pos
  | .collect x ann dom e, pos => .collect x (f ann) (Expression.map f dom) (Expression.map f e) @@ pos
  | .map' e x ann cod dom, pos =>
    .map' (Expression.map f e) x (f ann) (f cod) (Expression.map f dom) @@ pos
  | .fnCall e fnTyp e', pos =>
    .fnCall (Expression.map f e) (f fnTyp) (Expression.map f e') @@ pos
  | .fn x ann cod dom e, pos =>
    .fn x (f ann) (f cod) (Expression.map f dom) (Expression.map f e) @@ pos
  | .record fs, pos => .record (Prod.map₃ f id (Expression.map f) <$> fs) @@ pos
  | .except e τ upds, pos =>
    .except (Expression.map f e) (f τ)
      (Bifunctor.bimap (·.map (Sum.map id (Expression.map f))) (Expression.map f) <$> upds) @@ pos
  | .recordAccess e v, pos => .recordAccess (Expression.map f e) v @@ pos
  | .tuple es, pos => .tuple (Bifunctor.bimap f (Expression.map f) <$> es) @@ pos
  | .seq es τ, pos => .seq (Expression.map f <$> es) (f τ) @@ pos
  | .if e₁ e₂ e₃ τ, pos =>
    .if (Expression.map f e₁) (Expression.map f e₂) (Expression.map f e₃) (f τ) @@ pos
  | .case es e τ, pos =>
    .case (Bifunctor.bimap (Expression.map f) (Expression.map f) <$> es) (Expression.map f <$> e) (f τ) @@ pos

instance : Functor Expression where
  map := Expression.map

local instance {F : Type → Type} [Applicative F] {α} : Inhabited (F (Expression α)) := ⟨pure .true⟩ in
protected partial def Expression.traverse {F : Type → Type} [Applicative F] {α β} (f : α → F β) (e : Expression α) : F (Expression β) := match_source e with
  | .var τ o, pos => (.var · o @@ pos) <$> f τ
  | .nat n, pos => pure <| .nat n @@ pos
  | .str s, pos => pure <| .str s @@ pos
  | .true, pos => pure <| .true @@ pos
  | .false, pos => pure <| .false @@ pos
  | .opCall e es, pos => (.opCall · · @@ pos) <$> Expression.traverse f e <*> traverse (Expression.traverse f) es
  | .forall x ann dom e, pos =>
    (.forall x · · · @@ pos) <$> f ann <*> Expression.traverse f dom <*> Expression.traverse f e
  | .exists x ann dom e, pos =>
    (.exists x · · · @@ pos) <$> f ann <*> Expression.traverse f dom <*> Expression.traverse f e
  | .choose x ann dom e, pos =>
    (.choose x · · · @@ pos) <$> f ann <*> Expression.traverse f dom <*> Expression.traverse f e
  | .set es τ, pos => (.set · · @@ pos) <$> traverse (Expression.traverse f) es <*> f τ
  | .collect x ann dom e, pos =>
    (.collect x · · · @@ pos) <$> f ann <*> Expression.traverse f dom <*> Expression.traverse f e
  | .map' e x ann cod dom, pos =>
    (.map' · x · · · @@ pos)
      <$> Expression.traverse f e <*> f ann <*> f cod <*> Expression.traverse f dom
  | .fnCall e fnTyp e', pos =>
    (.fnCall · · · @@ pos) <$> Expression.traverse f e <*> f fnTyp <*> Expression.traverse f e'
  | .fn x ann cod dom e, pos =>
    (.fn x · · · · @@ pos)
      <$> f ann <*> f cod <*> Expression.traverse f dom <*> Expression.traverse f e
  | .record fs, pos => (.record · @@ pos) <$> traverse (Prod.traverse₃ f pure (Expression.traverse f)) fs
  | .except e τ upds, pos =>
    (.except · · · @@ pos) <$> Expression.traverse f e <*> f τ
      <*> traverse (bitraverse (traverse (bitraverse pure (Expression.traverse f))) (Expression.traverse f)) upds
  | .recordAccess e v, pos => (.recordAccess · v @@ pos) <$> Expression.traverse f e
  | .tuple es, pos => (.tuple · @@ pos) <$> traverse (bitraverse f (Expression.traverse f)) es
  | .seq es τ, pos => (.seq · · @@ pos) <$> traverse (Expression.traverse f) es <*> f τ
  | .if e₁ e₂ e₃ τ, pos =>
    (.if · · · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
      <*> Expression.traverse f e₃ <*> f τ
  | .case es e τ, pos =>
    (.case · · · @@ pos) <$> traverse (bitraverse (Expression.traverse f) (Expression.traverse f)) es
      <*> traverse (Expression.traverse f) e <*> f τ

instance : Traversable Expression where
  traverse := Expression.traverse

/-- A top-level, computable TLA⁺ declaration. -/
abbrev Declaration := _root_.Declaration Expression

/--
  A computable TLA⁺ module, wrapping the (separately translated) `ComputablePlusCal` algorithm at
  whatever `α` the caller instantiates it at — kept abstract to avoid a cyclic import, same as
  `TypedTLAPlus.Module`.
-/
abbrev Module := _root_.Module Expression

namespace Module
export _root_.Module (mk)
end Module

end ComputableTLAPlus

end
