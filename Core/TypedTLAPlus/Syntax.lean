module

public import Common.Position
public import Core.Declaration
public import Core.SurfaceTLAPlus.Syntax
public import Mathlib.Control.Bifunctor
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Control.Traversable.Instances
public import Mathlib.Control.Bitraversable.Basic
public import Mathlib.Control.Bitraversable.Instances
public import Extra.Prod

@[expose] public section


/-!
  The output of the type checker — `CoreTLAPlus.Expression`/`Declaration`/`Module`, every binder's
  annotation now a required `Typ` rather than optional, plus two new constructors with no
  `CoreTLAPlus` counterpart: `mvar` (a pending-coercion placeholder, resolved before the checker's
  output is ever handed to a caller) and `seq` (the checking-mode sequence rule, kept distinct
  from `tuple`'s synthesis rule).

  Most nodes don't carry a redundant "own type" field — it's recoverable from context — except
  where checking would otherwise need to re-synthesize it: `var` (the `Γ`-lookup result);
  `set`/`seq`'s element type (an empty literal has no element to derive a type from); `tuple`'s
  per-component types (each component can be an arbitrary expression); `record`/`recordSet`'s
  per-field types (already present in `CoreTLAPlus.Expression`'s shape).
-/

namespace TypedTLAPlus

/-- The type grammar, reusing `SurfaceTLAPlus.Typ` rather than defining a second copy: the
checker's job is to populate every binder with a real value of this type, not invent a new one. -/
abbrev Typ := SurfaceTLAPlus.Typ

/-- The type used to identify a not-yet-resolved metavariable `?n`. -/
abbrev MVarId := Nat

/-- Where a name resolved via `Γ` came from: an ordinary binder; a top-level declaration of some
real or simulated module (`name` — own, imported, or a `builtinModules` entry like `Naturals`/
`Sequences`); or `intrinsic`, for a name with no owning module at all — real TLA⁺'s own core
syntax (`=`, `/\`, `\in`, `\cup`, `DOMAIN`, …), never `EXTENDS`-gated. `intrinsic` is not a fake
module name: an operator that *does* come from a real module (e.g. `Len`/`Sequences`, `..`/
`Naturals`) is tagged `.module "Sequences"`/`.module "Naturals"` instead, even when synthesized by
the compiler itself (`Elaborator/Subtyping.lean`'s coercion machinery). Tagged at `Γ`-construction
time and baked onto `Expression.var` below, so it survives into the checked AST — later passes
(`WellFormedness`, `Network2Go`) read it straight off a `.var` node. Not a third type parameter on
`Expression`: unlike `α`, this doesn't vary by stage. -/
inductive Origin : Type
  | binder
  | intrinsic
  | «module» (name : String)
  deriving Repr, Inhabited, BEq

/--
  TLA⁺ expressions after type checking. `α` is always instantiated at `Typ` by the checker's
  actual output — kept generic to match `CoreTLAPlus.Expression`'s own shape. Identical to
  `CoreTLAPlus.Expression` node-for-node except: `var` gains a trailing type (the `Γ`-lookup
  result) and an `Origin`; `mvar`/`seq` are new.
-/
inductive Expression (α : Type) : Type
  /-- An unqualified identifier, now with its type resolved via `Γ` and its `Origin` recorded. -/
  | var : String → α → Origin → Expression α
  /-- An operator application `f(e₁, …, eₙ)`. -/
  | opCall : Expression α → List (Expression α) → Expression α
  /-- Bounded or unbounded universal quantification. -/
  | «forall» : String → α → Option (Expression α) → Expression α → Expression α
  /-- Bounded or unbounded existential quantification. -/
  | «exists» : String → α → Option (Expression α) → Expression α → Expression α
  /-- Temporal universal quantification `\AA x : P`. -/
  | fforall : String → α → Expression α → Expression α
  /-- Temporal existential quantification. -/
  | eexists : String → α → Expression α → Expression α
  /-- Hilbert's epsilon operator. -/
  | choose : String → α → Option (Expression α) → Expression α → Expression α
  /-- A literal set `{e₁, …, eₙ}`, `α` its element type — kept since an empty `{}` gives nothing
  to reconstruct it from. -/
  | set : List (Expression α) → α → Expression α
  /-- Set filtering `{x ∈ A : P}`. -/
  | collect : String → α → Expression α → Expression α → Expression α
  /-- The image of a function by a set `{e : x ∈ A}`. `ann` is the bound variable's type (`A`'s
  element type), `cod` the type of `e`. Both are recorded because neither recovers the other —
  `{Len(s) : s ∈ setOfSeqs}` has `ann = Seq(τ)` and `cod = Int` — and a backend needs both: Go's
  `SetMap` takes a `func` literal, whose signature must be written out on both sides. -/
  | map' : Expression α → String → (ann : α) → (cod : α) → Expression α → Expression α
  /-- A function call `f[e]` — always unary. The head's type is recorded because `f[e]` is three
  different things depending on it (a function application, a sequence index, a tuple projection)
  and a backend has to tell them apart; re-deriving it means redoing inference. -/
  | fnCall : Expression α → (fnTyp : α) → Expression α → Expression α
  /-- A function literal `[x ∈ A ↦ e]`. `ann`/`cod` as in `map'`. -/
  | fn : String → (ann : α) → (cod : α) → Expression α → Expression α → Expression α
  /-- The set of all functions from a domain to a codomain, `[A -> B]`. -/
  | fnSet : Expression α → Expression α → Expression α
  /-- A literal record `[a |-> e₁, …, z |-> eₙ]`, each field's own `α` its (ascribed or inferred)
  type. -/
  | record : List (α × String × Expression α) → Expression α
  /-- The set of all records whose fields are in the given sets, `[a : A, …, z : Z]`. -/
  | recordSet : List (α × String × Expression α) → Expression α
  /-- Function update `[f EXCEPT ![e] = e₂]` — each path step's index is unary, same as `fnCall`,
  and like `fnCall` the target's type is recorded. `![i]` is one syntax for overloading a function,
  updating a sequence and updating a tuple, which are three different operations; the path walk
  also needs each step's type to compile the step below it. The type of the whole expression is
  this same type — an override changes values, never the shape. -/
  | except : Expression α → (τ : α) → List (List (String ⊕ Expression α) × Expression α) → Expression α
  /-- Record access `r.x`. -/
  | recordAccess : Expression α → String → Expression α
  /-- A literal tuple `<<e₁, …, eₙ>>`, synthesis-mode. Each component pairs its own type with
  itself directly, since a component's type isn't a cheap pattern-match away in general. Kept
  distinct from `seq` below — the same surface syntax, but a different elaboration rule. -/
  | tuple : List (α × Expression α) → Expression α
  /-- A literal sequence `<<e₁, …, eₙ>>`, checking-mode only (fired when checking against an
  expected `Seq(τ)`) — has no `CoreTLAPlus` counterpart. `α` the element type `τ` every `eᵢ` was
  checked against — kept because an empty `<<>>` gives nothing to reconstruct it from. -/
  | seq : List (Expression α) → α → Expression α
  /-- Conditional `IF e₁ THEN e₂ ELSE e₃`, carrying the type of the whole conditional.

  This one is not recoverable from the branches by inspection: in synthesis position the type is
  `lub` over them, and while `lub` can only return one of its arguments
  (`Elaborator/Subtyping.lean`), *which* one is not syntactically apparent — so reading it off, say,
  the `THEN` branch is wrong whenever the join came from the `ELSE`. Both rules
  (`Elaborator/Expressions.lean`) coerce every branch into this type, so it is the type of each
  branch as elaborated, not merely an upper bound on them. -/
  | «if» : Expression α → Expression α → Expression α → (τ : α) → Expression α
  /-- Case distinction `CASE p₁ -> e₁ [] … [] OTHER -> eₙ₊₁`, carrying the type of the whole
  expression — same reasoning as `if`'s, over `lubAll` of every arm. -/
  | case : List (Expression α × Expression α) → Option (Expression α) → (τ : α) → Expression α
  | nat : String → Expression α
  | str : String → Expression α
  | «true» : Expression α
  | «false» : Expression α
  /-- The stuttering-allowed action `[A]_e`. -/
  | stutter : Expression α → Expression α → Expression α
  /-- An expression-level placeholder for a *pending* coercion: wraps an already-elaborated
  expression whose true type still depends on an unresolved metavariable `?n`. Has no
  `CoreTLAPlus` counterpart — every `mvar` node is substituted away before the checker's output
  is ever handed to a caller, so no consumer outside the checker itself should pattern-match on
  it. -/
  | mvar : MVarId → Expression α → Expression α
  deriving Repr, Inhabited, BEq

-- Structural recursion isn't visibly decreasing to Lean here (nested `List`/`Option` occurrences
-- of `Expression`) — `partial` until revisited.
protected partial def Expression.map {α β} (f : α → β) (e : Expression α) : Expression β := match_source e with
  | .var v τ o, pos => .var v (f τ) o @@ pos
  | .nat n, pos => .nat n @@ pos
  | .str s, pos => .str s @@ pos
  | .true, pos => .true @@ pos
  | .false, pos => .false @@ pos
  | .opCall v es, pos => .opCall (Expression.map f v) (Expression.map f <$> es) @@ pos
  | .forall x ann dom e, pos => .forall x (f ann) (Expression.map f <$> dom) (Expression.map f e) @@ pos
  | .exists x ann dom e, pos => .exists x (f ann) (Expression.map f <$> dom) (Expression.map f e) @@ pos
  | .fforall x ann e, pos => .fforall x (f ann) (Expression.map f e) @@ pos
  | .eexists x ann e, pos => .eexists x (f ann) (Expression.map f e) @@ pos
  | .choose x ann dom e, pos => .choose x (f ann) (Expression.map f <$> dom) (Expression.map f e) @@ pos
  | .set es τ, pos => .set (Expression.map f <$> es) (f τ) @@ pos
  | .collect x ann dom e, pos => .collect x (f ann) (Expression.map f dom) (Expression.map f e) @@ pos
  | .map' e x ann cod dom, pos =>
    .map' (Expression.map f e) x (f ann) (f cod) (Expression.map f dom) @@ pos
  | .fnCall e fnTyp e', pos =>
    .fnCall (Expression.map f e) (f fnTyp) (Expression.map f e') @@ pos
  | .fn x ann cod dom e, pos =>
    .fn x (f ann) (f cod) (Expression.map f dom) (Expression.map f e) @@ pos
  | .fnSet e₁ e₂, pos => .fnSet (Expression.map f e₁) (Expression.map f e₂) @@ pos
  | .record fs, pos => .record (Prod.map₃ f id (Expression.map f) <$> fs) @@ pos
  | .recordSet fs, pos => .recordSet (Prod.map₃ f id (Expression.map f) <$> fs) @@ pos
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
  | .stutter e₁ e₂, pos => .stutter (Expression.map f e₁) (Expression.map f e₂) @@ pos
  | .mvar n e, pos => .mvar n (Expression.map f e) @@ pos

instance : Functor Expression where
  map := Expression.map

local instance {F : Type → Type} [Applicative F] {α} : Inhabited (F (Expression α)) := ⟨pure .true⟩ in
protected partial def Expression.traverse {F : Type → Type} [Applicative F] {α β} (f : α → F β) (e : Expression α) : F (Expression β) := match_source e with
  | .var v τ o, pos => (.var v · o @@ pos) <$> f τ
  | .nat n, pos => pure <| .nat n @@ pos
  | .str s, pos => pure <| .str s @@ pos
  | .true, pos => pure <| .true @@ pos
  | .false, pos => pure <| .false @@ pos
  | .opCall e es, pos => (.opCall · · @@ pos) <$> Expression.traverse f e <*> traverse (Expression.traverse f) es
  | .forall x ann dom e, pos =>
    (.forall x · · · @@ pos) <$> f ann <*> traverse (Expression.traverse f) dom <*> Expression.traverse f e
  | .exists x ann dom e, pos =>
    (.exists x · · · @@ pos) <$> f ann <*> traverse (Expression.traverse f) dom <*> Expression.traverse f e
  | .fforall x ann e, pos => (.fforall x · · @@ pos) <$> f ann <*> Expression.traverse f e
  | .eexists x ann e, pos => (.eexists x · · @@ pos) <$> f ann <*> Expression.traverse f e
  | .choose x ann dom e, pos =>
    (.choose x · · · @@ pos) <$> f ann <*> traverse (Expression.traverse f) dom <*> Expression.traverse f e
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
  | .fnSet e₁ e₂, pos => (.fnSet · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
  | .record fs, pos => (.record · @@ pos) <$> traverse (Prod.traverse₃ f pure (Expression.traverse f)) fs
  | .recordSet fs, pos => (.recordSet · @@ pos) <$> traverse (Prod.traverse₃ f pure (Expression.traverse f)) fs
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
  | .stutter e₁ e₂, pos => (.stutter · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
  | .mvar n e, pos => (.mvar n · @@ pos) <$> Expression.traverse f e

instance : Traversable Expression where
  traverse := Expression.traverse

/-- A top-level, type-checked TLA⁺ declaration. `RECURSIVE` and module `INSTANCE` are out of
scope. -/
abbrev Declaration := _root_.Declaration Expression

/--
  A type-checked TLA⁺ module, wrapping the (separately checked) typed PlusCal algorithm at
  whatever `α` the caller instantiates it at — kept abstract to avoid a cyclic import.
-/
abbrev Module := _root_.Module Expression

namespace Module
export _root_.Module (mk)
end Module

end TypedTLAPlus

end
