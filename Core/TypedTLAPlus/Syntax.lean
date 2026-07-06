import Common.Position
import Core.SurfaceTLAPlus.Syntax
import Mathlib.Control.Bifunctor
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Traversable.Instances
import Mathlib.Control.Bitraversable.Basic
import Mathlib.Control.Bitraversable.Instances
import Extra.Prod

/-!
  The output of the type checker — `CoreTLAPlus.Expression`/`Declaration`/`Module`, every binder's
  annotation now a required `Typ` rather than an optional user-written one, plus two new
  constructors with no `CoreTLAPlus` counterpart: `mvar` (a pending-coercion placeholder, resolved
  before the checker's own output is ever handed to a caller) and `seq` (the checking-mode
  sequence-constructor rule, kept distinct from `tuple`'s synthesis rule).

  Most nodes don't carry a redundant "own type" field — it's recoverable from context — except
  where checking would otherwise need to re-synthesize it: `var` (the `Γ`-lookup result);
  `set`/`seq`'s element type (the empty-literal case has no element to derive a type from);
  `tuple`'s per-component types (each component can be an arbitrary expression, not a cheap
  pattern-match); `record`/`recordSet`'s per-field types (already present in
  `CoreTLAPlus.Expression`'s own shape).
-/

namespace TypedTLAPlus

/-- The type grammar, reusing `SurfaceTLAPlus.Typ` rather than defining a second copy: the
checker's job is to populate every binder with a real value of this type, not invent a new one. -/
abbrev Typ := SurfaceTLAPlus.Typ

/-- The type used to identify a not-yet-resolved metavariable `?n`. -/
abbrev MVarId := Nat

/--
  TLA⁺ expressions after type checking. `α` is always instantiated at `Typ` by the checker's
  actual output — kept generic to match `CoreTLAPlus.Expression`'s own shape. Identical to
  `CoreTLAPlus.Expression` node-for-node except: `var` gains a trailing type (the `Γ`-lookup
  result); `mvar`/`seq` are new.
-/
inductive Expression (α : Type) : Type
  /-- An unqualified identifier, now with its type resolved via `Γ`. -/
  | var : String → α → Expression α
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
  /-- The image of a function by a set `{e : x ∈ A}`. -/
  | map' : Expression α → String → α → Expression α → Expression α
  /-- A function call `f[e]` — always unary. -/
  | fnCall : Expression α → Expression α → Expression α
  /-- A function literal `[x ∈ A ↦ e]`. -/
  | fn : String → α → Expression α → Expression α → Expression α
  /-- The set of all functions from a domain to a codomain, `[A -> B]`. -/
  | fnSet : Expression α → Expression α → Expression α
  /-- A literal record `[a |-> e₁, …, z |-> eₙ]`, each field's own `α` its (ascribed or inferred)
  type. -/
  | record : List (α × String × Expression α) → Expression α
  /-- The set of all records whose fields are in the given sets, `[a : A, …, z : Z]`. -/
  | recordSet : List (α × String × Expression α) → Expression α
  /-- Function update `[f EXCEPT ![e] = e₂]` — each path step's index is unary, same as
  `fnCall`. -/
  | except : Expression α → List (List (String ⊕ Expression α) × Expression α) → Expression α
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
  /-- Conditional `IF e₁ THEN e₂ ELSE e₃`. -/
  | «if» : Expression α → Expression α → Expression α → Expression α
  /-- Case distinction `CASE p₁ -> e₁ [] … [] OTHER -> eₙ₊₁`. -/
  | case : List (Expression α × Expression α) → Option (Expression α) → Expression α
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
  | .var v τ, pos => .var v (f τ) @@ pos
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
  | .map' e x ann dom, pos => .map' (Expression.map f e) x (f ann) (Expression.map f dom) @@ pos
  | .fnCall e e', pos => .fnCall (Expression.map f e) (Expression.map f e') @@ pos
  | .fn x ann dom e, pos => .fn x (f ann) (Expression.map f dom) (Expression.map f e) @@ pos
  | .fnSet e₁ e₂, pos => .fnSet (Expression.map f e₁) (Expression.map f e₂) @@ pos
  | .record fs, pos => .record (Prod.map₃ f id (Expression.map f) <$> fs) @@ pos
  | .recordSet fs, pos => .recordSet (Prod.map₃ f id (Expression.map f) <$> fs) @@ pos
  | .except e upds, pos =>
    .except (Expression.map f e)
      (Bifunctor.bimap (·.map (Sum.map id (Expression.map f))) (Expression.map f) <$> upds) @@ pos
  | .recordAccess e v, pos => .recordAccess (Expression.map f e) v @@ pos
  | .tuple es, pos => .tuple (Bifunctor.bimap f (Expression.map f) <$> es) @@ pos
  | .seq es τ, pos => .seq (Expression.map f <$> es) (f τ) @@ pos
  | .if e₁ e₂ e₃, pos => .if (Expression.map f e₁) (Expression.map f e₂) (Expression.map f e₃) @@ pos
  | .case es e, pos => .case (Bifunctor.bimap (Expression.map f) (Expression.map f) <$> es) (Expression.map f <$> e) @@ pos
  | .stutter e₁ e₂, pos => .stutter (Expression.map f e₁) (Expression.map f e₂) @@ pos
  | .mvar n e, pos => .mvar n (Expression.map f e) @@ pos

instance : Functor Expression where
  map := Expression.map

local instance {F : Type → Type} [Applicative F] {α} : Inhabited (F (Expression α)) := ⟨pure .true⟩ in
protected partial def Expression.traverse {F : Type → Type} [Applicative F] {α β} (f : α → F β) (e : Expression α) : F (Expression β) := match_source e with
  | .var v τ, pos => (.var v · @@ pos) <$> f τ
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
  | .map' e x ann dom, pos =>
    (.map' · x · · @@ pos) <$> Expression.traverse f e <*> f ann <*> Expression.traverse f dom
  | .fnCall e e', pos => (.fnCall · · @@ pos) <$> Expression.traverse f e <*> Expression.traverse f e'
  | .fn x ann dom e, pos =>
    (.fn x · · · @@ pos) <$> f ann <*> Expression.traverse f dom <*> Expression.traverse f e
  | .fnSet e₁ e₂, pos => (.fnSet · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
  | .record fs, pos => (.record · @@ pos) <$> traverse (Prod.traverse₃ f pure (Expression.traverse f)) fs
  | .recordSet fs, pos => (.recordSet · @@ pos) <$> traverse (Prod.traverse₃ f pure (Expression.traverse f)) fs
  | .except e upds, pos =>
    (.except · · @@ pos) <$> Expression.traverse f e
      <*> traverse (bitraverse (traverse (bitraverse pure (Expression.traverse f))) (Expression.traverse f)) upds
  | .recordAccess e v, pos => (.recordAccess · v @@ pos) <$> Expression.traverse f e
  | .tuple es, pos => (.tuple · @@ pos) <$> traverse (bitraverse f (Expression.traverse f)) es
  | .seq es τ, pos => (.seq · · @@ pos) <$> traverse (Expression.traverse f) es <*> f τ
  | .if e₁ e₂ e₃, pos => (.if · · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂ <*> Expression.traverse f e₃
  | .case es e, pos => (.case · · @@ pos) <$> traverse (bitraverse (Expression.traverse f) (Expression.traverse f)) es <*> traverse (Expression.traverse f) e
  | .stutter e₁ e₂, pos => (.stutter · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
  | .mvar n e, pos => (.mvar n · @@ pos) <$> Expression.traverse f e

instance : Traversable Expression where
  traverse := Expression.traverse

/-- A top-level, type-checked TLA⁺ declaration. `RECURSIVE` and module `INSTANCE` are out of
scope. -/
inductive Declaration (α : Type) : Type
  | constants : List (String × α) → Declaration α
  | «variables» : List (String × α) → Declaration α
  | assume : Expression α → Declaration α
  /-- An operator definition, optionally with higher-order arguments (each parameter's `Nat` is
  its own arity, `0` for `x`, `3` for `F(_, _, _)`, …). -/
  | operator : α → String → List (String × Nat) → Expression α → Declaration α
  /-- A function definition, with an explicit domain for every argument. -/
  | function : α → String → List (String × Expression α) → Expression α → Declaration α
  deriving Repr

instance : Functor Declaration where
  map f
    | .constants xs => .constants (Bifunctor.snd f <$> xs)
    | .variables xs => .variables (Bifunctor.snd f <$> xs)
    | .assume e => .assume (f <$> e)
    | .operator a x args e => .operator (f a) x args (f <$> e)
    | .function a x args e => .function (f a) x (Bifunctor.snd (f <$> ·) <$> args) (f <$> e)

instance : Traversable Declaration where
  traverse f
    | .constants xs => .constants <$> traverse (bitraverse pure f) xs
    | .variables xs => .variables <$> traverse (bitraverse pure f) xs
    | .assume e => .assume <$> traverse f e
    | .operator a x args e => (.operator · x args ·) <$> f a <*> traverse f e
    | .function a x args e => (.function · x · ·) <$> f a <*> traverse (bitraverse pure (traverse f)) args <*> traverse f e

/--
  A type-checked TLA⁺ module, wrapping the (separately checked) typed PlusCal algorithm at
  whatever `α` the caller instantiates it at — kept abstract to avoid a cyclic import.
-/
structure Module (α β : Type) : Type where
  name : String
  «extends» : List String
  declarations₁ : List (Declaration β)
  pcalAlgorithm : Option α
  declarations₂ : List (Declaration β)
  deriving Repr, Inhabited

instance : Bifunctor Module where
  bimap f g m := { m with
    declarations₁ := (g <$> ·) <$> m.declarations₁
    pcalAlgorithm := f <$> m.pcalAlgorithm
    declarations₂ := (g <$> ·) <$> m.declarations₂
  }

instance : Bitraversable Module where
  bitraverse f g m :=
    ({m with declarations₁ := ·, pcalAlgorithm := ·, declarations₂ := ·})
      <$> traverse (traverse g) m.declarations₁
      <*> traverse f m.pcalAlgorithm
      <*> traverse (traverse g) m.declarations₂

end TypedTLAPlus
