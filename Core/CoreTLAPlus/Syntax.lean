import Common.Position
import Mathlib.Control.Bifunctor
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Traversable.Instances
import Mathlib.Control.Bitraversable.Basic
import Mathlib.Control.Bitraversable.Instances
import Extra.Prod

/-!
  The desugared core syntax of TLA⁺ expressions — the output of desugaring, and the language the
  type checker and everything downstream actually works against.

  Relative to `SurfaceTLAPlus.Expression`:
  - `@` is eliminated entirely (substituted away during desugaring).
  - Conjunction/disjunction lists become binary `infixCall`s (`.conj`/`.disj` don't exist here).
  - Every prefix/infix/postfix operator application becomes an ordinary (prefix-style) `opCall`,
    with the operator referenced by its canonical spelling through the same `var` constructor
    used for ordinary identifiers — no separate operator-enum or value constructors.
  - Every quantifier-like binder (`\A`/`\E`/`\AA`/`\EE`/`CHOOSE`/set-map/set-filter/function
    literals) binds exactly one variable over at most one domain; multi-variable and
    tuple-pattern binders are surface sugar eliminated before reaching this type.
-/

namespace CoreTLAPlus

/--
  TLA⁺ expressions after desugaring. `α` carries whatever comment-annotation payload the binders
  (quantifiers, `LET` in the future, record fields, …) need.
-/
inductive Expression (α : Type) : Type
  /-- An unqualified identifier: a variable, a user-defined 0-ary operator, or (by canonical
  spelling, e.g. `"+"`, `"\\in"`, `"DOMAIN"`) a builtin operator referenced as a value. -/
  | var : String → Expression α
  /-- An operator application `f(e₁, …, eₙ)` — the only form of application here, used uniformly
  for user-defined operators and (applying a builtin `var`) builtins alike. -/
  | opCall : Expression α → List (Expression α) → Expression α
  /-- Bounded (`\A x ∈ A : P`, `domain = some A`) or unbounded (`\A x : P`, `domain = none`, the
  annotation `α` on `x` carrying the required explicit type) universal quantification. -/
  | «forall» : String → α → Option (Expression α) → Expression α → Expression α
  /-- Bounded or unbounded existential quantification, dual to `forall`. -/
  | «exists» : String → α → Option (Expression α) → Expression α → Expression α
  /-- Temporal universal quantification `\AA x : P` — always unbounded. -/
  | fforall : String → α → Expression α → Expression α
  /-- Temporal existential quantification, dual to `fforall`. -/
  | eexists : String → α → Expression α → Expression α
  /-- Hilbert's epsilon operator: bounded (`CHOOSE x ∈ A : P`) or unbounded (`CHOOSE x : P`,
  checked against the expected type rather than annotated). -/
  | choose : String → α → Option (Expression α) → Expression α → Expression α
  /-- A literal set `{e₁, …, eₙ}`. -/
  | set : List (Expression α) → Expression α
  /-- Set filtering `{x ∈ A : P}`. -/
  | collect : String → α → Expression α → Expression α → Expression α
  /-- The image of a function by a set `{e : x ∈ A}`. -/
  | map' : Expression α → String → α → Expression α → Expression α
  /-- A function call `f[e]` — always unary; a surface multi-index call `f[e₁, …, eₙ]` (`n > 1`)
  desugars to `f[<<e₁, …, eₙ>>]`. -/
  | fnCall : Expression α → Expression α → Expression α
  /-- A function literal `[x ∈ A ↦ e]`. -/
  | fn : String → α → Expression α → Expression α → Expression α
  /-- The set of all functions from a domain to a codomain, `[A -> B]`. -/
  | fnSet : Expression α → Expression α → Expression α
  /-- A literal record `[a |-> e₁, …, z |-> eₙ]`. -/
  | record : List (α × String × Expression α) → Expression α
  /-- The set of all records whose fields are in the given sets, `[a : A, …, z : Z]`. -/
  | recordSet : List (α × String × Expression α) → Expression α
  /-- Function update `[f EXCEPT ![e] = e₂]` — each path step's index (`.inr`) is unary, same as
  `fnCall`. -/
  | except : Expression α → List (List (String ⊕ Expression α) × Expression α) → Expression α
  /-- Record access `r.x`. -/
  | recordAccess : Expression α → String → Expression α
  /-- A literal tuple `<<e₁, …, eₙ>>` — also TLA⁺'s only literal sequence former (`Seq(S)` is an
  ordinary `opCall`, not a literal). -/
  | tuple : List (Expression α) → Expression α
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
  deriving Repr, Inhabited, BEq

-- Structural recursion isn't visibly decreasing to Lean here (nested `List`/`Option` occurrences
-- of `Expression`) — `partial` until revisited.
protected partial def Expression.map {α β} (f : α → β) (e : Expression α) : Expression β := match_source e with
  | .var v, pos => .var v @@ pos
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
  | .set es, pos => .set (Expression.map f <$> es) @@ pos
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
  | .tuple es, pos => .tuple (Expression.map f <$> es) @@ pos
  | .if e₁ e₂ e₃, pos => .if (Expression.map f e₁) (Expression.map f e₂) (Expression.map f e₃) @@ pos
  | .case es e, pos => .case (Bifunctor.bimap (Expression.map f) (Expression.map f) <$> es) (Expression.map f <$> e) @@ pos
  | .stutter e₁ e₂, pos => .stutter (Expression.map f e₁) (Expression.map f e₂) @@ pos

instance : Functor Expression where
  map := Expression.map

local instance {F : Type → Type} [Applicative F] {α} : Inhabited (F (Expression α)) := ⟨pure .true⟩ in
protected partial def Expression.traverse {F : Type → Type} [Applicative F] {α β} (f : α → F β) (e : Expression α) : F (Expression β) := match_source e with
  | .var v, pos => pure <| .var v @@ pos
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
  | .set es, pos => (.set · @@ pos) <$> traverse (Expression.traverse f) es
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
  | .tuple es, pos => (.tuple · @@ pos) <$> traverse (Expression.traverse f) es
  | .if e₁ e₂ e₃, pos => (.if · · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂ <*> Expression.traverse f e₃
  | .case es e, pos => (.case · · @@ pos) <$> traverse (bitraverse (Expression.traverse f) (Expression.traverse f)) es <*> traverse (Expression.traverse f) e
  | .stutter e₁ e₂, pos => (.stutter · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂

instance : Traversable Expression where
  traverse := Expression.traverse

/-- A top-level TLA⁺ declaration. `RECURSIVE` and module `INSTANCE` are not represented. -/
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
  A desugared TLA⁺ module, wrapping the embedded (still-Surface, not-yet-desugared-at-the-
  statement-level) PlusCal algorithm at whatever `α` the caller instantiates it at — kept abstract
  to avoid a cyclic import.
-/
structure Module (α β : Type) : Type where
  name : String
  «extends» : List String
  declarations₁ : List (Declaration β)
  pcalAlgorithm : Option α
  declarations₂ : List (Declaration β)
  deriving Repr

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

end CoreTLAPlus
