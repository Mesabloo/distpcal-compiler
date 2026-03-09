import Common.Position
-- import PlusCalCompiler.SurfaceTLAPlus.Tokens
import Mathlib.Control.Bifunctor
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Traversable.Instances
import Mathlib.Control.Bitraversable.Basic
import Mathlib.Control.Bitraversable.Instances
import Mathlib.Control.Functor
import Mathlib.Logic.Function.Defs
import Extra.Prod
import Core.CoreTLAPlus.Syntax

namespace TypedTLAPlus
  export CoreTLAPlus (QuantifierBound IdentifierOrTuple PrefixOperator InfixOperator PostfixOperator)

  /- TLA+: https://lamport.azurewebsites.net/tla/TLAPlus2Grammar.tla -/
  /- See also page 268 of the book "Specifying Systems". -/

  -- TODO: support qualified identifiers and operators

  /--
    The inductive type describing TLA⁺ expressions as accepted syntactically.

    The `α` parameter is used to make the type of comment annotations generic.
  -/
  inductive Expression (α : Type) : Type
    /-- A TLA+ (unqualified) identifier. -/
    | var : String → α → Expression α
    /-- An operator call `f(e₁, …, eₙ)`. -/
    | opCall : Expression α → List (Expression α) → Expression α
    /-- A prefix operator call. -/
    | prefixCall : PrefixOperator → Expression α → Expression α
    /-- An infix operator call. -/
    | infixCall : Expression α → InfixOperator → Expression α → Expression α
    /-- A postfix operator call. -/
    | postfixCall : Expression α → PostfixOperator → Expression α
    /-- Bounded universal quantification `\A q \in A : e`. -/
    | bforall : List (QuantifierBound α (Expression α)) → Expression α → Expression α
    /-- Bounded existential quantification `\E q \in A : p`. -/
    | bexists : List (QuantifierBound α (Expression α)) → Expression α → Expression α
    /-- Unbounded universal quantification `\A x, y, …, z : p`. -/
    | forall : List String → Expression α → Expression α
    /-- Unbounded existential quantification `\E x, y, …, z : p`. -/
    | exists : List String → Expression α → Expression α
    /-- Temporal universal quantification `\AA x, y, …, z : p`. -/
    | fforall : List String → Expression α → Expression α
    /-- Temporal existential quantification `\EE x, y, …, z : p`. -/
    | eexists : List String → Expression α → Expression α
    /-- Hilbert's epsilon operator `CHOOSE x \in A : p`. -/
    | choose : IdentifierOrTuple String → Option (Expression α) → Expression α → Expression α
    /-- A literal set `{e₁, …, eₙ} : 𝒫(τ)`. -/
    | set : List (Expression α) → α → Expression α
    /-- Set collection/filtering `{x \in A : p}`. -/
    | collect : IdentifierOrTuple String → Expression α → Expression α → Expression α
    /-- The image of a function by a set `{e : x \in A}`. -/
    | map' : Expression α → List (QuantifierBound α (Expression α)) → Expression α
    /-- A function call `f[e₁, …, eₙ]`. -/
    | fnCall : Expression α → List (Expression α) → Expression α
    /-- A function literal `[x \in A, …, z \in B ↦ e]`. -/
    | fn : List (QuantifierBound α (Expression α)) → Expression α → Expression α
    /-- The set of all functions from a given domain to a given codomain `[A -> B]`. -/
    | fnSet : Expression α → Expression α → Expression α
    /-- The literal record `[x₁ : τ₁ |-> e₁, …, xₙ : τₙ |-> eₙ]`, with types ascribed to the fields. -/
    | record : List (α × String × Expression α) → Expression α
    /-- The set of all records whose fields are in the given sets `[a : A, …, z : Z]`. -/
    | recordSet : List (α × String × Expression α) → Expression α
    /-- Function update `[f EXCEPT ![e₁] = e₂]`. -/
    | except : Expression α → List (List (String ⊕ List (Expression α)) × Expression α) → Expression α
    /-- Record access `r.x`. -/
    | recordAccess : Expression α → String → Expression α
    /-- A literal tuple `<<e₁, …, eₙ>> : τ₁ × … × τₙ`. -/
    | tuple : List (Expression α × α) → Expression α
    /-- Sequence literal `Seq(<<e₁, …, eₙ>>) : Seq(τ)`. -/
    | seq : List (Expression α) → α → Expression α
    /-- Conditional expression `IF e₁ THEN e₂ ELSE e₃`. -/
    | if : Expression α → Expression α → Expression α → Expression α
    /-- Case distinction `CASE p₁ -> e₁ [] … [] OTHER -> eₙ₊₁`. -/
    | case : List (Expression α × Expression α) → Option (Expression α) → Expression α
    -- TODO: to be able to define `LET`, we need to make `Expression` mutual with `Declaration`…
    /-- A natural number. -/
    | nat : String → Expression α
    /-- A literal string. -/
    | str : String → Expression α
    /-- `TRUE` -/
    | true : Expression α
    /-- `FALSE` -/
    | false : Expression α
    /-- `[A]_e` -/
    | stutter : Expression α → Expression α → Expression α
    -- WF_ / SF_
    -- TODO: other temporal and action operators
    -- TODO: module instances
    deriving Repr, Inhabited, BEq

  -- TODO: prove termination, at some point
  protected partial def Expression.map {α β} (f : α → β) (e : Expression α) : Expression β := match_source e with
    | .var v τ, pos => .var v (f τ) @@ pos
    | .nat n, pos => .nat n @@ pos
    | .str s, pos => .str s @@ pos
    | .true, pos => .true @@ pos
    | .false, pos => .false @@ pos
    | .opCall v es, pos => .opCall (Expression.map f v) (Expression.map f <$> es) @@ pos
    | .prefixCall op e, pos => .prefixCall op (Expression.map f e) @@ pos
    | .infixCall e₁ op e₂, pos => .infixCall (Expression.map f e₁) op (Expression.map f e₂) @@ pos
    | .postfixCall e op, pos => .postfixCall (Expression.map f e) op @@ pos
    | .bforall qs e, pos => .bforall (bimap f (Expression.map f) <$> qs) (Expression.map f e) @@ pos
    | .bexists qs e, pos => .bexists (bimap f (Expression.map f) <$> qs) (Expression.map f e) @@ pos
    | .forall vs e, pos => .forall vs (Expression.map f e) @@ pos
    | .exists vs e, pos => .exists vs (Expression.map f e) @@ pos
    | .fforall vs e, pos => .fforall vs (Expression.map f e) @@ pos
    | .eexists vs e, pos => .eexists vs (Expression.map f e) @@ pos
    | .choose vs e₁ e₂, pos => .choose vs (Expression.map f <$> e₁) (Expression.map f e₂) @@ pos
    | .set es τ, pos => .set (Expression.map f <$> es) (f τ) @@ pos
    | .collect vs e₁ e₂, pos => .collect vs (Expression.map f e₁) (Expression.map f e₂) @@ pos
    | .map' e qs, pos => .map' (Expression.map f e) (bimap f (Expression.map f) <$> qs) @@ pos
    | .fnCall e es, pos => .fnCall (Expression.map f e) (Expression.map f <$> es) @@ pos
    | .fn qs e, pos => .fn (bimap f (Expression.map f) <$> qs) (Expression.map f e) @@ pos
    | .fnSet e₁ e₂, pos => .fnSet (Expression.map f e₁) (Expression.map f e₂) @@ pos
    | .record fs, pos => .record (Prod.map₃ f id (Expression.map f) <$> fs) @@ pos
    | .recordSet fs, pos => .recordSet (Prod.map₃ f id (Expression.map f) <$> fs) @@ pos
    | .except e upds, pos => .except (Expression.map f e) (bimap (Bifunctor.snd (Expression.map f <$> ·) <$> ·) (Expression.map f) <$> upds) @@ pos
    | .recordAccess e v, pos => .recordAccess (Expression.map f e) v @@ pos
    | .tuple es, pos => .tuple (bimap (Expression.map f) f <$> es) @@ pos
    | .seq es τ, pos => .seq (Expression.map f <$> es) (f τ) @@ pos
    | .if e₁ e₂ e₃, pos => .if (Expression.map f e₁) (Expression.map f e₂) (Expression.map f e₃) @@ pos
    | .case es e, pos => .case (bimap (Expression.map f) (Expression.map f) <$> es) (Expression.map f <$> e) @@ pos
    | .stutter e₁ e₂, pos => .stutter (Expression.map f e₁) (Expression.map f e₂) @@ pos

  instance : Functor Expression where
    map := Expression.map

  local instance {F : Type _ → Type _} [Applicative F] {α} [Inhabited α] : Inhabited (F α) := ⟨pure default⟩ in
  -- TODO: prove termination at some point
  protected partial def Expression.traverse {F : Type _ → Type _} [Applicative F] {α β} (f : α → F β) (e : Expression α) : F (Expression β) := match_source e with
    | .var v τ, pos => (.var v · @@ pos) <$> f τ
    | .nat n, pos => pure <| .nat n @@ pos
    | .str s, pos => pure <| .str s @@ pos
    | .true, pos => pure <| .true @@ pos
    | .false, pos => pure <| .false @@ pos
    | .opCall e es, pos =>
      (.opCall · · @@ pos) <$> Expression.traverse f e <*> traverse (Expression.traverse f) es
    | .prefixCall op e, pos => (.prefixCall op · @@ pos) <$> Expression.traverse f e
    | .infixCall e₁ op e₂, pos =>
      (.infixCall · op · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
    | .postfixCall e op, pos => (.postfixCall · op @@ pos) <$> Expression.traverse f e
    | .bforall qs e, pos =>
      (.bforall · · @@ pos)
        <$> traverse (bitraverse f (Expression.traverse f)) qs
        <*> Expression.traverse f e
    | .bexists qs e, pos =>
      (.bexists · · @@ pos)
        <$> traverse (bitraverse f (Expression.traverse f)) qs
        <*> Expression.traverse f e
    | .forall vs e, pos => (.forall vs · @@ pos) <$> Expression.traverse f e
    | .exists vs e, pos => (.exists vs · @@ pos) <$> Expression.traverse f e
    | .fforall vs e, pos => (.fforall vs · @@ pos) <$> Expression.traverse f e
    | .eexists vs e, pos => (.eexists vs · @@ pos) <$> Expression.traverse f e
    | .choose vs e₁ e₂, pos =>
      (.choose vs · · @@ pos) <$> traverse (Expression.traverse f) e₁ <*> Expression.traverse f e₂
    | .set es τ, pos =>
      (.set · · @@ pos) <$> traverse (Expression.traverse f) es <*> f τ
    | .collect vs e₁ e₂, pos =>
      (.collect vs · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
    | .map' e qs, pos =>
      (.map' · · @@ pos) <$> Expression.traverse f e <*> traverse (bitraverse f (Expression.traverse f)) qs
    | .fnCall e es, pos =>
      (.fnCall · · @@ pos) <$> Expression.traverse f e <*> traverse (Expression.traverse f) es
    | .fn qs e, pos =>
      (.fn · · @@ pos)
        <$> traverse (bitraverse f (Expression.traverse f)) qs
        <*> Expression.traverse f e
    | .fnSet e₁ e₂, pos =>
      (.fnSet · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
    | .record fs, pos =>
      (.record · @@ pos) <$> traverse (Prod.traverse₃ f pure (Expression.traverse f)) fs
    | .recordSet fs, pos =>
      (.recordSet · @@ pos) <$> traverse (Prod.traverse₃ f pure (Expression.traverse f)) fs
    | .except e upds, pos =>
      (.except · · @@ pos)
        <$> Expression.traverse f e
        <*> traverse (bitraverse (traverse (bitraverse pure (traverse (Expression.traverse f)))) (Expression.traverse f)) upds
    | .recordAccess e v, pos => (.recordAccess · v @@ pos) <$> Expression.traverse f e
    | .tuple es, pos =>
      (.tuple · @@ pos) <$> traverse (bitraverse (Expression.traverse f) f) es
    | .seq es τ, pos =>
      (.seq · · @@ pos) <$> traverse (Expression.traverse f) es <*> f τ
    | .if e₁ e₂ e₃, pos =>
      (.if · · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂ <*> Expression.traverse f e₃
    | .case es e, pos =>
      (.case · · @@ pos)
        <$> traverse (bitraverse (Expression.traverse f) (Expression.traverse f)) es
        <*> traverse (Expression.traverse f) e
    | .stutter e₁ e₂, pos =>
      (.stutter · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂

  instance : Traversable Expression where
    traverse := Expression.traverse

  -- TODO: support distfix heads for operator definitions
  -- (keep in mind that to define the prefix `-`, one has to write `-. _ == _`, not `- _ == _`, somehow)

  inductive Declaration (α : Type) : Type
    | constants : List (String × α) → Declaration α
    | «variables» : List (String × α) → Declaration α
    | assume : Expression α → Declaration α
    /--
      An operator definition with optionally higher-order arguments.
      The `Nat` value associated to each parameter denotes its number of parameters (e.g. 0 for `x`, 3 for `F(_, _, _)`, …).
    -/
    | operator : α → String → List (String × Nat) → Expression α → Declaration α
    /-- A function definition given a domain for all its arguments. -/
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

  structure Module (α β : Type _) : Type _ where
    name : String
    «extends» : List String
    declarations₁ : List (Declaration β)
    pcalAlgorithm : Option α -- (SurfacePlusCal.Algorithm Expr)
    declarations₂ : List (Declaration β)
    deriving Repr

  instance : Bifunctor Module where
    bimap f g m := {m with
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
