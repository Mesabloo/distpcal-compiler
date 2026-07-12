module

public import Mathlib.Control.Bifunctor
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Control.Traversable.Instances
public import Mathlib.Control.Bitraversable.Basic
public import Mathlib.Control.Bitraversable.Instances

@[expose] public section


/-!
  The shape of a TLA⁺ declaration/module, shared verbatim by `SurfaceTLAPlus`, `CoreTLAPlus`,
  `TypedTLAPlus` — each stage's `Declaration`/`Module` used to be identical source text, differing
  only in which stage's `Expression` former they closed over. Parametrized here by that former
  (`E`) so the shape and its `Functor`/`Traversable`/`Bifunctor`/`Bitraversable` instances are
  defined once; each stage recovers its `Declaration`/`Module` via an `abbrev` over its
  `Expression`.
-/

/-- A top-level TLA⁺ declaration. `RECURSIVE` and module `INSTANCE` are not represented. -/
inductive Declaration (E : Type → Type) (α : Type) : Type
  | constants : List (String × α) → Declaration E α
  | «variables» : List (String × α) → Declaration E α
  | assume : E α → Declaration E α
  /--
    An operator definition, optionally with higher-order arguments. Each parameter's `Nat`
    is its arity (`0` for `x`, `3` for `F(_, _, _)`, …).
  -/
  | operator : α → String → List (String × Nat) → E α → Declaration E α
  /-- A function definition, with an explicit domain for every argument. -/
  | function : α → String → List (String × E α) → E α → Declaration E α

/-- Hand-written since `deriving Repr` can't discharge the higher-kinded `Repr (E α)` obligation. -/
instance {E α} [Repr α] [Repr (E α)] : Repr (Declaration E α) where
  reprPrec d _ := match d with
    | .constants xs => f!"Declaration.constants {repr xs}"
    | .variables xs => f!"Declaration.variables {repr xs}"
    | .assume e => f!"Declaration.assume {repr e}"
    | .operator a x args e => f!"Declaration.operator {repr a} {repr x} {repr args} {repr e}"
    | .function a x args e => f!"Declaration.function {repr a} {repr x} {repr args} {repr e}"

instance {E} [Functor E] : Functor (Declaration E) where
  map f
    | .constants xs => .constants (Bifunctor.snd f <$> xs)
    | .variables xs => .variables (Bifunctor.snd f <$> xs)
    | .assume e => .assume (f <$> e)
    | .operator a x args e => .operator (f a) x args (f <$> e)
    | .function a x args e => .function (f a) x (Bifunctor.snd (f <$> ·) <$> args) (f <$> e)

instance {E} [Traversable E] : Traversable (Declaration E) where
  traverse f
    | .constants xs => .constants <$> traverse (bitraverse pure f) xs
    | .variables xs => .variables <$> traverse (bitraverse pure f) xs
    | .assume e => .assume <$> traverse f e
    | .operator a x args e => (.operator · x args ·) <$> f a <*> traverse f e
    | .function a x args e => (.function · x · ·) <$> f a <*> traverse (bitraverse pure (traverse f)) args <*> traverse f e

/--
  A TLA⁺ module, `EXTENDS`-list and all, wrapping the embedded (Distributed) PlusCal algorithm at
  whatever `α` the caller instantiates it at — kept abstract to avoid a cyclic import between the
  TLA⁺ and PlusCal Core ASTs. Each stage recovers its `Module` via an `abbrev` over its
  `Expression` (`SurfaceTLAPlus.Module`, `CoreTLAPlus.Module`, `TypedTLAPlus.Module`). Dot-called
  extension methods under a stage's `Module` namespace (`mod.runChecker`, `mod.checkWellFormed`,
  …) become qualified calls rather than method calls: generalized field notation resolves through
  the `abbrev`'s full unfold, landing on this shared type instead of the stage's (nonexistent)
  namespace.
-/
structure Module (E : Type → Type) (α β : Type) : Type where
  name : String
  «extends» : List String
  declarations₁ : List (Declaration E β)
  pcalAlgorithm : Option α
  declarations₂ : List (Declaration E β)
  deriving Inhabited

/-- Hand-written, same reason as `Declaration`'s `Repr` instance above. -/
instance {E α β} [Repr α] [Repr β] [Repr (E β)] : Repr (Module E α β) where
  reprPrec m _ :=
    f!"\{ name := {repr m.name}, extends := {repr m.extends}, declarations₁ := {repr m.declarations₁}, " ++
    f!"pcalAlgorithm := {repr m.pcalAlgorithm}, declarations₂ := {repr m.declarations₂} }"

instance {E} [Functor E] : Bifunctor (Module E) where
  bimap f g m := { m with
    declarations₁ := (g <$> ·) <$> m.declarations₁
    pcalAlgorithm := f <$> m.pcalAlgorithm
    declarations₂ := (g <$> ·) <$> m.declarations₂
  }

instance {E} [Traversable E] : Bitraversable (Module E) where
  bitraverse f g m :=
    ({m with declarations₁ := ·, pcalAlgorithm := ·, declarations₂ := ·})
      <$> traverse (traverse g) m.declarations₁
      <*> traverse f m.pcalAlgorithm
      <*> traverse (traverse g) m.declarations₂

end
