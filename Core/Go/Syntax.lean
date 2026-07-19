module

public import Mathlib.Control.Bifunctor
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Control.Bitraversable.Basic
public import Mathlib.Control.Bitraversable.Instances

public section


/-!
  The target of `Network2Go`: the fragment of Go the thesis gives a denotational semantics to
  (§6.6, Definitions 6.6.1 and 6.6.11–6.6.20), extended with what §7.2's compilation listings
  actually emit.

  - **Written from the thesis, not ported.** Prior art's `GoCal`
    (`~/Documents/distpcal-compiler/Core/Go/Syntax.lean`, same on both its `typechecker` and
    `go-semantics` branches) has no Go type or expression AST at all: it parameterizes its
    statement layer over TLA⁺ `TypedSetTheory.Typ`/`Expression` and reuses
    `NetworkPlusCal.ChanRef` for references. Consequence for the pass: compiling TLA⁺ types and
    expressions *into* the ones below is real work (§7.2.1/§7.2.2), not something parameterization
    hands over for free.
  - **Blocks are `List Statement`**, not §6.6's `; S` continuation style, so `var`/`make` are
    ordinary statements scoped by position rather than by a syntactic continuation. Nothing in the
    semantics depends on the difference — a denotation folds over the list.
  - **Beyond §6.6:** composite literals (`structLit`/`sliceLit`/`mapLit`/`make`) and
    `Typ.named`/`Typ.var`. §7.2's listings need `Lock[struct {…}]`, `Receiver[T]`, `Set[T]`,
    `LazyFunction[T, U]`, `Address`, `Network`; without them the generated code has to route
    around its own runtime library.
  - `Ref` is Go's own (`_`, `x`, `r[e]`, `r.x`, Definition 6.6.11), generic over `Expr` alone —
    unlike `GuardedPlusCal.Ref` it carries no type annotation, so it gets `Functor`/`Traversable`
    rather than the bifunctor pair.
  - `&&`/`||` are ordinary `BinaryOperator` cases, even though Definition 6.6.9 gives them
    short-circuiting semantics: that is a property of their semantic rule, which case-splits on the
    operator regardless, not of the syntax. Splitting them out bought nothing and cost a case in
    every traversal.
  - `switch`'s default is a required field (§6.6.15 always has a `_ → {S}` tail); `select`'s is
    optional, since a blocking `select` with no default is exactly what §7.2.3's scheduling loops
    emit.
  - Instances follow `Core/CorePlusCal/Syntax.lean`'s shape for a *nested* statement type
    (`mutual`-free `partial def` + explicit instance) rather than `Core/NetworkPlusCal/Syntax.lean`'s
    derived-style ones, which only work because its `Statement` is flat.
  - Pinned at `Go.Typ`/`Go.Expression Go.Typ` in `ComputableGo` below, mirroring how
    `Core/ComputablePlusCal/Syntax.lean` pins its own shared layer. This file imports nothing from
    `Core/` — the Go AST doesn't mention TLA⁺.
-/

namespace Go

/-- Go types, per the cases `𝟘⋅` is defined over (Definition 6.6.1), plus `named`/`var` for §7.2's
generic runtime types. -/
inductive Typ : Type
  | int
  | str
  | bool
  /-- `chan τ` -/
  | chan (τ : Typ)
  /-- `[]τ` -/
  | slice (τ : Typ)
  /-- `[n]τ` -/
  | array (n : Nat) (τ : Typ)
  /-- `map[κ]τ` -/
  | map (key value : Typ)
  /-- `struct {x₁ τ₁, …, xₙ τₙ}` -/
  | «struct» (fields : List (String × Typ))
  /-- `func(τ₁, …, τₙ) (τ'₁, …, τ'ₘ)` — parameter names aren't part of the type. -/
  | func (params returns : List Typ)
  /-- A named type, applied to type arguments when generic: `Address`, `Network`, `Lock[τ]`,
  `Receiver[τ]`, `Set[τ]`, `LazyFunction[τ, τ']`. -/
  | named (name : String) (args : List Typ)
  /-- A generic type parameter, bound by the enclosing `Function.typeParams`. -/
  | var (name : String)
  deriving Repr, Inhabited, BEq

inductive UnaryOperator : Type
  /-- `!e` -/
  | not
  /-- `-e` -/
  | neg
  deriving Repr, Inhabited, BEq

/-- Binary operators, including the short-circuiting `&&`/`||` (Definition 6.6.9). Their
non-strictness is a fact about the semantic rule for `and`/`or`, not about the syntax, so they live
here rather than as separate `Expression` constructors — a denotation case-splits on the operator
either way. -/
inductive BinaryOperator : Type
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  /-- `e₁ && e₂` — short-circuiting. -/
  | and
  /-- `e₁ || e₂` — short-circuiting. -/
  | or
  deriving Repr, Inhabited, BEq

/-- Go's builtin functions, kept out of `Expression.call` so that a user-chosen name colliding with
one of them is a non-issue. -/
inductive Builtin : Type
  | len
  | cap
  | append
  deriving Repr, Inhabited, BEq

/-- Go expressions (§6.6.2). `α` carries type annotations at the sites that need one — the same
role it plays in `ComputableTLAPlus.Expression`. -/
inductive Expression (α : Type) : Type
  /-- An integer literal, kept as its source text (same as `ComputableTLAPlus.Expression.nat`). -/
  | nat (n : String)
  | str (s : String)
  | «true»
  | «false»
  | var (name : String)
  | unary (op : UnaryOperator) (e : Expression α)
  | binary (op : BinaryOperator) (e₁ e₂ : Expression α)
  /-- `e[i]` -/
  | index (e i : Expression α)
  /-- `e.x` -/
  | field (e : Expression α) (name : String)
  | call (f : Expression α) (args : List (Expression α))
  | builtin (b : Builtin) (args : List (Expression α))
  /-- `τ{x₁: e₁, …}` — also covers named composite literals like `LazyFunction{…}`. -/
  | structLit (τ : α) (fields : List (String × Expression α))
  /-- `τ{e₁, …, eₙ}` -/
  | sliceLit (τ : α) (elems : List (Expression α))
  /-- `τ{k₁: v₁, …}` -/
  | mapLit (τ : α) (entries : List (Expression α × Expression α))
  /-- `make(τ, e₁, …)` — the expression form (`make(map[K]V)`); channel creation has its own
  statement, `Statement.make`. -/
  | make (τ : α) (args : List (Expression α))
  deriving Repr, Inhabited

/-- An assignable reference (Definition 6.6.11). No type annotation, unlike `GuardedPlusCal.Ref`. -/
inductive Ref (Expr : Type) : Type
  /-- `_` -/
  | wildcard
  | var (name : String)
  /-- `r[e]` -/
  | index (r : Ref Expr) (e : Expr)
  /-- `r.x` -/
  | field (r : Ref Expr) (name : String)
  deriving Repr, Inhabited

/-- One `g → {S}` arm of a `select` (Definition 6.6.19). `guard` is itself a statement — in
practice a `send` or `receive`. Generic over the statement type so that `Statement` below can
nest it. -/
structure SelectClause (α : Type) : Type where
  guard : α
  body : List α
  deriving Repr, Inhabited

/-- One `v → {S}` arm of a `switch` (Definition 6.6.15). -/
structure SwitchClause (Expr α : Type) : Type where
  head : Expr
  body : List α
  deriving Repr, Inhabited

/-- Go statements (§6.6.3.4). Blocks are `List Statement` — see the module doc. -/
inductive Statement (Typ Expr : Type) : Type
  | skip
  | print (e : Expr)
  | panic (e : Expr)
  /-- `return e₁, …, eₙ` — Go's multi-valued return, widened from §6.6.12's single `e`. -/
  | «return» (es : List Expr)
  /-- `var x τ`, zero-initialized. -/
  | var (name : String) (τ : Typ)
  /-- `r₁, …, rₙ = e₁, …, eₘ` — covers both `a, b = 1, 2` and `a, b = f()`. -/
  | assign (lhs : List (Ref Expr)) (rhs : List Expr)
  /-- `c := make(chan τ, k)`; `capacity` absent means a synchronous (unbuffered) channel. -/
  | make (name : String) (τ : Typ) (capacity : Option Expr)
  | close (c : Expr)
  /-- `c <- e` -/
  | send (c : Expr) (e : Expr)
  /-- `x, ok = <-c`; `ok` absent for the single-valued form. -/
  | receive (c : Expr) (x : Ref Expr) (ok : Option (Ref Expr))
  | go (body : List (Statement Typ Expr))
  | «if» (cond : Expr) (thenBranch elseBranch : List (Statement Typ Expr))
  /-- `for e do {S}` — Go's conditional loop. -/
  | «for» (cond : Expr) (body : List (Statement Typ Expr))
  | «switch» (e : Expr) (cases : List (SwitchClause Expr (Statement Typ Expr)))
      («default» : List (Statement Typ Expr))
  /-- A `default`-less `select` blocks until some guard fires. -/
  | select (cases : List (SelectClause (Statement Typ Expr)))
      («default» : Option (List (Statement Typ Expr)))
  deriving Repr, Inhabited

/-- A top-level function (Definition 6.6.20), plus `typeParams` for the generic functions §7.2
emits. Each type parameter carries its constraint, which is an ordinary type: `any`,
`comparable`, or one of the runtime library's own interfaces (`Eq[T]`, `Ord[T]` — §7.2.1.2). -/
structure Function (Typ Expr : Type) : Type where
  name : String
  typeParams : List (String × Typ)
  params : List (String × Typ)
  returnType : List Typ
  body : List (Statement Typ Expr)
  deriving Repr, Inhabited

def Ref.map {Expr Expr'} (g : Expr → Expr') : Ref Expr → Ref Expr'
  | .wildcard => .wildcard
  | .var name => .var name
  | .index r e => .index (Ref.map g r) (g e)
  | .field r name => .field (Ref.map g r) name

def Ref.traverse {m : Type → Type} [Applicative m] {Expr Expr'} (g : Expr → m Expr') :
    Ref Expr → m (Ref Expr')
  | .wildcard => pure .wildcard
  | .var name => pure (.var name)
  | .index r e => .index <$> Ref.traverse g r <*> g e
  | .field r name => (.field · name) <$> Ref.traverse g r

instance : Functor Ref where
  map := Ref.map

instance : Traversable Ref where
  traverse := Ref.traverse

/-- `partial` rather than structurally recursive: `α` occurs under `List`/`Prod` in most
constructors, the same situation `Core/CorePlusCal/Syntax.lean`'s own instances are `partial` for. -/
partial def Expression.map {α β} (f : α → β) : Expression α → Expression β
  | .nat n => .nat n
  | .str s => .str s
  | .true => .true
  | .false => .false
  | .var name => .var name
  | .unary op e => .unary op (Expression.map f e)
  | .binary op e₁ e₂ => .binary op (Expression.map f e₁) (Expression.map f e₂)
  | .index e i => .index (Expression.map f e) (Expression.map f i)
  | .field e name => .field (Expression.map f e) name
  | .call g args => .call (Expression.map f g) (Expression.map f <$> args)
  | .builtin b args => .builtin b (Expression.map f <$> args)
  | .structLit τ fields => .structLit (f τ) (Prod.map id (Expression.map f) <$> fields)
  | .sliceLit τ elems => .sliceLit (f τ) (Expression.map f <$> elems)
  | .mapLit τ entries => .mapLit (f τ) (Prod.map (Expression.map f) (Expression.map f) <$> entries)
  | .make τ args => .make (f τ) (Expression.map f <$> args)

instance : Functor Expression where
  map := Expression.map

local instance {F : Type _ → Type _} [Applicative F] {α} [Inhabited α] : Inhabited (F α) :=
  ⟨pure default⟩ in
partial def Expression.traverse {F : Type _ → Type _} [Applicative F] {α β} (f : α → F β) :
    Expression α → F (Expression β)
  | .nat n => pure (.nat n)
  | .str s => pure (.str s)
  | .true => pure .true
  | .false => pure .false
  | .var name => pure (.var name)
  | .unary op e => .unary op <$> Expression.traverse f e
  | .binary op e₁ e₂ => .binary op <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
  | .index e i => .index <$> Expression.traverse f e <*> Expression.traverse f i
  | .field e name => (.field · name) <$> Expression.traverse f e
  | .call g args =>
    .call <$> Expression.traverse f g <*> Traversable.traverse (Expression.traverse f) args
  | .builtin b args => .builtin b <$> Traversable.traverse (Expression.traverse f) args
  | .structLit τ fields =>
    .structLit <$> f τ <*> Traversable.traverse (bitraverse pure (Expression.traverse f)) fields
  | .sliceLit τ elems =>
    .sliceLit <$> f τ <*> Traversable.traverse (Expression.traverse f) elems
  | .mapLit τ entries =>
    .mapLit <$> f τ
      <*> Traversable.traverse
        (bitraverse (Expression.traverse f) (Expression.traverse f)) entries
  | .make τ args => .make <$> f τ <*> Traversable.traverse (Expression.traverse f) args

instance : Traversable Expression where
  traverse := Expression.traverse

partial def Statement.bimap {Typ Typ' Expr Expr'} (f : Typ → Typ') (g : Expr → Expr') :
    Statement Typ Expr → Statement Typ' Expr'
  | .skip => .skip
  | .print e => .print (g e)
  | .panic e => .panic (g e)
  | .return es => .return (g <$> es)
  | .var name τ => .var name (f τ)
  | .assign lhs rhs => .assign (Ref.map g <$> lhs) (g <$> rhs)
  | .make name τ capacity => .make name (f τ) (g <$> capacity)
  | .close c => .close (g c)
  | .send c e => .send (g c) (g e)
  | .receive c x ok => .receive (g c) (Ref.map g x) (Ref.map g <$> ok)
  | .go body => .go (Statement.bimap f g <$> body)
  | .if cond B₁ B₂ => .if (g cond) (Statement.bimap f g <$> B₁) (Statement.bimap f g <$> B₂)
  | .for cond body => .for (g cond) (Statement.bimap f g <$> body)
  | .switch e cases «default» =>
    .switch (g e)
      ((λ c ↦ { head := g c.head, body := Statement.bimap f g <$> c.body }) <$> cases)
      (Statement.bimap f g <$> «default»)
  | .select cases «default» =>
    .select
      ((λ c ↦ { guard := Statement.bimap f g c.guard, body := Statement.bimap f g <$> c.body })
        <$> cases)
      ((Statement.bimap f g <$> ·) <$> «default»)

instance : Bifunctor Statement where
  bimap := Statement.bimap

local instance {F : Type _ → Type _} [Applicative F] {α} [Inhabited α] : Inhabited (F α) :=
  ⟨pure default⟩ in
partial def Statement.bitraverse {F : Type _ → Type _} [Applicative F] {Typ Typ' Expr Expr'}
    (f : Typ → F Typ') (g : Expr → F Expr') : Statement Typ Expr → F (Statement Typ' Expr')
  | .skip => pure .skip
  | .print e => .print <$> g e
  | .panic e => .panic <$> g e
  | .return es => .return <$> traverse g es
  | .var name τ => .var name <$> f τ
  | .assign lhs rhs => .assign <$> traverse (Ref.traverse g) lhs <*> traverse g rhs
  | .make name τ capacity => .make name <$> f τ <*> traverse g capacity
  | .close c => .close <$> g c
  | .send c e => .send <$> g c <*> g e
  | .receive c x ok =>
    .receive <$> g c <*> Ref.traverse g x <*> traverse (Ref.traverse g) ok
  | .go body => .go <$> traverse (Statement.bitraverse f g) body
  | .if cond B₁ B₂ =>
    .if <$> g cond
      <*> traverse (Statement.bitraverse f g) B₁
      <*> traverse (Statement.bitraverse f g) B₂
  | .for cond body => .for <$> g cond <*> traverse (Statement.bitraverse f g) body
  | .switch e cases «default» =>
    .switch <$> g e
      <*> traverse
        (λ c ↦ SwitchClause.mk <$> g c.head <*> traverse (Statement.bitraverse f g) c.body) cases
      <*> traverse (Statement.bitraverse f g) «default»
  | .select cases «default» =>
    .select
      <$> traverse
        (λ c ↦ SelectClause.mk
          <$> Statement.bitraverse f g c.guard
          <*> traverse (Statement.bitraverse f g) c.body) cases
      <*> traverse (traverse (Statement.bitraverse f g)) «default»

instance : Bitraversable Statement where
  bitraverse := Statement.bitraverse

instance : Bifunctor Function where
  bimap f g F := { F with
    typeParams := Prod.map id f <$> F.typeParams
    params := Prod.map id f <$> F.params
    returnType := f <$> F.returnType
    body := Statement.bimap f g <$> F.body
  }

instance : Bitraversable Function where
  bitraverse f g F :=
    (Function.mk F.name · · · ·)
      <$> traverse (bitraverse pure f) F.typeParams
      <*> traverse (bitraverse pure f) F.params
      <*> traverse f F.returnType
      <*> traverse (Statement.bitraverse f g) F.body

end Go

-- Pinned for `Network2Go`'s use, mirroring `Core/NetworkPlusCal/Syntax.lean`'s
-- `ComputableNetworkPlusCal` pinning. Unlike every other layer's pinning, the parameters are
-- instantiated at this language's *own* types: a Go expression is annotated with Go types.
namespace ComputableGo

abbrev Typ := Go.Typ
abbrev Expression := Go.Expression Go.Typ
abbrev Ref := Go.Ref Expression
abbrev Statement := Go.Statement Typ Expression
abbrev SelectClause := Go.SelectClause Statement
abbrev SwitchClause := Go.SwitchClause Expression Statement
abbrev Function := Go.Function Typ Expression

end ComputableGo

end
