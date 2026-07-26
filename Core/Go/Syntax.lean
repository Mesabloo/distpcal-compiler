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
  - **Beyond §6.6:** composite literals (`structLit`/`sliceLit`/`mapLit`/`make`), function literals
    (`funcLit`), and `Typ.named`/`Typ.var`. §7.2's listings need `Lock[struct {…}]`, `Receiver[T]`,
    `Set[T]`, `LazyFunction[T, U]`, `Address`, `Network`; without them the generated code has to
    route around its own runtime library.
  - **`Expression` and `Statement` are one `mutual` family, parameterized by a single `α`** (the
    type annotations expressions carry) rather than `Statement` being generic over its expression
    type. `funcLit` forces this: every callback the runtime library takes (`SetFilter`/`SetMap`/
    `Choose`'s predicates, `FnConstructor`/`MkRecFn`'s generators — §7.2.1.2) has a *statement*
    body, and so does the only faithful compilation of `IF`/`CASE`, Go having no conditional
    expression and an eager helper being wrong (`IF x # 0 THEN 1/x ELSE 0` must not evaluate both
    arms). A `Statement` generic over `Expr` cannot tie that knot. The cost is the
    `Bifunctor`/`Bitraversable` pair on `Statement`/`Function`, which become `Functor`/`Traversable`
    over `α`; nothing was instantiating either parameter independently, Go being the terminal AST.
  - `Ref` is Go's own (`_`, `x`, `r[e]`, `r.x`, Definition 6.6.11), and stays generic over `Expr`
    alone — it is not part of the mutual family, since a reference contains expressions but no
    statements. Unlike `GuardedPlusCal.Ref` it carries no type annotation, so it gets
    `Functor`/`Traversable` rather than the bifunctor pair.
  - `&&`/`||` are ordinary `BinaryOperator` cases, even though Definition 6.6.9 gives them
    short-circuiting semantics: that is a property of their semantic rule, which case-splits on the
    operator regardless, not of the syntax. Splitting them out bought nothing and cost a case in
    every traversal.
  - `switch`'s default is a required field (§6.6.15 always has a `_ → {S}` tail); `select`'s is
    optional, since a blocking `select` with no default is exactly what §7.2.3's scheduling loops
    emit.
  - Instances follow `Core/CorePlusCal/Syntax.lean`'s shape for a *nested* statement type
    (`partial def` + explicit instance) rather than `Core/NetworkPlusCal/Syntax.lean`'s
    derived-style ones, which only work because its `Statement` is flat; the mutual family's
    traversals are one `mutual` block of `partial def`s, mirroring the type declarations.
  - Pinned at `Go.Typ` in `ComputableGo` below, mirroring how `Core/ComputablePlusCal/Syntax.lean`
    pins its own shared layer. This file imports nothing from `Core/` — the Go AST doesn't mention
    TLA⁺.
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

/-- An assignable reference (Definition 6.6.11). No type annotation, unlike `GuardedPlusCal.Ref`.

Generic over `Expr` rather than a member of the `Expression`/`Statement` mutual family below: a
reference contains expressions but never statements, so nothing in it needs the knot tied. -/
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

mutual

/-- Go expressions (§6.6.2), plus `funcLit`. `α` carries type annotations at the sites that need
one — the same role it plays in `ComputableTLAPlus.Expression`. -/
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
  /-- `func(x₁ τ₁, …) (τ'₁, …) { S }` — an anonymous function, closing over whatever is in scope
  at the site it appears.

  Not in §6.6, which has only top-level functions, but §7.2.1.2 cannot be compiled without it:
  `{x ∈ S : P}`, `{e : x ∈ S}`, `CHOOSE x ∈ S : P` and `[x ∈ S ↦ e]` all compile to a runtime
  call taking a callback, and `IF`/`CASE` compile to an immediately-applied literal, Go having no
  conditional expression. Lambda-lifting these to `Function`s is not an alternative: they capture
  the enclosing block's variables, and Go has no partial application to re-supply them with. -/
  | funcLit (params : List (String × α)) (returns : List α) (body : List (Statement α))
  deriving Repr

/-- Go statements (§6.6.3.4). Blocks are `List Statement` — see the module doc. -/
inductive Statement (α : Type) : Type
  | skip
  /-- A call evaluated for its effect, `f(e₁, …)`. Go accepts only a call in this position, never
  an arbitrary expression, so nothing else should be built here.

  Not in §6.6, but §7.2.3 needs it: `net.c.Send(e)` and `Release(ℓ, st)` both return nothing, so
  the `_ = f(…)` form that covers a value-returning call is not available for them. -/
  | expr (e : Expression α)
  | print (e : Expression α)
  | panic (e : Expression α)
  /-- `return e₁, …, eₙ` — Go's multi-valued return, widened from §6.6.12's single `e`. -/
  | «return» (es : List (Expression α))
  /-- `var x τ`, zero-initialized. -/
  | var (name : String) (τ : α)
  /-- `r₁, …, rₙ = e₁, …, eₘ` — covers both `a, b = 1, 2` and `a, b = f()`. -/
  | assign (lhs : List (Ref (Expression α))) (rhs : List (Expression α))
  /-- `c := make(chan τ, k)`; `capacity` absent means a synchronous (unbuffered) channel. -/
  | make (name : String) (τ : α) (capacity : Option (Expression α))
  | close (c : Expression α)
  /-- `c <- e` -/
  | send (c : Expression α) (e : Expression α)
  /-- `x, ok = <-c`; `ok` absent for the single-valued form. -/
  | receive (c : Expression α) (x : Ref (Expression α)) (ok : Option (Ref (Expression α)))
  | go (body : List (Statement α))
  | «if» (cond : Expression α) (thenBranch elseBranch : List (Statement α))
  /-- `for e do {S}` — Go's conditional loop. -/
  | «for» (cond : Expression α) (body : List (Statement α))
  | «switch» (e : Expression α) (cases : List (SwitchClause (Expression α) (Statement α)))
      («default» : List (Statement α))
  /-- A `default`-less `select` blocks until some guard fires. -/
  | select (cases : List (SelectClause (Statement α)))
      («default» : Option (List (Statement α)))
  deriving Repr

end

instance {α} : Inhabited (Expression α) := ⟨.true⟩
instance {α} : Inhabited (Statement α) := ⟨.skip⟩

/-- A top-level function (Definition 6.6.20), plus `typeParams` for the generic functions §7.2
emits. Each type parameter carries its constraint, which is an ordinary type: `any`,
`comparable`, or one of the runtime library's own interfaces (`Eq[T]`, `Ord[T]` — §7.2.1.2). -/
structure Function (α : Type) : Type where
  name : String
  typeParams : List (String × α)
  params : List (String × α)
  returnType : List α
  body : List (Statement α)
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

mutual

/-- `partial` rather than structurally recursive: `α` occurs under `List`/`Prod` in most
constructors, the same situation `Core/CorePlusCal/Syntax.lean`'s own instances are `partial`
for. -/
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
  | .funcLit params returns body =>
    .funcLit (Prod.map id f <$> params) (f <$> returns) (Statement.map f <$> body)

partial def Statement.map {α β} (f : α → β) : Statement α → Statement β
  | .skip => .skip
  | .expr e => .expr (Expression.map f e)
  | .print e => .print (Expression.map f e)
  | .panic e => .panic (Expression.map f e)
  | .return es => .return (Expression.map f <$> es)
  | .var name τ => .var name (f τ)
  | .assign lhs rhs =>
    .assign (Ref.map (Expression.map f) <$> lhs) (Expression.map f <$> rhs)
  | .make name τ capacity => .make name (f τ) (Expression.map f <$> capacity)
  | .close c => .close (Expression.map f c)
  | .send c e => .send (Expression.map f c) (Expression.map f e)
  | .receive c x ok =>
    .receive (Expression.map f c) (Ref.map (Expression.map f) x)
      (Ref.map (Expression.map f) <$> ok)
  | .go body => .go (Statement.map f <$> body)
  | .if cond B₁ B₂ => .if (Expression.map f cond) (Statement.map f <$> B₁) (Statement.map f <$> B₂)
  | .for cond body => .for (Expression.map f cond) (Statement.map f <$> body)
  | .switch e cases «default» =>
    .switch (Expression.map f e)
      ((λ c ↦ { head := Expression.map f c.head, body := Statement.map f <$> c.body }) <$> cases)
      (Statement.map f <$> «default»)
  | .select cases «default» =>
    .select
      ((λ c ↦ { guard := Statement.map f c.guard, body := Statement.map f <$> c.body }) <$> cases)
      ((Statement.map f <$> ·) <$> «default»)

end

instance : Functor Expression where
  map := Expression.map

instance : Functor Statement where
  map := Statement.map

section Traverse

local instance {F : Type _ → Type _} [Applicative F] {α} [Inhabited α] : Inhabited (F α) :=
  ⟨pure default⟩

mutual

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
  | .funcLit params returns body =>
    .funcLit
      <$> Traversable.traverse (bitraverse pure f) params
      <*> Traversable.traverse f returns
      <*> Traversable.traverse (Statement.traverse f) body

partial def Statement.traverse {F : Type _ → Type _} [Applicative F] {α β} (f : α → F β) :
    Statement α → F (Statement β)
  | .skip => pure .skip
  | .expr e => .expr <$> Expression.traverse f e
  | .print e => .print <$> Expression.traverse f e
  | .panic e => .panic <$> Expression.traverse f e
  | .return es => .return <$> Traversable.traverse (Expression.traverse f) es
  | .var name τ => .var name <$> f τ
  | .assign lhs rhs =>
    .assign
      <$> Traversable.traverse (Ref.traverse (Expression.traverse f)) lhs
      <*> Traversable.traverse (Expression.traverse f) rhs
  | .make name τ capacity =>
    .make name <$> f τ <*> Traversable.traverse (Expression.traverse f) capacity
  | .close c => .close <$> Expression.traverse f c
  | .send c e => .send <$> Expression.traverse f c <*> Expression.traverse f e
  | .receive c x ok =>
    .receive
      <$> Expression.traverse f c
      <*> Ref.traverse (Expression.traverse f) x
      <*> Traversable.traverse (Ref.traverse (Expression.traverse f)) ok
  | .go body => .go <$> Traversable.traverse (Statement.traverse f) body
  | .if cond B₁ B₂ =>
    .if <$> Expression.traverse f cond
      <*> Traversable.traverse (Statement.traverse f) B₁
      <*> Traversable.traverse (Statement.traverse f) B₂
  | .for cond body =>
    .for <$> Expression.traverse f cond <*> Traversable.traverse (Statement.traverse f) body
  | .switch e cases «default» =>
    .switch <$> Expression.traverse f e
      <*> Traversable.traverse
        (λ c ↦ SwitchClause.mk
          <$> Expression.traverse f c.head
          <*> Traversable.traverse (Statement.traverse f) c.body) cases
      <*> Traversable.traverse (Statement.traverse f) «default»
  | .select cases «default» =>
    .select
      <$> Traversable.traverse
        (λ c ↦ SelectClause.mk
          <$> Statement.traverse f c.guard
          <*> Traversable.traverse (Statement.traverse f) c.body) cases
      <*> Traversable.traverse (Traversable.traverse (Statement.traverse f)) «default»

end

end Traverse

instance : Traversable Expression where
  traverse := Expression.traverse

instance : Traversable Statement where
  traverse := Statement.traverse

instance : Functor Function where
  map f F := { F with
    typeParams := Prod.map id f <$> F.typeParams
    params := Prod.map id f <$> F.params
    returnType := f <$> F.returnType
    body := Statement.map f <$> F.body
  }

instance : Traversable Function where
  traverse f F :=
    (Function.mk F.name · · · ·)
      <$> Traversable.traverse (bitraverse pure f) F.typeParams
      <*> Traversable.traverse (bitraverse pure f) F.params
      <*> Traversable.traverse f F.returnType
      <*> Traversable.traverse (Statement.traverse f) F.body

/--
  A top-level declaration: what a generated `.go` file is a list of.

  §6.6 has only `Function`, which is enough for the statement layer, but §7.2.2 compiles a
  parameter-less operator and *every* function definition to a package-level `var` — the former
  because Go's `const` accepts only a small class of types, none of which a TLA⁺ definition
  generally has, the latter because a function is a `LazyFunction` value rather than a Go `func`.

  A package-level `var` cannot be generic in Go, which is what forces both forms to reject a type
  variable in their type; only `Function` carries `typeParams`.
-/
inductive Declaration (α : Type) : Type
  | function (F : Function α)
  /-- `var x τ = e`, with `e` absent for a zero-initialized declaration. -/
  | var (name : String) (τ : α) (value : Option (Expression α))
  /-- `type N τ` — a *defined* type, not an alias (`type N = τ`).

  Not in §6.6, which has no top-level type declarations, but §7.2.3 needs one: the `Network`
  struct every generated function takes a parameter of is an anonymous struct type otherwise, and
  Go would then require it spelled out identically at every signature that mentions it. -/
  | typ (name : String) (τ : α)
  deriving Repr, Inhabited

instance : Functor Declaration where
  map f
    | .function F => .function (f <$> F)
    | .var name τ value => .var name (f τ) (Expression.map f <$> value)
    | .typ name τ => .typ name (f τ)

instance : Traversable Declaration where
  traverse f
    | .function F => .function <$> Traversable.traverse f F
    | .var name τ value =>
      (.var name · ·) <$> f τ <*> Traversable.traverse (Expression.traverse f) value
    | .typ name τ => .typ name <$> f τ

end Go

-- Pinned for `Network2Go`'s use, mirroring `Core/NetworkPlusCal/Syntax.lean`'s
-- `ComputableNetworkPlusCal` pinning. Unlike every other layer's pinning, the parameter is
-- instantiated at this language's *own* type: a Go expression is annotated with Go types.
namespace ComputableGo

abbrev Typ := Go.Typ
abbrev Expression := Go.Expression Go.Typ
abbrev Ref := Go.Ref Expression
abbrev Statement := Go.Statement Go.Typ
abbrev SelectClause := Go.SelectClause Statement
abbrev SwitchClause := Go.SwitchClause Expression Statement
abbrev Function := Go.Function Go.Typ
abbrev Declaration := Go.Declaration Go.Typ

end ComputableGo

end
