module

public import Network2Go.Expression

public section

/-!
  Compiling TLA⁺ operator and function definitions into Go top-level declarations (thesis §7.2.2).

  Four forms, and which one a declaration takes is read off its *type*, not its syntax:

  - **A parameter-less operator** (`X == e`) becomes a package-level `var X τ = ⟦e⟧`. Not a `const`:
    Go accepts only a small class of types there, and a TLA⁺ definition generally has none of them.
    Immutability is a convention here rather than something Go enforces.
  - **A parametric operator** (`X(p₁, …, pₙ) == e`) becomes an ordinary Go function. Go supports
    mutually recursive top-level functions natively, so nothing special is needed — and in this
    compiler an operator is never recursive at all: `RECURSIVE` is out of the accepted language, and
    `Elaborator/Declarations.lean`'s `[Operator definition]` rule checks the body without the
    operator itself in `Γ`. The thesis's mutually-recursive `Even`/`Odd` example is unreachable.
  - **A non-recursive function definition** (`F[x ∈ D] == e`) becomes `var F = FnConstructor(…)`.
  - **A recursive function definition** becomes `var F = MkRecFn(…)`, which ties the knot: it
    allocates the `LazyFunction` with no generator, then overwrites the generator with a closure
    that captures the function itself. Unlike operators, a function definition *always* gets
    self-recursion (`[Function definition]` binds `f` while checking the body), so which of the two
    to emit is decided by looking for the self-reference rather than by a keyword.

  **Type variables reach only the parametric-operator form.** A rigid type variable compiles to a
  Go type parameter, and each one carries a dictionary parameter beside it, since a polymorphic
  definition is called at many types and its ordering therefore cannot be a closed expression. Go
  has no generic package-level `var`, so the other three forms — all of which are `var`s — must
  reject one. That is a restriction of Go's, not a choice: there is nowhere to bind the parameter.

  `CONSTANT`/`VARIABLE` declarations and `ASSUME` produce nothing. A `CONSTANT` is supplied by
  whoever wires the generated code into a runnable system, under the capitalized name every
  reference to it compiles to — the same boundary the absence of an emitted `main` sits on. An
  `ASSUME` is a proof obligation about a specification, with no computational content to emit.
-/

namespace Network2Go

open ComputableTLAPlus (Typ)

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty N2GError m] [MonadFresh m]

/-- Does `name` occur in `e` as a reference to the enclosing *definition* being checked?

A function definition's body sees its own name as an ordinary binder (`Elaborator/Context.lean`'s
`extendAll` tags every binding it introduces `.binder`), which is what distinguishes a self-call
from a reference to some other module-level definition — those carry `.module`. The caller has
already ruled out a parameter of the same name, so the origin check is exact and no
binder-respecting scope walk is needed. -/
partial def mentionsSelf (name : String) (e : ComputablePlusCal.Expression) : Bool :=
  let go := mentionsSelf name
  match_source e with
  | .var x _ .binder, _ => x == name
  | .var .., _ | .nat _, _ | .str _, _ | .true, _ | .false, _ => false
  | .opCall f args, _ => go f || args.any go
  | .forall _ _ d b, _ | .exists _ _ d b, _ | .choose _ _ d b, _ | .collect _ _ d b, _ =>
    go d || go b
  | .set es _, _ | .seq es _, _ => es.any go
  | .map' b _ _ _ d, _ => go b || go d
  | .fn _ _ _ d b, _ => go d || go b
  | .fnCall f _ i, _ => go f || go i
  | .record fs, _ => fs.any λ (_, _, e') ↦ go e'
  | .except f _ upds, _ =>
    go f || upds.any λ (path, rhs) ↦
      go rhs || path.any λ | .inl _ => false | .inr i => go i
  | .recordAccess r _, _ => go r
  | .tuple es, _ => es.any λ (_, e') ↦ go e'
  | .if c t f _, _ => go c || go t || go f
  | .case arms other _, _ =>
    arms.any (λ (p, b) ↦ go p || go b) || (other.map go).getD false

/-- The Go type parameters a definition of type `τ` binds, each paired with the dictionary
parameter that carries its ordering. Type parameters are unconstrained (`any`): the ordering
travels as a value, which is the whole point of the dictionary representation.

The dictionary's type argument goes through `binderName` exactly as the type parameter itself does,
and for a sharper reason than consistency: a type variable named after a predeclared identifier
would otherwise leave `Ord[int]` referring to *Go's* `int` while the parameter it is meant to order
is the renamed `int_`. That reads as well-typed and means something else. -/
private def genericParams (τ : Typ) : List (String × Go.Typ) × List (String × Go.Typ) :=
  let vars := Typ.typeVars τ
  ( vars.map λ a ↦ (binderName a, .named "any" []),
    vars.map λ a ↦ (ordParamName a, tlaplusTyp "Ord" [.var (binderName a)]) )

/-- A form that compiles to a package-level `var` cannot be polymorphic — Go has no generic `var`.
`what` names the form, for the diagnostic. -/
private def requireMonomorphic (pos : SourceSpan) (what name : String) (τ : Typ) : m Unit :=
  if (Typ.typeVars τ).isEmpty then pure () else
    throw (.unsupported pos s!"{what} '{name}'"
      "it compiles to a package-level Go variable, and Go has no generic variables — only a \
       parametric operator can carry type parameters")

/--
  Compiles one top-level declaration, or nothing for the ones with no computational content.
-/
def compileDeclaration (pos : SourceSpan) :
    ComputableTLAPlus.Declaration Typ → m (Option ComputableGo.Declaration)
  | .constants _ | .variables _ | .assume _ => return none
  | .operator τ f [] body => do
    -- `X == e`: the annotation is the result type directly, not `() => τ` — a parameter-less
    -- definition is referenced by bare name and never called.
    requireMonomorphic pos "the definition" f τ
    return some (.var (definitionName (isLocal := false) f) (← compileTyp τ) (some (← compileExpr body)))
  | .operator τ f args body => do
    let .operator paramTys ret := τ
      | throw (.internalInvariantViolated pos
          s!"operator '{f}' takes arguments but its type is {repr τ}, which type checking should \
             already have rejected")
    if paramTys.length ≠ args.length then
      throw (.internalInvariantViolated pos
        s!"operator '{f}' has {args.length} parameters but {paramTys.length} parameter types")
    let (typeParams, dictParams) := genericParams τ
    -- Parameter names are left as written: §7.2.2 capitalizes definitions, not the variables bound
    -- inside them, and every reference to one compiles as an ordinary binder.
    let params ← (args.zip paramTys).mapM λ ((x, _arity), τᵢ) ↦ return (binderName x, ← compileTyp τᵢ)
    return some (.function
      { name := definitionName (isLocal := false) f
        typeParams, params := dictParams ++ params
        returnType := [← compileTyp ret]
        body := [.return [← compileExpr body]] })
  | .function τ f args body => do
    requireMonomorphic pos "the function definition" f τ
    let .function domτ ranτ := τ
      | throw (.internalInvariantViolated pos
          s!"function '{f}' has type {repr τ}, which type checking should already have rejected")
    let [(x, dom)] := args
      | throw (.unsupported pos s!"the function definition '{f}'"
          "a function of several binders has the Cartesian product of their domains as its own \
           domain, and the runtime has no product construction to build it with")
    -- With the same name on both, `MkRecFn`'s generator would take two parameters called `f`.
    if x == f then
      throw (.unsupported pos s!"the function definition '{f}'"
        "its binder shadows its own name, so a recursive reference could not be told from a \
         reference to the binder")
    let goτ ← compileTyp τ
    let dict ← ordDict domτ
    let dom' ← compileExpr dom
    let paramτ ← compileTyp domτ
    let retτ ← compileTyp ranτ
    let body' ← compileExpr body
    -- The self-reference compiles to the *original* name, being an ordinary binder, so naming the
    -- generator's first parameter after it is exactly what closes the loop. The top-level `var` is
    -- capitalized and so cannot collide with it.
    let value :=
      if mentionsSelf f body then
        tlaplusCall "MkRecFn"
          [dict, dom', .funcLit [(binderName f, goτ), (binderName x, paramτ)] [retτ] [.return [body']]]
      else
        tlaplusCall "FnConstructor" [dict, dom', .funcLit [(binderName x, paramτ)] [retτ] [.return [body']]]
    return some (.var (definitionName (isLocal := false) f) goτ (some value))

/-- A whole declaration list, keeping only what compiles to something. Order is preserved: Go
resolves package-level declarations independently of the order they are written in, so this matters
for readability rather than for correctness. -/
def compileDeclarations (pos : SourceSpan) (ds : List (ComputableTLAPlus.Declaration Typ)) :
    m (List ComputableGo.Declaration) :=
  return (← ds.mapM (compileDeclaration pos)).reduceOption

end Network2Go

end
