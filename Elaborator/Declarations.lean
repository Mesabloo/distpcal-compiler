import Elaborator.Expressions

/-!
  Declaration/module-level checking: `checkDeclaration`/`checkDeclarations`, threading `Γ` across
  `CONSTANTS`/`VARIABLES`/`ASSUME`/operator-definition/function-definition, plus `builtinContext`
  — a minimal `Γ₀` prelude of core TLA⁺ operators (equality, boolean connectives, core set
  theory) needed before any user declaration is checked.

  Every declaration's own expressions are closed out via `resolveMVars` before `checkDeclaration`
  returns, so a metavariable freshened during one declaration's checking doesn't leak unresolved
  into the next declaration's `Γ`.

  `THEOREM`/`RECURSIVE` are both out of scope: neither has a `CoreTLAPlus.Declaration`
  constructor. Consequently operator definitions get no self- or mutual recursion (their own name
  is never in scope for their own body), while function definitions get self-recursion
  unconditionally (`f` is in scope checking its own body), matching ordinary TLA⁺ recursive
  function definitions.

  A multi-argument function *definition* `f[x₁ ∈ e₁,...,xₙ ∈ eₙ]` isn't pre-tupled the way a
  multi-index *call* is, so this file reconciles the two: `n = 1` gives a domain type of `τ₁`
  itself; `n > 1` requires the annotation's domain to be `Typ.tuple [τ₁,...,τₙ]`.
-/

open TypedTLAPlus (Typ)

/-- The checker's actual input for one declaration: `CoreTLAPlus.Declaration` at `α := Option Typ`. -/
abbrev SrcDecl := CoreTLAPlus.Declaration (Option Typ)

/-- The checker's output for one declaration. -/
abbrev Decl := TypedTLAPlus.Declaration Typ

/-- `Γ₀` — the minimal builtin prelude. Every entry is a scheme (`Binding.isScheme := true`):
each is a genuine operator definition, so `Typ.var`s used for whatever's meant to be generic get
freshened into their own metavariable at every reference (`specializeType`,
`Elaborator/Expressions.lean`'s `inferExpr`). -/
def builtinContext : Context := Std.HashMap.ofList [
  -- Equality.
  ("=", { type := .operator [.var "a", .var "a"] .bool, isScheme := true, origin := .intrinsic }),
  ("/=", { type := .operator [.var "a", .var "a"] .bool, isScheme := true, origin := .intrinsic }),
  -- Boolean connectives.
  ("/\\", { type := .operator [.bool, .bool] .bool, isScheme := true, origin := .intrinsic }),
  ("\\/", { type := .operator [.bool, .bool] .bool, isScheme := true, origin := .intrinsic }),
  ("=>", { type := .operator [.bool, .bool] .bool, isScheme := true, origin := .intrinsic }),
  ("<=>", { type := .operator [.bool, .bool] .bool, isScheme := true, origin := .intrinsic }),
  ("\\neg", { type := .operator [.bool] .bool, isScheme := true, origin := .intrinsic }),
  -- Sets.
  ("\\in", { type := .operator [.var "a", .set (.var "a")] .bool, isScheme := true, origin := .intrinsic }),
  ("\\notin", { type := .operator [.var "a", .set (.var "a")] .bool, isScheme := true, origin := .intrinsic }),
  ("\\subseteq", { type := .operator [.set (.var "a"), .set (.var "a")] .bool, isScheme := true, origin := .intrinsic }),
  ("\\cup", { type := .operator [.set (.var "a"), .set (.var "a")] (.set (.var "a")), isScheme := true, origin := .intrinsic }),
  ("\\cap", { type := .operator [.set (.var "a"), .set (.var "a")] (.set (.var "a")), isScheme := true, origin := .intrinsic }),
  ("\\", { type := .operator [.set (.var "a"), .set (.var "a")] (.set (.var "a")), isScheme := true, origin := .intrinsic }),
  ("DOMAIN", { type := .operator [.function (.var "a") (.var "b")] (.set (.var "a")), isScheme := true, origin := .intrinsic }),
]

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/-- A higher-order parameter's declared arity (`0` for `x`, `k` for `F(_,...,_)` with `k` `_`s)
must match its annotated type's own operator-arity, once one is known. Arity `0` needs no check
at all — any type is a legitimate ordinary-value parameter, including an operator-shaped one. -/
private def checkParamArity (pos : SourceSpan) (param : String) (arity : Nat) (τ : Typ) : m Unit :=
  if arity = 0 then pure ()
  else match τ with
    | .operator σs _ =>
      if σs.length = arity then pure ()
      else throw (.paramArityMismatch pos param arity σs.length)
    | _ => throw (.notAnOperatorType pos τ)

/-- `Γ ⊢ D ⊣ Γ'` — checks one declaration, returning its elaborated form alongside the bindings
`Γ'` adds over `Γ` (`[]` for `ASSUME`, which adds none). A `CONSTANT`/`VARIABLE` binding is never
a scheme (`Binding.isScheme := false`, even if its annotation happens to mention a `Typ.var`): a
`CONSTANT` is one fixed, if abstract, value, not a family of them to instantiate fresh per
reference. An `operator`/`function` definition's own returned binding *is* a scheme, any arity —
see each case below. -/
def checkDeclaration (moduleName : String) (d : SrcDecl) : m (Decl × List (String × Binding)) := match d with
  /-
     ∀ 1 ≤ i ≤ n, xᵢ ∉ Γ
    ───────────────────────────────────────────────────── [Constants]
     Γ ⊢ CONSTANTS x₁ : τ₁, …, xₙ : τₙ ⊣ Γ, x₁ : τ₁, …, xₙ : τₙ

    (`xᵢ ∉ Γ` deferred to the well-scopedness pass, not checked here.)
  -/
  | .constants xs => do
    let xs' ← xs.mapM λ (x, ann) ↦ return (x, ← requireAnnotation SourceSpan.placeholder s!"CONSTANT `{x}`" ann)
    return (.constants xs', xs'.map λ (x, τ) ↦ (x, { type := τ, origin := .module moduleName }))
  /-
    Same shape as [Constants].
  -/
  | .variables xs => do
    let xs' ← xs.mapM λ (x, ann) ↦ return (x, ← requireAnnotation SourceSpan.placeholder s!"VARIABLE `{x}`" ann)
    return (.variables xs', xs'.map λ (x, τ) ↦ (x, { type := τ, origin := .module moduleName }))
  /-
     Γ ⊢ e ⇓ Bool
    ─────────────────── [Assumption]
     Γ ⊢ ASSUME e ⊣ Γ

    (`ASSUME` has no name to bind, so checking one adds nothing to `Γ`.)
  -/
  | .assume e => do
    let e' ← checkExpr e .bool
    let e' ← resolveMVars e'
    return (.assume e', [])
  /-
     f ∉ Γ       Γ, x₁ : τ₁, …, xₙ : τₙ ⊢ e ⇓ τ
    ──────────────────────────────────────────────────────────────── [Operator definition]
     Γ ⊢ f(x₁, …, xₙ) : (τ₁, …, τₙ) ⇒ τ ≜ e ⊣ Γ, f : (τ₁, …, τₙ) ⇒ τ

    (No `f` in the context used to check `e` — operator definitions get no self-recursion.

    Zero-argument definitions (`f == e`, no parens at all) are checked against the annotation
    directly as the bare result type, not `() => τ`: a 0-ary definition is always referenced by
    bare name, never called like `Nodes()`.)
  -/
  | .operator ann f args body => do
    let τ ← requireAnnotation (posOf body) s!"operator `{f}`" ann
    match args, τ with
    | [], retTy => do
      let body' ← checkExpr body retTy
      let body' ← resolveMVars body'
      return (.operator retTy f args body', [(f, { type := retTy, isScheme := true, origin := .module moduleName })])
    | _, .operator paramTys retTy =>
      if paramTys.length ≠ args.length then
        throw (.arityMismatch (posOf body) paramTys.length args.length)
      else do
        (args.zip paramTys).forM λ ((x, arity), τᵢ) ↦ checkParamArity (posOf body) x arity τᵢ
        let bindings := args.map Prod.fst |>.zip paramTys
        let body' ← extendAll bindings (checkExpr body retTy)
        let body' ← resolveMVars body'
        return (.operator τ f args body', [(f, { type := τ, isScheme := true, origin := .module moduleName })])
    | _, _ => throw (.notAnOperatorType (posOf body) τ)
  /-
     f ∉ Γ       ∀ 1 ≤ i ≤ n, Γ ⊢ eᵢ ⇓ Set(τᵢ)       Γ, f : ⟨τ₁, …, τₙ⟩ → τ, x₁ : τ₁, …, xₙ : τₙ ⊢ e ⇓ τ
    ──────────────────────────────────────────────────────────────────────────────────────────────── [Function definition]
     Γ ⊢ f[x₁ ∈ e₁, …, xₙ ∈ eₙ] : ⟨τ₁, …, τₙ⟩ → τ ≜ e ⊣ Γ, f : ⟨τ₁, …, τₙ⟩ → τ

    (`f` *is* in the context checking `e`, unconditionally — function definitions get
    self-recursion for free, unlike operator definitions above.)
  -/
  | .function ann f args body => do
    let τ ← requireAnnotation (posOf body) s!"function `{f}`" ann
    match τ with
    | .function domTy retTy => do
      let τs ← match args.length, domTy with
        | 1, τ₁ => pure [τ₁]
        | n, .tuple τs => if τs.length = n then pure τs else throw (.arityMismatch (posOf body) τs.length n)
        | _, got => throw (.notATupleType (posOf body) got)
      let args' ← (args.zip τs).mapM λ ((x, e), τᵢ) ↦ do
        return (x, ← resolveMVars (← checkExpr e (.set τᵢ)))
      let bindings := (f, τ) :: (args.map Prod.fst |>.zip τs)
      let body' ← extendAll bindings (checkExpr body retTy)
      let body' ← resolveMVars body'
      return (.function τ f args' body', [(f, { type := τ, isScheme := true, origin := .module moduleName })])
    | _ => throw (.notAFunctionType (posOf body) τ)

/-- `Γ ⊢ D₁, …, Dₙ ⊣ Γ'` — checks a whole declaration list, threading `Γ` through each one.
Returns the accumulated `Γ' \ Γ` bindings alongside the checked declarations. -/
def checkDeclarations (moduleName : String) : List SrcDecl → m (List Decl × List (String × Binding))
  | [] => return ([], [])
  | d :: ds => do
    let (d', bindings) ← checkDeclaration moduleName d
    let (ds', restBindings) ← extendAllBindings bindings (checkDeclarations moduleName ds)
    return (d' :: ds', bindings ++ restBindings)
