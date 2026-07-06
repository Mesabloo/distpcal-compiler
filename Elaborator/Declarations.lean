import Elaborator.Expressions

/-!
  Declaration/module-level checking (§5.3, thesis Figs. 3.1.9/3.1.10): `checkDeclaration`/
  `checkDeclarations`, threading `Γ` across `CONSTANTS`/`VARIABLES`/`ASSUME`/operator-definition/
  function-definition, plus `builtinContext` — a minimal `Γ₀` prelude of core TLA⁺ operators,
  since real programs (and `Elaborator/Subtyping.lean`'s own `DOMAIN`/`Len`/`..`/`=` coercion
  helpers) need *some* of these bound before any user declaration is checked, and the project
  owner's own review of this file's scope confirmed seeding a small hardcoded set now rather than
  deferring it entirely (unlike `Driver/Modules.lean`'s `builtinModules`, which stays genuinely
  empty until real test input needs a specific `EXTENDS`-gated standard-module operator).

  **Every declaration's own expressions are closed out via `Elaborator/Expressions.lean`'s
  `resolveMVars` before `checkDeclaration` returns** (`PLAN.md` §5.3's single end-of-check
  defaulting point — flagged by the project owner as missing from the checker entirely until this
  session's own fix): a metavariable `specializeOperator` freshens during one declaration's
  checking must not leak into the next declaration's `Γ` still unresolved, so `ASSUME`'s
  expression, an operator definition's body, and a function definition's domain expressions and
  body each get `resolveMVars`-ed individually, right where they're produced.

  **`THEOREM`/`RECURSIVE` — both out of scope, for different reasons.** `THEOREM` isn't a
  violation to special-case around: it has no `CoreTLAPlus.Declaration` constructor at all (surface
  parser doesn't recognize it either), so there's nothing here to match on. `RECURSIVE` is a real
  absence too (`PLAN.md` §9.9, §2) — consequently the thesis's own `Γ|Δ ⊢ D ⊣ Γ'|Δ'` judgment
  simplifies to just `Γ ⊢ D ⊣ Γ'` throughout this file: `Δ` (the "marked-recursive" tracking
  context) never gets populated by anything, since the one declaration that ever writes to it
  (`RECURSIVE`) doesn't exist here, so every rule below that thesis Fig. 3.1.9 writes with a `Δ` on
  both sides is implemented with no `Δ` at all — not an approximation, a faithful reflection of
  `Δ` always being empty.

  **A consequence of no `RECURSIVE`: operator definitions get no self- or mutual recursion.**
  Fig. 3.1.9's `OPERATOR DEFINITION` rule already excludes `f` itself from the context used to check
  `e` (`(Γ ∪ Δ), x₁:τ₁,...,xₙ:τₙ ⊢ e ⇓ τ` — no `f` on the left) *unless* `f : τ' ∈ Δ` from an earlier
  `RECURSIVE` mark; with `Δ` always empty here, that's simply never available, so an operator
  definition's own name is never in scope for its own body.

  **Function definitions are different: they get self-recursion unconditionally, no `RECURSIVE`
  needed.** Fig. 3.1.9's `FUNCTION DEFINITION` rule checks `e` against `Γ, f : ⟨τ₁,...,τₙ⟩ → τ,
  x₁:τ₁,...,xₙ:τₙ` — `f` *is* already in scope, unconditionally, matching ordinary TLA⁺ recursive
  function definitions (`f[x ∈ S] == ... f[x - 1] ...`) and the thesis's own prose justification
  right after the figure: annotations are mandatory on every function definition (even non-recursive
  ones) specifically *because* `f` needs a known type before `e` is checked, on pain of circularity
  otherwise. This is why `requireAnnotation` below is unconditional for both operator and function
  definitions, not just the recursive case — there is no non-recursive case to special-case, since
  nothing here can tell in advance whether `e` actually uses `f`.

  **Single- vs. multi-argument function definitions — a deliberate departure from the figure's
  literal `⟨τ₁,...,τₙ⟩ → τ` notation, forced by this project's own encoding, not a new figure.**
  `CoreTLAPlus.Expression.fnCall`'s own doc: a multi-index *call* `f[e₁,...,eₙ]` (`n > 1`) is
  already desugared to the single-index `f[⟨e₁,...,eₙ⟩]` by the time this checker ever sees it, but
  a multi-argument function *definition* `f[x₁ ∈ e₁,...,xₙ ∈ eₙ]` is **not** correspondingly
  pre-tupled (`Desugarer/TLAPlus.lean`'s `Declaration.desugar`'s `.function` case threads `ps`
  through unchanged) — so this file has to reconcile the two directly: `n = 1` gives a domain type
  of `τ₁` itself (an ordinary unary function, matching the single-index call it's actually indexed
  by); `n > 1` requires the annotation's domain to be `Typ.tuple [τ₁,...,τₙ]` (matching the
  pre-tupled multi-index call site). Getting this wrong would make a real multi-arg function
  definition never callable through `CoreTLAPlus.Expression.fnCall`'s own single-index encoding.

  **`builtinContext` now only carries what's genuinely `EXTENDS`-independent** (resolving `PLAN.md`
  §9.19): equality, the boolean connectives, and core set theory (`\in`/`\subseteq`/`\cup`/`\cap`/
  `\`/`DOMAIN`) — the operators the thesis itself treats as pre-existing in `Γ` with no `EXTENDS` of
  any kind. Arithmetic (`+`/`-`/`-.`/`*`/`<`/`>`/`=<`/`>=`/`..`/`Nat`) and the sequence operators
  (`Len`/`Head`/`Tail`/`Append`) — properly `Naturals`-only and `Sequences`-only (respectively) in
  real TLA⁺ — now live as real declarations in `Driver/Modules.lean`'s `builtinModules["Naturals"]`/
  `builtinModules["Sequences"]` entries instead, so a module only sees them via an actual `EXTENDS
  Naturals`/`EXTENDS Sequences` (`Elaborator/Elaborator.lean`'s `Γ₀`-merge already threads a
  dependency's own declarations in this way — `Driver/Modules.lean`'s `compileModule` doc). **Not
  included**: `Str2Seq` (`Elaborator/Subtyping.lean`'s placeholder coercion helper)
  needs no entry here at all — every use of it is a term the coercion itself constructs directly
  (`.var "Str2Seq" (.operator [.str] (.seq .int))`, already fully typed at the construction site),
  never a name any checked *source* expression looks up through `Γ`. Unary minus (`-x`, parsed
  exactly as before — no surface-syntax change) gets its own canonical spelling, `"-."`
  (`Desugarer/TLAPlus.lean`'s `PrefixOperator.canonicalName`, resolving `PLAN.md` §9.18 — the same
  disambiguating trick "Specifying Systems" itself uses), so it can carry its own entry, distinct
  from binary `-`'s, in `Driver/Modules.lean`'s `Naturals` declarations rather than here.
-/

open TypedTLAPlus (Typ)

/-- The checker's actual input for one declaration: `CoreTLAPlus.Declaration` at `α := Option Typ`,
matching `Elaborator/Expressions.lean`'s `SrcExpr` convention. -/
abbrev SrcDecl := CoreTLAPlus.Declaration (Option Typ)

/-- The checker's output for one declaration. -/
abbrev Decl := TypedTLAPlus.Declaration Typ

/--
  `Γ₀` — the minimal builtin prelude (module doc). Every entry uses `Typ.var` for whatever's
  meant to be generic (`Elaborator/Expressions.lean`'s `specializeOperator` already freshens every
  distinct `Typ.var` into its own metavariable at each call site, so this needs no special
  polymorphism support beyond what `OPERATOR CALL` already does).
-/
def builtinContext : Context := Std.HashMap.ofList [
  -- Equality (thesis: `Γ` is assumed to already carry these).
  ("=", .operator [.var "a", .var "a"] .bool),
  ("/=", .operator [.var "a", .var "a"] .bool),
  -- Boolean connectives.
  ("/\\", .operator [.bool, .bool] .bool),
  ("\\/", .operator [.bool, .bool] .bool),
  ("=>", .operator [.bool, .bool] .bool),
  ("<=>", .operator [.bool, .bool] .bool),
  ("\\neg", .operator [.bool] .bool),
  -- Sets.
  ("\\in", .operator [.var "a", .set (.var "a")] .bool),
  ("\\notin", .operator [.var "a", .set (.var "a")] .bool),
  ("\\subseteq", .operator [.set (.var "a"), .set (.var "a")] .bool),
  ("\\cup", .operator [.set (.var "a"), .set (.var "a")] (.set (.var "a"))),
  ("\\cap", .operator [.set (.var "a"), .set (.var "a")] (.set (.var "a"))),
  ("\\", .operator [.set (.var "a"), .set (.var "a")] (.set (.var "a"))),
  ("DOMAIN", .operator [.function (.var "a") (.var "b")] (.set (.var "a"))),
]

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/-- A higher-order parameter's declared arity (`Nat`, from `List (String × Nat)` — `0` for `x`,
`k` for `F(_,...,_)` with `k` `_`s) must match its annotated type's own operator-arity, once one
is known — thesis Fig. 3.1.9's `OPERATOR DEFINITION` writes every parameter type as a plain `τᵢ`,
but doesn't itself need to reconcile this against a separate arity, since its own grammar has no
notion of a parameter's declared arity independent of its type; this project's own AST does (the
parser counting `_`s), so checking the two agree is this file's own addition, not the thesis's
rule. Arity `0` needs no check at all — any type is a legitimate ordinary-value parameter,
including an operator-shaped one (thesis p. 14's own `CONSTANT F(_,_) : (τ1,τ2) ⇒ τ` sits at
arity `0` from a parameter's perspective, and is exactly this permissive case). -/
private def checkParamArity (pos : SourceSpan) (param : String) (arity : Nat) (τ : Typ) : m Unit :=
  if arity = 0 then pure ()
  else match τ with
    | .operator σs _ =>
      if σs.length = arity then pure ()
      else throw (.paramArityMismatch pos param arity σs.length)
    | _ => throw (.notAnOperatorType pos τ)

/-- `Γ ⊢ D ⊣ Γ'` (thesis Fig. 3.1.9, `Δ`-free per the module doc) — checks one declaration,
returning its elaborated form alongside the bindings `Γ'` adds over `Γ` (`[]` for `ASSUME`, which
adds none). -/
def checkDeclaration (d : SrcDecl) : m (Decl × List (String × Typ)) := match d with
  /-
     ∀ 1 ≤ i ≤ n, xᵢ ∉ Γ
    ───────────────────────────────────────────────────── [Constants]
     Γ ⊢ CONSTANTS x₁ : τ₁, …, xₙ : τₙ ⊣ Γ, x₁ : τ₁, …, xₙ : τₙ

    (`xᵢ ∉ Γ` deferred to the well-scopedness pass, `PLAN.md` §5.3/§2 — see that decision's own
    justification for why shadowing checks live there, not here.)
  -/
  | .constants xs => do
    let xs' ← xs.mapM λ (x, ann) ↦ return (x, ← requireAnnotation SourceSpan.placeholder s!"CONSTANT `{x}`" ann)
    return (.constants xs', xs')
  /-
    Same shape as [Constants].
  -/
  | .variables xs => do
    let xs' ← xs.mapM λ (x, ann) ↦ return (x, ← requireAnnotation SourceSpan.placeholder s!"VARIABLE `{x}`" ann)
    return (.variables xs', xs')
  /-
     Γ ⊢ e ⇓ Bool
    ─────────────────── [Assumption]
     Γ ⊢ ASSUME e ⊣ Γ

    (This project's own `ASSUME` has no name to bind — `CoreTLAPlus.Declaration.assume`'s own
    doc — so unlike the thesis's named `ASSUME x ≜ e`, checking one adds nothing to `Γ`.)
  -/
  | .assume e => do
    let e' ← checkExpr e .bool
    let e' ← resolveMVars e'
    return (.assume e', [])
  /-
     f ∉ Γ       Γ, x₁ : τ₁, …, xₙ : τₙ ⊢ e ⇓ τ
    ──────────────────────────────────────────────────────────────── [Operator definition]
     Γ ⊢ f(x₁, …, xₙ) : (τ₁, …, τₙ) ⇒ τ ≜ e ⊣ Γ, f : (τ₁, …, τₙ) ⇒ τ

    (No `f : τ' ∈ Δ` reconciliation premise — `Δ` is always empty here, module doc; no `f` in the
    context used to check `e` either, for the same reason: no `RECURSIVE` to have put it there.)

    **Zero-argument definitions (`f == e`, no parens at all) are checked against the annotation
    directly as the bare result type, not `() => τ`.** Found via hand-verification against
    `LamportMutex3.tla`'s `(* @type: Set(Int); *) Nodes == 1 .. N` — a real 0-ary definition is
    always referenced by bare name (`Nodes`, via `[Var]`), never called like `Nodes()`, so `f`'s
    own Γ binding is the plain value type, matching how every existing fixture actually writes
    these annotations (never an operator-shaped one for a 0-ary definition).
  -/
  | .operator ann f args body => do
    let τ ← requireAnnotation (posOf body) s!"operator `{f}`" ann
    match args, τ with
    | [], retTy => do
      let body' ← checkExpr body retTy
      let body' ← resolveMVars body'
      return (.operator retTy f args body', [(f, retTy)])
    | _, .operator paramTys retTy =>
      if paramTys.length ≠ args.length then
        throw (.arityMismatch (posOf body) paramTys.length args.length)
      else do
        (args.zip paramTys).forM λ ((x, arity), τᵢ) ↦ checkParamArity (posOf body) x arity τᵢ
        let bindings := args.map Prod.fst |>.zip paramTys
        let body' ← extendAll bindings (checkExpr body retTy)
        let body' ← resolveMVars body'
        return (.operator τ f args body', [(f, τ)])
    | _, _ => throw (.notAnOperatorType (posOf body) τ)
  /-
     f ∉ Γ       ∀ 1 ≤ i ≤ n, Γ ⊢ eᵢ ⇓ Set(τᵢ)       Γ, f : ⟨τ₁, …, τₙ⟩ → τ, x₁ : τ₁, …, xₙ : τₙ ⊢ e ⇓ τ
    ──────────────────────────────────────────────────────────────────────────────────────────────── [Function definition]
     Γ ⊢ f[x₁ ∈ e₁, …, xₙ ∈ eₙ] : ⟨τ₁, …, τₙ⟩ → τ ≜ e ⊣ Γ, f : ⟨τ₁, …, τₙ⟩ → τ

    (`f` *is* in the context checking `e`, unconditionally — module doc on why function
    definitions get self-recursion for free, unlike operator definitions above. `n = 1`/`n > 1`
    domain-shape reconciliation — module doc.)
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
      return (.function τ f args' body', [(f, τ)])
    | _ => throw (.notAFunctionType (posOf body) τ)

/-- `Γ ⊢ D₁, …, Dₙ ⊣ Γ'` — the accumulation half of thesis Fig. 3.1.10 (module typing threads its
declarations through exactly this, on both sides of the embedded PlusCal algorithm). Returns the
accumulated `Γ' \ Γ` bindings alongside the checked declarations — `Elaborator/Elaborator.lean`
(§5.3 task 10) needs them to keep extending `Γ` into the embedded PlusCal algorithm and the
second `declarations₂` list, the same way `Elaborator/PlusCal.lean`'s own `checkVariables`/
`checkPlusCalDeclarations` already expose theirs for exactly this reason. Structurally recursive
on the list — no `partial` needed, unlike `Elaborator/Expressions.lean`'s mutual group. -/
def checkDeclarations : List SrcDecl → m (List Decl × List (String × Typ))
  | [] => return ([], [])
  | d :: ds => do
    let (d', bindings) ← checkDeclaration d
    let (ds', restBindings) ← extendAll bindings (checkDeclarations ds)
    return (d' :: ds', bindings ++ restBindings)
