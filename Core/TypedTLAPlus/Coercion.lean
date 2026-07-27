module

public import Core.TypedTLAPlus.Syntax

public section


/-!
  `Coercion` — a term-level witness of `<:`, realized as closed structural data, not an opaque
  `Expr → Expr` closure. Lives in `Core/` (not `Elaborator/`) so `CorePlusCal.Statement.receive`
  can carry a `Coercion` field without `Core/` depending on `Elaborator/`. `Elaborator/
  Subtyping.lean` owns everything *about* `Coercion` (the subtyping judgment, every coercion built
  from one); this file only owns the type itself, its discharge (`Coercion.apply`), and its `Repr`
  instance.

  Data rather than a closure because a `receive` statement's coercion (`Core/GuardedPlusCal/
  Syntax.lean`) must survive past `Typed2Computable`'s type change (`TypedTLAPlus.Expression` →
  `ComputableTLAPlus.Expression`) and discharge against the *later* type — a closure fixed at one
  concrete `Expr` type can't cross that boundary. Each constructor mirrors one of `Elaborator/
  Subtyping.lean`'s structural `<:` rules (or `tryAxioms`'s non-structural ones), carrying the type
  indices, field names, and nested sub-`Coercion`s that rule's discharge needs, plus any fresh
  binder name (`x`/`y`/`i`) generated via `MonadFresh` at construction time — baked in once, since
  a name fresh at construction stays fresh at discharge.

  Two structural recursions consume this data, one per concrete expression type: `Coercion.apply`
  (below) and `Coercion.applyComputable` (`Core/ComputableTLAPlus/Coercion.lean`).

  `Repr Coercion` is a placeholder: `-d dump-typecheck` renders any `receive`'s coercion as the literal
  string `"<coercion>"`.
-/

namespace TypedTLAPlus

/-- Checked TLA⁺ expressions at the checker's own output type — what a `Coercion` transforms. -/
abbrev Expr := Expression Typ

/--
  A coercion, witnessing `τ <: τ'` at the term level. `.id` is its own constructor rather than
  folded into a general case, so structural subtyping rules can cheaply detect "nothing to wrap"
  by pattern matching alone.
-/
inductive Coercion : Type
  /-- No wrapping needed — the source expression is already of the target type as-is. -/
  | id
  /-- `Str <: Seq(Int)` — `StrToSeq(e)`, the sequence of the string's Unicode code points. An
  intrinsic (`Origin.intrinsic`) rather than a member of `Sequences`: real TLA⁺ has no such
  operator, and only a coercion ever builds this node, so binding a name for it in
  `builtinContext` would invent surface syntax nothing needs. -/
  | strToSeq
  /-- `Seq(τ) <: Int → τ` — `[i ∈ 1..Len(e) ↦ e[i]]`. `i` a fresh name chosen at construction. -/
  | seqToFun (τ : Typ) (i : String)
  /-- `⟨τ,...,τ⟩ <: Seq(τ)` (uniform tuple only) — a tuple's arity `n` is static, so discharge is
  just a literal `.seq` of the `n` projected components. -/
  | tupleToSeq (n : Nat) (τ : Typ)
  /-- `Set(τ) <: Set(τ')` — `{coerce(x) : x ∈ e}`. `x` a fresh binder name. `τ'` is carried
  alongside the source `τ` because the `.map'` this discharges to records its codomain, and the
  coerced body's type is exactly `τ'`. -/
  | set (x : String) (τ τ' : Typ) (c : Coercion)
  /-- `⟨τ₁,...,τₙ⟩ <: ⟨τ₁',...,τₙ'⟩` — a new literal tuple, each component projected out of the
  source (tuples being encoded as unary functions from naturals) and coerced. `τs` is the *source*
  component list, needed because each projection discharges to a `.fnCall`, which records the type
  of its head — here the source tuple. -/
  | tuple (coes : List Coercion) (τs τs' : List Typ)
  /-- `[x₁:τ₁,...] <: [x₁:τ₁',...]` — a new literal record, each field projected out of the source
  and coerced. -/
  | record (fields : List (String × Coercion × Typ))
  /-- `τ₁ → τ₂ <: τ₁' → τ₂'` via a `CHOOSE`-based domain remap. `x`/`y` fresh binder names. `rng'`
  is carried for the same reason `set` carries `τ'`: the `.fn` this discharges to records its
  codomain, which is the *target* range, not the source's. -/
  | function (x y : String) (dom rng dom' rng' : Typ) (cDom cRng : Coercion)
  /-- Sequential composition — discharge `c₁` then `c₂` on the result. Realizes `<:`'s
  transitivity for `tryAxioms`' chained-axiom case (e.g. `Str <: Seq(Int) <: Int → Int`). -/
  | comp (c₁ c₂ : Coercion)

-- Structural recursion isn't visibly decreasing to Lean here (nested `List Coercion` occurrences,
-- same shape as `Expression.map`'s own note in `Core/TypedTLAPlus/Syntax.lean`) — `partial` until
-- revisited.
/-- Apply a coercion to an already-elaborated expression.

Every node built here is synthesized — none of it has source text of its own — but all of it
stands for the coerced expression `e`, so all of it is registered at `e`'s own span. Leaving a
synthesized node unregistered is not neutral: `posOf` cannot tell "never registered" from
"registered by something now dead" and answers with an unrelated node's span
(`Common/Position.lean`). A coercion inserted by subtyping can wrap most of an expression, so
skipping this loses positions across whole subtrees. -/
partial def Coercion.apply (c : Coercion) (e : Expr) : Expr :=
  let pos := posOf e
  match c with
  | .id => e
  | .strToSeq =>
    .opCall (.var "StrToSeq" (.operator [.str] (.seq .int)) .intrinsic @@ pos) [e] @@ pos
  | .seqToFun τ₀ i =>
    let range : Expr :=
      .opCall (.var ".." (.operator [.int, .int] (.set .int)) (.module "Naturals") @@ pos)
        [.nat "1" @@ pos,
         .opCall (.var "Len" (.operator [.seq τ₀] .int) (.module "Sequences") @@ pos) [e] @@ pos] @@ pos
    .fn i .int τ₀ range (.fnCall e (.seq τ₀) (.var i .int .binder @@ pos) @@ pos) @@ pos
  | .tupleToSeq n τ =>
    .seq ((List.range n).map λ i ↦
      .fnCall e (.tuple (List.replicate n τ)) (.nat (toString (i + 1)) @@ pos) @@ pos) τ @@ pos
  | .set x τ τ' c =>
    .map' (c.apply (.var x τ .binder @@ pos)) x τ τ' e @@ pos
  | .tuple coes τs τs' =>
    (.tuple <| ((List.range coes.length).zip coes).zip τs' |>.map λ ((i, c), τ'ᵢ) ↦
      (τ'ᵢ, c.apply (.fnCall e (.tuple τs) (.nat (toString (i + 1)) @@ pos) @@ pos))) @@ pos
  | .record fields =>
    (.record <| fields.map λ (name, c, τ'ᵢ) ↦ (τ'ᵢ, name, c.apply (.recordAccess e name @@ pos))) @@ pos
  | .function x y dom rng dom' rng' cDom cRng =>
    let domainExpr : Expr :=
      .opCall (.var "DOMAIN" (.operator [.function dom rng] (.set dom)) .intrinsic @@ pos) [e] @@ pos
    let newDomain : Expr := .map' (cDom.apply (.var x dom .binder @@ pos)) x dom dom' domainExpr @@ pos
    let eqTy : Typ := .operator [dom', dom'] .bool
    let recoveredArg : Expr :=
      .choose x dom (some domainExpr)
        (.opCall (.var "=" eqTy .intrinsic @@ pos)
          [cDom.apply (.var x dom .binder @@ pos), .var y dom' .binder @@ pos] @@ pos) @@ pos
    .fn y dom' rng' newDomain (cRng.apply (.fnCall e (.function dom rng) recoveredArg @@ pos)) @@ pos
  | .comp c₁ c₂ => c₂.apply (c₁.apply e)

/-- A placeholder rendering (module doc). -/
instance : Repr Coercion := ⟨fun _ _ => "<coercion>"⟩

end TypedTLAPlus

end
