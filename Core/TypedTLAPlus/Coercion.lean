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

  `Repr Coercion` is a placeholder: `-d dump-typed` renders any `receive`'s coercion as the literal
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
  /-- `Str <: Seq(Int)` — `"Str2Seq"` is a placeholder builtin name pending a real bundled-stub
  operator table, so it has no real owning module either. -/
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
/-- Apply a coercion to an already-elaborated expression. -/
partial def Coercion.apply : Coercion → Expr → Expr
  | .id, e => e
  | .strToSeq, e =>
    .opCall (.var "Str2Seq" (.operator [.str] (.seq .int)) (.module "Sequences")) [e]
  | .seqToFun τ₀ i, e =>
    let range : Expr := .opCall (.var ".." (.operator [.int, .int] (.set .int)) (.module "Naturals"))
      [.nat "1", .opCall (.var "Len" (.operator [.seq τ₀] .int) (.module "Sequences")) [e]]
    .fn i .int τ₀ range (.fnCall e (.seq τ₀) (.var i .int .binder))
  | .tupleToSeq n τ, e =>
    .seq ((List.range n).map λ i ↦
      .fnCall e (.tuple (List.replicate n τ)) (.nat (toString (i + 1)))) τ
  | .set x τ τ' c, e =>
    .map' (c.apply (.var x τ .binder)) x τ τ' e
  | .tuple coes τs τs', e =>
    .tuple <| ((List.range coes.length).zip coes).zip τs' |>.map λ ((i, c), τ'ᵢ) ↦
      (τ'ᵢ, c.apply (.fnCall e (.tuple τs) (.nat (toString (i + 1)))))
  | .record fields, e =>
    .record <| fields.map λ (name, c, τ'ᵢ) ↦ (τ'ᵢ, name, c.apply (.recordAccess e name))
  | .function x y dom rng dom' rng' cDom cRng, e =>
    let domainExpr : Expr := .opCall (.var "DOMAIN" (.operator [.function dom rng] (.set dom)) .intrinsic) [e]
    let newDomain : Expr := .map' (cDom.apply (.var x dom .binder)) x dom dom' domainExpr
    let eqTy : Typ := .operator [dom', dom'] .bool
    let recoveredArg : Expr :=
      .choose x dom (some domainExpr)
        (.opCall (.var "=" eqTy .intrinsic) [cDom.apply (.var x dom .binder), .var y dom' .binder])
    .fn y dom' rng' newDomain (cRng.apply (.fnCall e (.function dom rng) recoveredArg))
  | .comp c₁ c₂, e => c₂.apply (c₁.apply e)

/-- A placeholder rendering (module doc). -/
instance : Repr Coercion := ⟨fun _ _ => "<coercion>"⟩

end TypedTLAPlus

end
