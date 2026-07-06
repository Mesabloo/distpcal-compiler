import Elaborator.Subtyping
import Elaborator.TypeUtils
import Elaborator.Resolution
import Elaborator.Context
import Core.CoreTLAPlus.Syntax

/-!
  Bidirectional expression checking (§5.3, thesis §3.1.1–3.1.3.7, Figs. 3.1.1–3.1.6): `checkExpr`
  (`Γ ⊢ e ⇓ τ`) and `inferExpr` (`Γ ⊢ e ⇑ τ`), turning a `CoreTLAPlus.Expression (Option
  TypedTLAPlus.Typ)` (the checker's actual input — every binder's annotation still the optional,
  user-written one) into a `TypedTLAPlus.Expression TypedTLAPlus.Typ` (every binder now a real,
  resolved type). Each case below carries the thesis rule it implements, rendered the same way
  `~/Documents/distpcal-compiler/Checker/Typechecker/Expressions.lean` renders its own (a plain
  comment: premises over a bar over the conclusion, `[Rule Name]` tag) — but using the thesis's
  own notation (`Bool`/`Int`/`Str`/`Set(τ)`/…) rather than that file's alternate `𝔹`/`ℤ`/`𝕊`/`𝒫`
  shorthand, since the thesis is this project's authoritative spec (`CLAUDE.md`), not that sketch.

  **The checking/synthesis split is precise, not a mechanical pass over every figure** — several
  thesis rules are checking-only *until* `<:`/`lub` exist (§3.1.3.7, p. 13), at which point the
  thesis itself *replaces* the checking rule with a synthesis one, and *only* the final, replaced
  form is implemented here (checking-mode use of the construct still works through the generic
  `[Subtype]` fallback below, so nothing is lost):
  - **`ENUMERATION`/`Empty set`** — `∅` stays checking-only (`lub` over zero elements is
    undefined), but a nonempty `{e1,...,en}` now *synthesizes* `Set(lub(τ1,...,τn))`.
  - **`CONDITIONAL`/`CONDITIONAL CHOICE`** — both now synthesize `lub` over their branches
    (`IF`'s two, `CASE`'s `n` cases plus `OTHER` if present) rather than only checking.
  - **`Sequence constructor` vs. `Tuple constructor` — a genuine, deliberate non-conversion, not
    an oversight.** `⟨e1,...,en⟩` is one surface/`CoreTLAPlus` AST node (`.tuple`) serving two
    thesis rules: `Tuple constructor` (Fig. 3.1.3, synthesis) and `Sequence constructor` (Fig.
    3.1.6, checking-only *by the thesis's own explicit choice*, p. 13 — converting it to
    synthesis "would conflict with... Tuple constructor, where it would not be immediate and
    local what type to synthesize"). Dispatched by mode here: `checkExpr` against an expected
    `Seq(τ)` uses `Sequence constructor` (each element only needs to *check* against `τ`, more
    permissive than synthesizing one first); everywhere else uses `Tuple constructor`'s
    synthesis, producing `TypedTLAPlus.Expression.tuple`. The *elaborated* term keeps the
    distinction the two rules discovered (`.tuple` vs. the genuinely separate `.seq`,
    `Core/TypedTLAPlus/Syntax.lean`) rather than collapsing back to one shared shape.
  - **Unbounded `\A`/`\E` vs. unbounded `CHOOSE` — two different resolutions to the same
    can't-synthesize-the-bound-variable's-type problem, not the same treatment twice.** Unbounded
    quantification stays a *synthesis* rule requiring an explicit `x : τ` annotation (`@type`,
    already-parsed surface syntax) — checked for presence here, not newly invented. Unbounded
    `CHOOSE` instead stays **checking-only** always (no synthesis form the thesis ever
    introduces for it, precisely to *avoid* needing a binder annotation there) — hitting it in a
    synthesis position is a real error (`TCError.cannotInferType`), not a missing-annotation one.
  - Bounded quantification/choice (`x ∈ S`) never has this problem (`x`'s type synthesizes from
    `S`) and stays a plain synthesis rule throughout.

  **Genuinely out of scope, confirmed absent from `CoreTLAPlus.Expression` rather than merely
  unhandled here:** `LAMBDA` (designed but unimplemented, `PLAN.md` §9.16 — no AST constructor
  exists to match on); `LET-IN` (no constructor either — TLA⁺'s `LET`/`IN` doesn't survive
  desugaring as its own node); weak/strong fairness (`WF_`/`SF_`), non-stuttering `⟨A⟩_e`, and
  temporal operators generally have no surface syntax at all in this project *except* the ones
  that reduce to plain builtin-operator application during desugaring (`UNCHANGED`, `ENABLED`,
  prime `'`, `~>`, `-+>`, `[]`, `<>` all desugar to `opCall (.var "<name>") […]`,
  `Desugarer/TLAPlus.lean`) — those need **no dedicated case here at all**, the generic
  `OPERATOR CALL` rule below already covers them once the builtin table (§5.3 task 7,
  `Elaborator/Declarations.lean`) gives each one a real `Γ` entry. Only `stutter` (`[A]_e`) is a
  genuine `CoreTLAPlus.Expression` constructor and gets its own case.

  **`EXCEPT` is more general here than any single thesis figure rule.** `CoreTLAPlus.Expression
  .except`/`TypedTLAPlus.Expression.except` allow an arbitrary-length path of record-field/
  index steps per update (`[f EXCEPT ![1].x[2] = v]`), where the thesis only ever shows one-step
  paths (`RECORD OVERLOADING`/`TUPLE OVERLOADING`/`SEQUENCE OVERLOADING`/`FUNCTION OVERLOADING`,
  Fig. 3.1.3, each a single step). Implemented as one general recursive walk (`stepInto`/
  `checkExceptPath` below) applying whichever single-step rule fits at each step, rather than
  four separate one-step cases — the thesis's rules are the base cases of that walk, not
  something to special-case around.

  **Polymorphism instantiation (`SPECIALIZE`, Fig. 3.1.7) — implemented per `PLAN.md` §5.3/§2's
  deliberate deviation, not the thesis's literal rule.** `OPERATOR CALL` collects every `Typ.var`
  appearing in the callee's operator type, allocates one fresh metavariable per *distinct* name
  (`specializeOperator` below), and substitutes throughout before checking arguments — argument
  checking then resolves those metavariables incrementally through `Elaborator/Subtyping.lean`'s
  direction-aware solving, not through a separate substitution guess at the call site.
-/

open TypedTLAPlus (Typ MVarId Expr)

/-- The checker's actual input: `CoreTLAPlus.Expression` at `α := Option Typ`, every binder's
annotation still the optional, user-written one (`@type` comments, already parsed) rather than a
resolved type. -/
abbrev SrcExpr := CoreTLAPlus.Expression (Option Typ)

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/-- `lub` folded across a nonempty list of types, erroring at `pos` the moment two of them turn
out incomparable (`ENUMERATION`/`CONDITIONAL`/`CONDITIONAL CHOICE`'s shared synthesis pattern,
module doc). -/
private def lubAll (pos : SourceSpan) : List Typ → m Typ
  | [] => throw (.ambiguousType pos)
  | τ :: τs => τs.foldlM (init := τ) λ acc τ' ↦ do
    match ← lub acc τ' with
    | some τ'' => return τ''
    | none => throw (.ambiguousType pos)

/-- Needed for the `partial def`s below to type-check at all (an arbitrary `m` isn't otherwise
known nonempty) — same fix `Elaborator/Subtyping.lean` already uses for the same reason. -/
local instance : Inhabited (m Expr) := ⟨pure default⟩
private local instance : Inhabited (m (Typ × Expr)) := ⟨pure default⟩
private local instance : Inhabited (m (Typ × (String ⊕ Expr))) := ⟨pure default⟩
private local instance : Inhabited (m (Typ × List (String ⊕ Expr))) := ⟨pure default⟩

mutual
  /--
    Indexing `e[e']` where `e`'s own type `τ` is already known — the shared core of `FUNCTION
    CALL`/`SEQUENCE ACCESS`/`TUPLE ACCESS` (thesis Fig. 3.1.3): `CoreTLAPlus.Expression.fnCall`
    is a single constructor covering all three (records/tuples/sequences are encoded as
    functions, module doc of `Core/CoreTLAPlus/Syntax.lean`), so which rule actually applies is a
    runtime dispatch on `τ`'s own shape, not something the AST distinguishes structurally.
  -/
  partial def indexInto (pos : SourceSpan) (τ : Typ) (idx : SrcExpr) : m (Typ × Expr) := do
    match τ with
    /-
       Γ ⊢ e ⇑ τ₁ → τ       Γ ⊢ e' ⇓ τ₁
      ─────────────────────────────────── [Function call]
                Γ ⊢ e[e'] ⇑ τ
    -/
    | .function dom rng => return (rng, ← checkExpr idx dom)
    /-
       Γ ⊢ e₁ ⇑ Seq(τ)       Γ ⊢ e₂ ⇓ Int
      ──────────────────────────────────── [Sequence access]
                Γ ⊢ e₁[e₂] ⇑ τ
    -/
    | .seq elem => return (elem, ← checkExpr idx .int)
    /-
       Γ ⊢ e ⇑ ⟨τ₁, …, τᵢ, …, τₙ⟩
      ──────────────────────────── [Tuple access]
              Γ ⊢ e[i] ⇑ τᵢ
    -/
    | .tuple τs => match idx with
      | .nat n => match n.toNat? with
        | some i =>
          if h : 1 ≤ i ∧ i ≤ τs.length then
            return (τs[i - 1]'(by omega), .nat n)
          else throw (.invalidTupleIndex pos n τs.length)
        | none => throw (.invalidTupleIndex pos n τs.length)
      | _ => throw (.invalidTupleIndex pos "a non-literal expression" τs.length)
    | _ => throw (.notIndexable pos τ)

  /-- One `EXCEPT` path step (module doc: a path is a `List (String ⊕ SrcExpr)`, `.inl` a record
  field, `.inr` an index) applied to an already-known type `τ` — `.inl`'s own rule below is
  `RECORD OVERLOADING`'s field-lookup half; `.inr` reuses `indexInto` (`FUNCTION`/`SEQUENCE`/
  `TUPLE OVERLOADING`'s shared index-lookup half). -/
  partial def stepInto (pos : SourceSpan) (τ : Typ) : (String ⊕ SrcExpr) → m (Typ × (String ⊕ Expr))
    | .inl field => match τ with
      /-
         Γ ⊢ e ⇑ [x₀ : τ₀, …, xₙ : τₙ]       y = xᵢ
        ────────────────────────────────────────────── [Record field access]
                        Γ ⊢ e.y ⇑ τᵢ
      -/
      | .record fs => match fs.lookup field with
        | some τ' => return (τ', .inl field)
        | none => throw (.unknownField pos field (fs.map Prod.fst))
      | _ => throw (.notARecordType pos τ)
    | .inr idx => do
      let (τ', idx') ← indexInto pos τ idx
      return (τ', .inr idx')

  /-- The general `EXCEPT` path walk (module doc) — recurses on the path, threading the type
  through each step via `stepInto`, and returns the type the final new value must be checked
  against alongside the elaborated (unchanged-shape) path. Structurally recursive on the list on
  its own, but stuck with `partial` anyway — every definition in one `mutual` block must agree on
  it, and the rest of this group already needs it (`indexInto`'s own doc). -/
  partial def checkExceptPath (pos : SourceSpan) (τ : Typ) :
      List (String ⊕ SrcExpr) → m (Typ × List (String ⊕ Expr))
    | [] => return (τ, [])
    | step :: rest => do
      let (τ', step') ← stepInto pos τ step
      let (final, rest') ← checkExceptPath pos τ' rest
      return (final, step' :: rest')

  /-- `Γ ⊢ e ⇓ τ` (thesis §3.1.1, Figs. 3.1.1–3.1.6) — see the module doc for exactly which
  constructs get a dedicated checking rule here versus falling to the generic `[Subtype]`
  fallback (everything else, including checking-mode use of every purely-synthesis rule
  `inferExpr` implements). -/
  partial def checkExpr (e : SrcExpr) (τ : Typ) : m Expr := match_source (indices := [1]) e, τ with
    /-
      ─────────────── [Empty set]
       Γ ⊢ ∅ ⇓ Set(τ)
    -/
    | .set [], .set τ₀, pos => return .set [] τ₀ @@ pos
    /-
       Γ, x : τ ⊢ P ⇓ Bool
      ───────────────────── [Unbounded choice]
       Γ ⊢ CHOOSE x : P ⇓ τ
    -/
    | .choose x _ann none body, τ, pos => do
      let body' ← extend x τ (checkExpr body .bool)
      return .choose x τ none body' @@ pos
    /-
           ∀ 0 ≤ i ≤ n, Γ ⊢ eᵢ ⇓ τ
      ──────────────────────────────── [Sequence constructor]
          Γ ⊢ ⟨e₀, …, eₙ⟩ ⇓ Seq(τ)
    -/
    | .tuple es, .seq τ₀, pos => do
      let es' ← es.mapM (checkExpr · τ₀)
      return .seq es' τ₀ @@ pos
    /-
       Γ ⊢ e ⇑ τ'       τ' <: τ
      ─────────────────────────── [Subtype]
             Γ ⊢ e ⇓ τ
    -/
    | e, τ, pos => do
      let (τ', e') ← inferExpr e
      match ← subtype τ' τ with
      | .success coe => return coe.apply e' @@ pos
      | .pending n => return .mvar n e' @@ pos
      | .failure => throw (.failedToConvertTypes pos τ τ')

  /-- `Γ ⊢ e ⇑ τ` (thesis §3.1.1, Figs. 3.1.1–3.1.6) — see the module doc for the precise
  checking/synthesis split. -/
  partial def inferExpr (e : SrcExpr) : m (Typ × Expr) := match_source e with
    /-
       x : τ ∈ Γ
      ─────────── [Var]
       Γ ⊢ x ⇑ τ
    -/
    | .var x, pos => do
      match (← readThe Context).get? x with
      | some τ => return (τ, .var x τ @@ pos)
      | none => throw (.unboundVariable pos x)
    /-
      ────────────── [Number]
       Γ ⊢ n ⇑ Int
    -/
    | .nat n, pos => return (.int, .nat n @@ pos)
    /-
      ────────────── [String]
       Γ ⊢ s ⇑ Str
    -/
    | .str s, pos => return (.str, .str s @@ pos)
    /-
      ─────────────── [True]
       Γ ⊢ TRUE ⇑ Bool
    -/
    | .true, pos => return (.bool, .true @@ pos)
    /-
      ──────────────── [False]
       Γ ⊢ FALSE ⇑ Bool
    -/
    | .false, pos => return (.bool, .false @@ pos)
    /-
       Γ ⊢ e ⇑ (τ₁, …, τₙ) ⇒ τ       ∀ 1 ≤ i ≤ n, Γ ⊢ eᵢ ⇓ τᵢ
      ────────────────────────────────────────────────────────── [Operator call]
                          Γ ⊢ e(e₁, …, eₙ) ⇑ τ
    -/
    | .opCall e args, pos => do
      let (τ, e') ← inferExpr e
      match τ with
      | .operator params ret =>
        if params.length ≠ args.length then throw (.arityMismatch pos params.length args.length)
        else do
          let (params', ret') ← specializeOperator params ret
          let args' ← (params'.zip args).mapM λ (τᵢ, argᵢ) ↦ checkExpr argᵢ τᵢ
          -- `e'` still carries the polymorphic operator type it had in `Γ` (only `.var` stores
          -- one at all, module doc of `Core/TypedTLAPlus/Syntax.lean`) — retag it with the
          -- specialized one so the callee's own type agrees with `ret'`/`args'` rather than
          -- silently keeping the un-instantiated `Typ.var`s around in the elaborated term.
          let e'' := match e' with
            | .var x _ => .var x (.operator params' ret') @@ posOf e'
            | _ => e'
          return (ret', .opCall e'' args' @@ pos)
      | _ => throw (.notAnOperatorType pos τ)
    /-
       Γ ⊢ S ⇑ Set(τ)       Γ, x : τ ⊢ P ⇓ Bool
      ────────────────────────────────────────── [Set filter]
                Γ ⊢ {x ∈ S : P} ⇑ Set(τ)
    -/
    | .collect x _ann domE pred, pos => do
      let (domTy, domE') ← inferExpr domE
      match domTy with
      | .set τ => do
        let pred' ← extend x τ (checkExpr pred .bool)
        return (.set τ, .collect x τ domE' pred' @@ pos)
      | _ => throw (.notASetType pos domTy)
    /-
       Γ ⊢ S ⇑ Set(τ)       Γ, x : τ ⊢ e ⇑ τ'
      ────────────────────────────────────────── [Set map]
                Γ ⊢ {e : x ∈ S} ⇑ Set(τ')
    -/
    | .map' body x _ann domE, pos => do
      let (domTy, domE') ← inferExpr domE
      match domTy with
      | .set τ => do
        let (τ', body') ← extend x τ (inferExpr body)
        return (.set τ', .map' body' x τ domE' @@ pos)
      | _ => throw (.notASetType pos domTy)
    /-
       Γ ⊢ e ⇑ τ₁ → τ       Γ ⊢ e' ⇓ τ₁
      ─────────────────────────────────── [Function/Sequence/Tuple access]
                Γ ⊢ e[e'] ⇑ τ
    -/
    | .fnCall e idx, pos => do
      let (τ, e') ← inferExpr e
      let (resTy, idx') ← indexInto pos τ idx
      return (resTy, .fnCall e' idx' @@ pos)
    /-
       Γ ⊢ S ⇑ Set(τ)       Γ, x : τ ⊢ e ⇑ τ'
      ────────────────────────────────────────── [Function constructor]
                Γ ⊢ [x ∈ S ↦ e] ⇑ τ → τ'
    -/
    | .fn x _ann domE body, pos => do
      let (domTy, domE') ← inferExpr domE
      match domTy with
      | .set τ => do
        let (τ', body') ← extend x τ (inferExpr body)
        return (.function τ τ', .fn x τ domE' body' @@ pos)
      | _ => throw (.notASetType pos domTy)
    /-
       Γ ⊢ S ⇑ Set(τ)       Γ ⊢ T ⇑ Set(τ')
      ──────────────────────────────────────── [Function set]
              Γ ⊢ [S -> T] ⇑ Set(τ → τ')
    -/
    | .fnSet domE codE, pos => do
      let (domTy, domE') ← inferExpr domE
      let (codTy, codE') ← inferExpr codE
      match domTy, codTy with
      | .set τ, .set τ' => return (.set (.function τ τ'), .fnSet domE' codE' @@ pos)
      | .set _, _ => throw (.notASetType pos codTy)
      | _, _ => throw (.notASetType pos domTy)
    /-
                    ∀ 1 ≤ i ≤ n, Γ ⊢ eᵢ ⇑ τᵢ
      ────────────────────────────────────────────────── [Record constructor]
       Γ ⊢ [x₁ ↦ e₁, …, xₙ ↦ eₙ] ⇑ [x₁ : τ₁, …, xₙ : τₙ]
    -/
    | .record fields, pos => do
      let fields' ← fields.mapM λ (ann, x, e) ↦ do
        match ann with
        | some τ => return (τ, x, ← checkExpr e τ)
        | none => do
          let (τ, e') ← inferExpr e
          return (τ, x, e')
      return (.record (fields'.map λ (τ, x, _) ↦ (x, τ)), .record fields' @@ pos)
    /-
                    ∀ 1 ≤ i ≤ n, Γ ⊢ Sᵢ ⇑ Set(τᵢ)
      ────────────────────────────────────────────────────── [Record set]
       Γ ⊢ [x₁ : S₁, …, xₙ : Sₙ] ⇑ Set([x₁ : τ₁, …, xₙ : τₙ])
    -/
    | .recordSet fields, pos => do
      let fields' ← fields.mapM λ (_ann, x, e) ↦ do
        let (τ, e') ← inferExpr e
        match τ with
        | .set τ' => return (τ', x, e')
        | _ => throw (.notASetType pos τ)
      return (.set (.record (fields'.map λ (τ, x, _) ↦ (x, τ))), .recordSet fields' @@ pos)
    /-
       Γ ⊢ e ⇑ τ       (general `EXCEPT` path walk, module doc)
      ─────────────────────────────────────────────────────────── [Overloading]
                              Γ ⊢ e ⇑ τ
    -/
    | .except e updates, pos => do
      let (τ, e') ← inferExpr e
      let updates' ← updates.mapM λ (path, newVal) ↦ do
        let (finalTy, path') ← checkExceptPath pos τ path
        let newVal' ← checkExpr newVal finalTy
        return (path', newVal')
      return (τ, .except e' updates' @@ pos)
    /-
       Γ ⊢ e ⇑ [x₀ : τ₀, …, xₙ : τₙ]       y = xᵢ
      ────────────────────────────────────────────── [Record field access]
                      Γ ⊢ e.y ⇑ τᵢ
    -/
    | .recordAccess e x, pos => do
      let (τ, e') ← inferExpr e
      match τ with
      | .record fs => match fs.lookup x with
        | some τ' => return (τ', .recordAccess e' x @@ pos)
        | none => throw (.unknownField pos x (fs.map Prod.fst))
      | _ => throw (.notARecordType pos τ)
    /-
       ∀ 1 ≤ i ≤ n, Γ ⊢ eᵢ ⇑ τᵢ
      ──────────────────────────── [Tuple constructor]
       Γ ⊢ ⟨e₁, …, eₙ⟩ ⇑ ⟨τ₁, …, τₙ⟩
    -/
    | .tuple es, pos => do
      let pairs ← es.mapM inferExpr
      return (.tuple (pairs.map Prod.fst), .tuple pairs @@ pos)
    /-
       Γ ⊢ e₁ ⇓ Bool       Γ ⊢ e₂ ⇑ τ₂       Γ ⊢ e₃ ⇑ τ₃
      ───────────────────────────────────────────────────── [Conditional]
               Γ ⊢ IF e₁ THEN e₂ ELSE e₃ ⇑ lub(τ₂, τ₃)
    -/
    | .if c t f, pos => do
      let c' ← checkExpr c .bool
      let (τt, t') ← inferExpr t
      let (τf, f') ← inferExpr f
      let τ ← lubAll pos [τt, τf]
      return (τ, .if c' t' f' @@ pos)
    /-
       ∀ 1 ≤ i ≤ n, Γ ⊢ pᵢ ⇓ Bool       ∀ 1 ≤ i ≤ n, Γ ⊢ eᵢ ⇑ τᵢ       Γ ⊢ eₙ₊₁ ⇑ τₙ₊₁
      ──────────────────────────────────────────────────────────────────────────────── [Conditional choice]
             Γ ⊢ CASE p₁ -> e₁ [] … [] pₙ -> eₙ [] OTHER -> eₙ₊₁ ⇑ lub(τ₁, …, τₙ₊₁)
    -/
    | .case branches other, pos => do
      let branches' ← branches.mapM λ (p, e) ↦ do
        let p' ← checkExpr p .bool
        let (τ, e') ← inferExpr e
        return (τ, p', e')
      let other' ← other.mapM inferExpr
      let τ ← lubAll pos (branches'.map (·.1) ++ (other'.map Prod.fst).toList)
      return (τ, .case (branches'.map λ (_, p, e) ↦ (p, e)) (other'.map Prod.snd) @@ pos)
    /-
       Γ ⊢ e ⇑ τ       Γ ⊢ A ⇓ Bool
      ────────────────────────────── [Stuttering]
              Γ ⊢ [A]_e ⇑ Bool
    -/
    | .stutter e a, pos => do
      let (_, e') ← inferExpr e
      let a' ← checkExpr a .bool
      return (.bool, .stutter e' a' @@ pos)
    /-
       Γ ⊢ S ⇑ Set(τ)       Γ, x : τ ⊢ P ⇓ Bool
      ────────────────────────────────────────── [Bounded quantification]
                Γ ⊢ ∫ x ∈ S : P ⇑ Bool
    -/
    | .forall x _ann (some domE) body, pos => do
      let (domTy, domE') ← inferExpr domE
      match domTy with
      | .set τ => do
        let body' ← extend x τ (checkExpr body .bool)
        return (.bool, .forall x τ (some domE') body' @@ pos)
      | _ => throw (.notASetType pos domTy)
    /-
       Γ, x : τ ⊢ P ⇓ Bool
      ───────────────────────── [Unbounded quantification]
       Γ ⊢ ∫ x : τ : P ⇑ Bool
    -/
    | .forall x ann none body, pos => do
      match ann with
      | some τ => do
        let body' ← extend x τ (checkExpr body .bool)
        return (.bool, .forall x τ none body' @@ pos)
      | none => throw (.expectedTypeAnnotation pos "unbounded ∀")
    | .exists x _ann (some domE) body, pos => do
      let (domTy, domE') ← inferExpr domE
      match domTy with
      | .set τ => do
        let body' ← extend x τ (checkExpr body .bool)
        return (.bool, .exists x τ (some domE') body' @@ pos)
      | _ => throw (.notASetType pos domTy)
    | .exists x ann none body, pos => do
      match ann with
      | some τ => do
        let body' ← extend x τ (checkExpr body .bool)
        return (.bool, .exists x τ none body' @@ pos)
      | none => throw (.expectedTypeAnnotation pos "unbounded ∃")
    /-
       Γ, x : τ ⊢ P ⇓ Bool
      ───────────────────────── [Temporal quantification]
       Γ ⊢ ∫ x : τ : P ⇑ Bool
    -/
    | .fforall x ann body, pos => do
      match ann with
      | some τ => do
        let body' ← extend x τ (checkExpr body .bool)
        return (.bool, .fforall x τ body' @@ pos)
      | none => throw (.expectedTypeAnnotation pos "temporal quantification (\\AA/\\EE)")
    | .eexists x ann body, pos => do
      match ann with
      | some τ => do
        let body' ← extend x τ (checkExpr body .bool)
        return (.bool, .eexists x τ body' @@ pos)
      | none => throw (.expectedTypeAnnotation pos "temporal quantification (\\AA/\\EE)")
    /-
       Γ ⊢ S ⇑ Set(τ)       Γ, x : τ ⊢ P ⇓ Bool
      ────────────────────────────────────────── [Bounded choice]
                Γ ⊢ CHOOSE x ∈ S : P ⇑ τ
    -/
    | .choose x _ann (some domE) body, pos => do
      let (domTy, domE') ← inferExpr domE
      match domTy with
      | .set τ => do
        let body' ← extend x τ (checkExpr body .bool)
        return (τ, .choose x τ (some domE') body' @@ pos)
      | _ => throw (.notASetType pos domTy)
    /-
       (no synthesis rule — thesis deliberately keeps unbounded `CHOOSE` checking-only, module doc)
    -/
    | .choose _ _ none _, pos =>
      throw (.cannotInferType pos
        "unbounded CHOOSE has no synthesis rule — it can only be checked against an expected type")
    /-
       ∀ 1 ≤ i ≤ n, Γ ⊢ eᵢ ⇑ τᵢ
      ──────────────────────────────────── [Enumeration]
       Γ ⊢ {e₁, …, eₙ} ⇑ Set(lub(τ₁, …, τₙ))
    -/
    | .set (e₀ :: es), pos => do
      let pairs ← (e₀ :: es).mapM inferExpr
      let τ ← lubAll pos (pairs.map Prod.fst)
      return (.set τ, .set (pairs.map Prod.snd) τ @@ pos)
    /-
       (no synthesis rule — `lub` over zero elements is undefined, thesis p. 13)
    -/
    | .set [], pos =>
      throw (.cannotInferType pos
        "an empty set literal has no element type to synthesize — check it against an expected `Set(τ)` instead")
end
