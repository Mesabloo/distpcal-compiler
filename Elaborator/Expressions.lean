module

public import Elaborator.Subtyping
public import Elaborator.TypeUtils
public import Elaborator.Resolution
public import Elaborator.Context
public import Core.CoreTLAPlus.Syntax

public section

/-!
  Bidirectional expression checking: `checkExpr` (`Γ ⊢ e ⇓ τ`) and `inferExpr` (`Γ ⊢ e ⇑ τ`),
  turning a `CoreTLAPlus.Expression (Option TypedTLAPlus.Typ)` (binder annotations still the
  optional, user-written ones) into a `TypedTLAPlus.Expression TypedTLAPlus.Typ` (every binder now
  a resolved type). Each case carries the rule it implements as a comment: premises over a bar
  over the conclusion, tagged `[Rule Name]`.

  A few constructs synthesize only in certain cases:
  - `∅` is checking-only (`lub` over zero elements is undefined); a nonempty `{e1,...,en}`
    synthesizes `Set(lub(τ1,...,τn))`.
  - `IF`/`CASE` both synthesize `lub` over their branches.
  - `⟨e1,...,en⟩` dispatches by mode: checked against an expected `Seq(τ)` it uses the sequence
    constructor (each element checks against `τ`); everywhere else it synthesizes as a tuple. The
    elaborated term keeps the distinction (`.tuple` vs. `.seq`).
  - Unbounded `\A`/`\E` synthesize only when annotated with an explicit `x : τ`. Unbounded
    `CHOOSE` is always checking-only — hitting it in synthesis position is a real error
    (`TCError.cannotInferType`), not a missing-annotation one. Bounded quantification/choice
    (`x ∈ S`) always synthesizes, since `x`'s type comes from `S`.

  Out of scope, with no `CoreTLAPlus.Expression` constructor to match on: `LAMBDA`, `LET-IN`,
  weak/strong fairness (`WF_`/`SF_`), non-stuttering `⟨A⟩_e`, and temporal operators generally.
  `UNCHANGED`/`ENABLED`/prime `'`/`~>`/`-+>`/`[]`/`<>` desugar to plain operator calls, covered by
  the generic `OPERATOR CALL` rule once the builtin table gives each one a `Γ` entry. Only
  `stutter` (`[A]_e`) is a real constructor with its own case.

  `EXCEPT` supports an arbitrary-length path of record-field/index steps per update (`[f EXCEPT
  ![1].x[2] = v]`), implemented as one general recursive walk (`stepInto`/`checkExceptPath` below)
  rather than one case per path length.

  Polymorphism instantiation happens once, at `[Var]` below, not at `OPERATOR CALL`: a reference
  to a *scheme* `Γ` binding (`Elaborator/Monad.lean`'s `Binding.isScheme` — a top-level
  `operator`/`function` definition, not an ordinary binder) freshens every distinct `Typ.var` in
  its type into its own metavariable (`specializeType`, `Elaborator/TypeUtils.lean`) right there,
  whether or not that reference is later called. `OPERATOR CALL` just checks arguments against the
  callee's already-specialized type, resolving those metavariables incrementally through
  `Elaborator/Subtyping.lean`'s direction-aware solving.
-/

open TypedTLAPlus (Typ MVarId Expr)

/-- The checker's actual input: `CoreTLAPlus.Expression` at `α := Option Typ`, every binder's
annotation still the optional, user-written one rather than a resolved type. -/
abbrev SrcExpr := CoreTLAPlus.Expression (Option Typ)

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/-- `lub` folded across a nonempty list of types, erroring at `pos` on the first incomparable pair. -/
private def lubAll (pos : SourceSpan) : List Typ → m Typ
  | [] => throw (.ambiguousType pos)
  | τ :: τs => τs.foldlM (init := τ) λ acc τ' ↦ do
    match ← lub acc τ' with
    | some τ'' => return τ''
    | none => throw (.ambiguousType pos)

/-- Needed for the `partial def`s below to type-check at all (an arbitrary `m` isn't otherwise
known nonempty). -/
private local instance {α} [Inhabited α] : Inhabited (m α) := ⟨pure default⟩

mutual
  /--
    Indexing `e[e']` where `e`'s own type `τ` is already known — the shared core of function
    call/sequence access/tuple access. `CoreTLAPlus.Expression.fnCall` is a single constructor
    covering all three, so which rule applies is a runtime dispatch on `τ`'s own shape.
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

  /-- One `EXCEPT` path step (a path is a `List (String ⊕ SrcExpr)`: `.inl` a record field,
  `.inr` an index) applied to an already-known type `τ`. -/
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

  /-- The general `EXCEPT` path walk — recurses on the path, threading the type through each step
  via `stepInto`, and returns the type the final new value must be checked against alongside the
  elaborated (unchanged-shape) path. -/
  partial def checkExceptPath (pos : SourceSpan) (τ : Typ) :
      List (String ⊕ SrcExpr) → m (Typ × List (String ⊕ Expr))
    | [] => return (τ, [])
    | step :: rest => do
      let (τ', step') ← stepInto pos τ step
      let (final, rest') ← checkExceptPath pos τ' rest
      return (final, step' :: rest')

  /-- `Γ ⊢ e ⇓ τ` — see the module doc for exactly which constructs get a dedicated checking rule
  here versus falling to the generic `[Subtype]` fallback (everything else, including
  checking-mode use of every purely-synthesis rule `inferExpr` implements). -/
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
      | .failure => throw (.failedToConvertTypes pos (← resolveTypeMVarsForDisplay τ) (← resolveTypeMVarsForDisplay τ'))

  /-- `Γ ⊢ e ⇑ τ` — see the module doc for the precise checking/synthesis split. -/
  partial def inferExpr (e : SrcExpr) : m (Typ × Expr) := match_source e with
    /-
       x : τ ∈ Γ
      ─────────── [Var]
       Γ ⊢ x ⇑ τ
    -/
    | .var x, pos => do
      match (← readThe Context).get? x with
      | none => throw (.unboundVariable pos x)
      | some { type := τ, isScheme := true, origin } => do
        let τ' ← specializeType τ
        return (τ', .var x τ' origin @@ pos)
      | some { type := τ, isScheme := false, origin } => return (τ, .var x τ origin @@ pos)
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
          -- `τ` (hence `params`/`ret`) is already specialized fresh if the callee was a scheme
          -- binding — `inferExpr`'s `.var` case does that once, at the reference itself.
          let args' ← (params.zip args).mapM λ (τᵢ, argᵢ) ↦ checkExpr argᵢ τᵢ
          return (ret, .opCall e' args' @@ pos)
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
       Γ ⊢ e ⇑ τ       (general `EXCEPT` path walk)
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
       (no synthesis rule — unbounded `CHOOSE` is checking-only)
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
       (no synthesis rule — `lub` over zero elements is undefined)
    -/
    | .set [], pos =>
      throw (.cannotInferType pos
        "an empty set literal has no element type to synthesize — check it against an expected `Set(τ)` instead")
end

end
