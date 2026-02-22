import PlusCalCompiler.CoreTLAPlus.Syntax
import PlusCalCompiler.TypedTLAPlus.Syntax
import PlusCalCompiler.Passes.Typechecker.Monad
import PlusCalCompiler.Passes.Typechecker.Convertibility

section Expressions
  variable {m : Type → Type} [MonadTC m] [Monad m]

  open CoreTLAPlus

  def makeFunctionType (τs : List Typ) (τ : Typ) : Typ := .function (.tuple τs) τ

  def makeOperatorType (τs : List Typ) (τ : Typ) : Typ := .operator τs τ

  /-
    In most cases, introduction rules are inference rules, and elimination rules are checking rules.
  -/
  mutual
    def checkExpr (e : Expression Typ) (τ : Typ) : m (TypedTLAPlus.Expression Typ) :=
      match_source (indices := [1]) e, τ with
      /-
         ∀ 0 ≤ i ≤ n, Γ ⊢ eᵢ ⇐ τ
        ────────────────────────── [Set-I]
          Γ ⊢ {e₀, …, eₙ} ⇐ 𝒫(τ)
      -/
      | .set es, .set τ, pos => do
        let es' ← es.attach.mapM λ ⟨e, _⟩ ↦ checkExpr e τ
        return .set es' τ @@ pos
      /-
          Γ ⊢ e ⇐ 𝔹
        ───────────── [¬-I]
         Γ ⊢ ¬e ⇐ 𝔹
      -/
      | .prefix .«¬» e, .bool, pos => do
        let e' ← checkExpr e .bool
        return .prefix .«¬» e' @@ pos
      /-
          Γ ⊢ e ⇐ ℤ
        ───────────── [--I]
         Γ ⊢ -e ⇐ ℤ
      -/
      | .prefix .«-» e, .int, pos => do
        let e' ← checkExpr e .int
        return .prefix .«-» e' @@ pos
      /-
         Γ ⊢ e₁ ⇐ 𝒫(τ)       Γ ⊢ e₂ ⇐ 𝒫(τ)
        ───────────────────────────────────── [∪-I]
                Γ ⊢ e₁ ∪ e₂ ⇐ 𝒫(τ)
      -/
      | .infix e₁ .«∪» e₂, .set τ, pos => do
        let e₁' ← checkExpr e₁ (.set τ)
        let e₂' ← checkExpr e₂ (.set τ)
        return .infix e₁' .«∪» e₂' @@ pos
      /-
         Γ ⊢ e₁ ⇐ ℤ       Γ ⊢ e₂ ⇐ ℤ
        ─────────────────────────────── [+-I]
                Γ ⊢ e₁ + e₂ ⇐ ℤ
      -/
      | .infix e₁ .«+» e₂, .int, pos => do
        let e₁' ← checkExpr e₁ .int
        let e₂' ← checkExpr e₂ .int
        return .infix e₁' .«+» e₂' @@ pos
      /-
         Γ ⊢ e₁ ⇐ ℤ       Γ ⊢ e₂ ⇐ ℤ
        ─────────────────────────────── [--I]
                Γ ⊢ e₁ - e₂ ⇐ ℤ
      -/
      | .infix e₁ .«-» e₂, .int, pos => do
        let e₁' ← checkExpr e₁ .int
        let e₂' ← checkExpr e₂ .int
        return .infix e₁' .«-» e₂' @@ pos
      /-
         ∀ 0 ≤ i ≤ n, Γ ⊢ eᵢ ⇒ τᵢ        Γ ⊢ e : τ₀ × … × τₙ → τ
        ────────────────────────────────────────────────────────── [Fun-E]
                            Γ ⊢ e[e₀, …, eₙ] ⇐ τ
      -/
      | .funcall e es, τ, pos => do
        let (τs, es') ← List.unzip <$> es.attach.mapM λ ⟨e, _⟩ ↦ inferExpr e
        let e' ← checkExpr e (makeFunctionType τs τ)
        return .funcall e' es' @@ pos
      /-
             ∀ 0 ≤ i ≤ n, Γ ⊢ eᵢ ⇐ τ
        ──────────────────────────────── [Seq-I]
         Γ ⊢ Seq(⟨e₀, …, eₙ⟩) : Seq(τ)
      -/
      | .seq es, .seq τ, pos => do
        let es' ← es.attach.mapM λ ⟨e, _⟩ ↦ checkExpr e τ
        return .seq es' τ @@ pos
      /-
         ∀ 0 ≤ i ≤ n, Γ ⊢ eᵢ ⇒ τᵢ        Γ ⊢ e ⇒ (τ₀, …, τₙ) ⇒ τ
        ────────────────────────────────────────────────────────── [Fun-E]
                            Γ ⊢ e[e₀, …, eₙ] ⇐ τ
      -/
      | .opcall e es, τ, pos => do
        let (τs, es') ← List.unzip <$> es.attach.mapM λ ⟨e, _⟩ ↦ inferExpr e
        let e' ← checkExpr e (makeOperatorType τs τ)
        return .opcall e' es' @@ pos
      /-
         Γ ⊢ e ⇒ τ'       τ ≅ τ'
        ────────────────────────── [Conv]
               Γ ⊢ e ⇐ τ
      -/
      | e, τ, pos => do
        let (τ', e') ← inferExpr e
        unless τ ≅ τ' do
          throw (.failedToConvertTypes τ τ' pos)
        return e' @@ pos
    termination_by e
    decreasing_by
      all: try decreasing_trivial

    def inferExpr (e : Expression Typ) : m (Typ × TypedTLAPlus.Expression Typ) :=
      match_source e with
      /-
         v : τ ∈ Γ
        ─────────── [Var-I]
         Γ ⊢ v ⇒ τ
      -/
      | .var v, pos => lookupDecl v >>= λ
        | .some τ => pure (τ, .var v τ @@ pos)
        | .none => throw (.unboundVariable v pos)
      /-
        ──────────── [Nat-I]
         Γ ⊢ n ⇒ ℤ
      -/
      | .nat n, pos => pure (.int, .nat n @@ pos)
      /-
        ──────────── [Str-I]
         Γ ⊢ s ⇒ 𝕊
      -/
      | .str s, pos => pure (.str, .str s @@ pos)
      /-
        ─────────────── [TRUE-I]           ──────────────── [FALSE-I]
         Γ ⊢ TRUE ⇒ 𝔹                      Γ ⊢ FALSE ⇒ 𝔹
      -/
      | .bool b, pos => pure (.bool, .bool b @@ pos)
      /-
         Γ ⊢ e ⇒ [x₀ : τₒ, …, xₙ : τₙ]         y = xᵢ
        ────────────────────────────────────────────── [Record-E]
                        Γ ⊢ e.y ⇒ τᵢ
      -/
      | .access e y, pos => do
        let (τ', e') ← inferExpr e
        match τ' with
        | .record τs =>
          match τs.lookup y with
          | .some τ => pure (τ, .access e' y @@ pos)
          | .none => throw (.recordHasNoField y (τs.map Prod.fst) (posOf e))
        | τ' => throw (.expectedRecordType (posOf e) τ')
      /-
                    ∀ 0 ≤ i ≤ n, Γ ⊢ eᵢ ⇒ τᵢ
        ────────────────────────────────────────────────── [Record-I]
         Γ ⊢ [x₀ ↦ e₀, …, xₙ ↦ eₙ] ⇒ [x₀ : τ₀, …, xₙ : τₙ]
      -/
      | .record fs, pos => do
        let fs' ← fs.attach.mapM λ ⟨(x, _τ, e), _⟩ ↦ (x, ·) <$> inferExpr e
        return (.record (fs'.map λ (x, τ, _) ↦ (x, τ)), .record fs' @@ pos)
      | e, pos => throw (.typeInferenceFailure e pos)
    termination_by e
    decreasing_by
      all: try decreasing_trivial
      · calc
          sizeOf e < sizeOf (x, _τ, e) := by decreasing_trivial
          _ < _                        := by decreasing_trivial
  end

end Expressions
