import PlusCalCompiler.Passes.Typechecker.TLAPlus
import Extra.AList

set_option mvcgen.warning false

open CoreTLAPlus

abbrev Context := AList λ _ : String ↦ Typ

mutual
  inductive CheckExpr : Context → Expression Typ → Typ → Prop
    | conv {Γ} {e} {τ τ'} : InferExpr Γ e τ' → τ ≅ τ' → CheckExpr Γ e τ

  inductive InferExpr : Context → Expression Typ → Typ → Prop
    | var {Γ} {v} {τ} : Γ.lookup v = some τ → InferExpr Γ (.var v) τ
    | str {Γ} {s} : InferExpr Γ (.str s) .str
    | nat {Γ} {n} : InferExpr Γ (.nat n) .int
    | bool {Γ} {b} : InferExpr Γ (.bool b) .bool
end

notation Γ " ⊢ " e " ⇐ " τ => CheckExpr Γ e τ
notation Γ " ⊢ " e " ⇒ " τ => InferExpr Γ e τ
notation Γ " ⊢ " e " : " τ => CheckExpr Γ e τ ∨ InferExpr Γ e τ

-------------------------

open scoped Std.Do

lemma lookupDecl_TC_eq {x : String} : lookupDecl (m := TC) x = (Std.HashMap.get? · x) <$> read := rfl

theorem lookupDecl_spec {x : String} {ctx} :
    ⦃λ ctx' ↦ ⌜ctx' = ctx⌝⦄
    lookupDecl (m := TC) x
    ⦃⇓ τ ctx' => ⌜ctx' = ctx ∧ ctx'[x]? = τ⌝⦄ := by
  rw [lookupDecl_TC_eq]
  mvcgen

mutual
  theorem checkExpr_spec {e : Expression Typ} {τ : Typ} {Γ : Context} :
      ⦃λ ctx ↦ ⌜∀ k, ctx[k]? = Γ.lookup k⌝⦄
      checkExpr (m := TC) e τ
      ⦃⇓? _ => ⌜Γ ⊢ e ⇐ τ⌝⦄ := by
    cases e with
      unfold checkExpr
    | set elems => sorry
    | «prefix» op e => sorry
    | «infix» e₁ op e₂ => sorry
    | funcall fn args => sorry
    | seq es => sorry
    | opcall fn args => sorry
    | var | str | nat | bool | record | access | except =>
      mvcgen [inferExpr_spec]
      try next res _ conv _ _ _ => exact CheckExpr.conv ‹Γ ⊢ _ ⇒ res.1› conv

  theorem inferExpr_spec {e : Expression Typ} {Γ : Context} :
      ⦃λ ctx ↦ ⌜∀ k, ctx.get? k = Γ.lookup k⌝⦄
      inferExpr (m := TC) e
      ⦃⇓? (τ, _) => ⌜Γ ⊢ e ⇒ τ⌝⦄ := by
    cases e with
      unfold inferExpr
    | var name =>
      mvcgen [lookupDecl_spec]
      next τ hyp _ _ _ ctx _ lookup_ctx =>
      apply InferExpr.var
      rw [← hyp, ← lookup_ctx.1, ← lookup_ctx.2]
      rfl
    | str raw =>
      mvcgen
      apply InferExpr.str
    | nat raw =>
      mvcgen
      apply InferExpr.nat
    | bool raw =>
      mvcgen
      apply InferExpr.bool
    | record fields =>
      sorry
    | access e x =>
      sorry
    | «infix» e₁ op e₂ =>
      sorry
    | «prefix» | seq | funcall | opcall | set =>
      mvcgen
    | except e upds =>
      -- No rule yet
      sorry
end
