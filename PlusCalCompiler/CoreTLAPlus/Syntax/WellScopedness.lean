import PlusCalCompiler.CoreTLAPlus.Syntax
import Mathlib.Data.Finset.Basic
import CustomPrelude

namespace CoreTLAPlus
  abbrev Scope := Finset String

  universe u
  variable {Typ : Type u}

  protected def Expression.WellScoped (e : Expression Typ) (Γ : Scope) : Prop := match e with
    | .var _ x => x ∈ Γ
    | .str _ _ | .nat _ _ | .bool _ _ => True
    | .set _ es => ∀ e ∈ es, e.WellScoped Γ
    | .record _ fs => ∀ f ∈ fs, f.2.2.WellScoped Γ
    | .prefix _ _ e => e.WellScoped Γ
    | .infix _ e₁ _ e₂ => e₁.WellScoped Γ ∧ e₂.WellScoped Γ
    | .funcall _ fn args => fn.WellScoped Γ ∧ ∀ arg ∈ args, arg.WellScoped Γ
    | .access _ e _ => e.WellScoped Γ
    | .seq _ es => ∀ e ∈ es, e.WellScoped Γ
    | .opcall _ fn args => fn.WellScoped Γ ∧ ∀ arg ∈ args, arg.WellScoped Γ
    | .except _ e upds => e.WellScoped Γ ∧ ∀ upd ∈ upds, upd.2.WellScoped Γ ∧ ∀ idx ∈ upd.1, match _h : idx with | .inr _ => True | .inl es => ∀ e ∈ es, e.WellScoped Γ
  termination_by e
  decreasing_by
    all: simp_wf; try decreasing_trivial
    · apply Nat.le_of_lt
      calc
        sizeOf es < sizeOf (Sum.inl (β := String) es) := by subst idx; decreasing_trivial
        _ < sizeOf upd.1 := by subst idx; decreasing_trivial
        _ < sizeOf upd := by repeat rw [Prod.mk.sizeOf_spec]; simp +arith
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by decreasing_trivial
    · calc
        sizeOf upd.2 < sizeOf upd := by repeat rw [Prod.mk.sizeOf_spec]; simp +arith
        _ < _ := by decreasing_trivial
    · calc
        sizeOf f.2.2 < sizeOf f := by repeat rw [Prod.mk.sizeOf_spec]; simp +arith
        _ < _ := by decreasing_trivial

  ------------------------------

  protected def Expression.FreshIn (e : Expression Typ) (x : String) : Prop := match e with
    | .var _ y => x ≠ y
    | .str _ _ | .nat _ _ | .bool _ _ => True
    | .set _ es => ∀ e ∈ es, e.FreshIn x
    | .record _ fs => ∀ f ∈ fs, f.2.2.FreshIn x
    | .prefix _ _ e => e.FreshIn x
    | .infix _ e₁ _ e₂ => e₁.FreshIn x ∧ e₂.FreshIn x
    | .funcall _ fn args => fn.FreshIn x ∧ ∀ arg ∈ args, arg.FreshIn x
    | .access _ e _ => e.FreshIn x
    | .seq _ es => ∀ e ∈ es, e.FreshIn x
    | .opcall _ fn args => fn.FreshIn x ∧ ∀ arg ∈ args, arg.FreshIn x
    | .except _ e upds => e.FreshIn x ∧ ∀ upd ∈ upds, upd.2.FreshIn x ∧ ∀ idx ∈ upd.1, match _h : idx with | .inr _ => True | .inl es => ∀ e ∈ es, e.FreshIn x
  termination_by e
  decreasing_by
    all: simp_wf; try decreasing_trivial
    · apply Nat.le_of_lt
      calc
        sizeOf es < sizeOf (Sum.inl (β := String) es) := by subst idx; decreasing_trivial
        _ < sizeOf upd.1 := by subst idx; decreasing_trivial
        _ < sizeOf upd := by repeat rw [Prod.mk.sizeOf_spec]; simp +arith
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by decreasing_trivial
    · calc
        sizeOf upd.2 < sizeOf upd := by repeat rw [Prod.mk.sizeOf_spec]; simp +arith
        _ < _ := by decreasing_trivial
    · calc
        sizeOf f.2.2 < sizeOf f := by repeat rw [Prod.mk.sizeOf_spec]; simp +arith
        _ < _ := by decreasing_trivial
