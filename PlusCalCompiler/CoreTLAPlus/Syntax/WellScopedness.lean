import PlusCalCompiler.CoreTLAPlus.Syntax
import Mathlib.Data.Finset.Basic
import CustomPrelude

namespace CoreTLAPlus
  abbrev Scope := Finset String

  universe u
  variable {Typ : Type u}

  protected def Expression.WellScoped (e : Expression Typ) (Γ : Scope) : Prop := match e with
    | .var x => x ∈ Γ
    | .str _ | .nat _ | .bool _ => True
    | .set es => ∀ e ∈ es, e.WellScoped Γ
    | .record fs => ∀ f ∈ fs, f.2.2.WellScoped Γ
    | .prefix _ e => e.WellScoped Γ
    | .infix e₁ _ e₂ => e₁.WellScoped Γ ∧ e₂.WellScoped Γ
    | .funcall fn args => fn.WellScoped Γ ∧ ∀ arg ∈ args, arg.WellScoped Γ
    | .access e _ => e.WellScoped Γ
    | .seq es => ∀ e ∈ es, e.WellScoped Γ
    | .opcall fn args => fn.WellScoped Γ ∧ ∀ arg ∈ args, arg.WellScoped Γ
    | .except e upds => e.WellScoped Γ ∧ ∀ upd ∈ upds, upd.2.WellScoped Γ ∧ ∀ idx ∈ upd.1, match _h : idx with | .inr _ => True | .inl es => ∀ e ∈ es, e.WellScoped Γ
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
    | .var y => x ≠ y
    | .str _ | .nat _ | .bool _ => True
    | .set es => ∀ e ∈ es, e.FreshIn x
    | .record fs => ∀ f ∈ fs, f.2.2.FreshIn x
    | .prefix _ e => e.FreshIn x
    | .infix e₁ _ e₂ => e₁.FreshIn x ∧ e₂.FreshIn x
    | .funcall fn args => fn.FreshIn x ∧ ∀ arg ∈ args, arg.FreshIn x
    | .access e _ => e.FreshIn x
    | .seq es => ∀ e ∈ es, e.FreshIn x
    | .opcall fn args => fn.FreshIn x ∧ ∀ arg ∈ args, arg.FreshIn x
    | .except e upds => e.FreshIn x ∧ ∀ upd ∈ upds, upd.2.FreshIn x ∧ ∀ idx ∈ upd.1, match _h : idx with | .inr _ => True | .inl es => ∀ e ∈ es, e.FreshIn x
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
