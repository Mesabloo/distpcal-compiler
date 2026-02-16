import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Defs.PartialOrder

/-- A type can be used to model event traces if it is a partially ordered monoid. -/
class Trace (ε : Type _) extends Monoid ε, PartialOrder ε where
  le_mul_right_inj : ∀ ⦃x y z : ε⦄, x ≤ y → z * x ≤ z * y
  -- jsp₃ : ∀ ⦃x y z : ε⦄, x ≤ y → x * z ≤ y * z
  le_extend_mul : ∀ ⦃x y z : ε⦄, x ≤ y → x ≤ y * z

abbrev Trace.τ {ε : Type _} [Trace ε] : ε := One.one

theorem append_τ_eq {ε} (a : ε) [Trace ε] : a * Trace.τ = a := mul_one a

theorem τ_append_eq {ε} (a : ε) [Trace ε] : Trace.τ * a = a := one_mul a
