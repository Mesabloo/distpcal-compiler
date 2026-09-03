module

import CustomPrelude

/-! Tests for `linter.fugue.unfoldForeign` (opt-in: `default := false`). -/

set_option linter.fugue.unfoldForeign true

/--
warning: `Function.comp` is imported — characterize it in the module that defines it, not by unfolding past its API here

Note: This linter can be disabled with `set_option linter.fugue.unfoldForeign false`
-/
#guard_msgs in
example (f g : Nat → Nat) (x : Nat) : (f ∘ g) x = f (g x) := by
  unfold Function.comp
  rfl

/-- A locally-defined function is fair game to unfold. -/
private def twice (n : Nat) : Nat := n + n

#guard_msgs in
example (n : Nat) : twice n = n + n := by
  unfold twice
  rfl

-- A `simp` argument that names a lemma (not a `def`) is normal use.
#guard_msgs in
example (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]
