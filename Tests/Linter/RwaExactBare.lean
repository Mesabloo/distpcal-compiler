module

import CustomPrelude

/-! Tests for `linter.fugue.rwaExactBare`. -/

/--
warning: `rw [S]` then `exact hpb` → `rwa [S]`

Note: This linter can be disabled with `set_option linter.fugue.rwaExactBare false`
-/
#guard_msgs in
example (p : Nat → Prop) (a b : Nat) (h : a = b) (hpb : p b) : p a := by
  rw [h]
  exact hpb

-- `exact` of an applied term is not a bare hypothesis — no `rwa` absorption.
#guard_msgs in
example (p : Nat → Prop) (a b : Nat) (h : a = b) (hp : ∀ x, p x) : p a := by
  rw [h]
  exact hp b

-- `exact` of a global name: `rwa`'s closing `assumption` would not find it.
#guard_msgs in
example (a b : Nat) (h : a = b) : a = b → True := by
  rw [h]
  intro _
  exact True.intro
