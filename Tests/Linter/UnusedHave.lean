module

import CustomPrelude

/-! Tests for `linter.fugue.unusedHave`. -/

/--
warning: `have h` is never used — delete it

Note: This linter can be disabled with `set_option linter.fugue.unusedHave false`
-/
#guard_msgs in
example : True := by
  have h : 1 ≤ 1 := Nat.le_refl 1
  trivial

/--
warning: `haveI inst` is never used — delete it

Note: This linter can be disabled with `set_option linter.fugue.unusedHave false`
-/
#guard_msgs in
example : True := by
  haveI inst : Inhabited Nat := ⟨0⟩
  trivial

-- A `have` the proof goes on to use is fine.
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  have h : p := id hp
  exact ⟨h, hq⟩

-- Used through a rewrite.
#guard_msgs in
example (n : Nat) (hn : n = 0) : n + 0 = 0 := by
  have h : n + 0 = n := Nat.add_zero n
  rw [h, hn]
