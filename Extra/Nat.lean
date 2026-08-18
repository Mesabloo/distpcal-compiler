module

meta import CustomPrelude
import Mathlib.Data.List.Induction
import Batteries.Data.String.Lemmas
import Std.Data.String.ToNat
import Std.Data.String.ToInt
import all Init.Data.String.Search
import all Init.Data.String.Slice

public section

namespace Nat
  theorem succ_le_exists_succ {m n : Nat} : m.succ ≤ n → ∃ n' : Nat, n = n'.succ := by
    intro m_lt_n
    induction n with
    | zero => nomatch m_lt_n
    | succ n IH =>
      by_cases n_eq : n = m
      · subst n_eq
        exists n
      · have m_succ_le_n : m.succ ≤ n := by omega
        obtain ⟨n', rfl⟩ := IH m_succ_le_n
        exists n'.succ

  theorem succ_lt_exists_succ {m n : Nat} : m < n → ∃ n', n = n' + 1 := succ_le_exists_succ

  theorem min_le {m n o p : Nat} : m ≤ n → o ≤ p → min m o ≤ min n p := by omega

  theorem add_max {m n o : Nat} : m + max n o = max (m + n) (m + o) := by omega

  theorem le_max_of_le_left {m n o : Nat} (h : m ≤ n) : m ≤ max n o := by omega

  theorem le_of_lt_non_null {m n : Nat} : m ≠ 0 → m - 1 < n → m ≤ n := by omega

  theorem le_max_iff {m n o : Nat} : m ≤ max n o ↔ m ≤ n ∨ m ≤ o := by omega

  def induction_from_one {P : Nat → Prop} (one : P 1) (more : (n : Nat) → n > 0 → P n → P (n + 1)) {n : Nat} (n_not_zero : n > 0) : P n := match (generalizing := true) n with
    | 0 => nomatch n_not_zero
    | 1 => one
    | n + 2 => more (n + 1) (Nat.add_one_pos _) (Nat.induction_from_one one more (Nat.add_one_pos _))

  def div.induct' (k : Nat) (k_pos : k > 1) {motive : Nat → Prop} (ind : ∀ n > k, motive (n / k) → motive n) (base₁ : ∀ n < k, motive n) (base₂ : motive k) (n : Nat) : motive n :=
    if h₁ : n = k then
      h₁ ▸ base₂
    else if h₂ : n < k then
      base₁ _ h₂
    else
      ind _ (by obtain _|_ := Nat.eq_or_lt_of_not_lt h₂ <;> trivial) (div.induct' k k_pos ind base₁ base₂ (n / k))
  termination_by n
  decreasing_by
    · have h : n > k := by obtain _|_ := Nat.eq_or_lt_of_not_lt h₂ <;> trivial
      apply div_lt_self
      · trans k
        · trans 1
          · exact Nat.one_pos
          · assumption
        · assumption
      · assumption

  theorem add_ge_add_iff_right {k m n : Nat} : k + n ≥ m + n ↔ k ≥ m := Nat.add_le_add_iff_right

  theorem repr_toInt! {n : Nat} : n.repr.toInt! = n := by
    unfold String.toInt! String.Slice.toInt!
    rw [← String.toInt?, toInt?_repr]
end Nat

end
