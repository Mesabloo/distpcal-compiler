import CustomPrelude

namespace String
  def escape : String → String := String.foldl escapeAux ""
  where
    escapeAux (acc : String) : Char → String
      | '\n' => acc ++ "\\n"
      | '\\' => acc ++ "\\\\"
      | '\t' => acc ++ "\\t"
      | c => acc.push c

  theorem get_singleton_0 {c : Char} : (String.singleton c).get 0 = c := rfl

  theorem next_singleton_0 {c : Char} : (String.singleton c).next 0 = (String.singleton c).endPos := rfl

  theorem endPos_singleton {c : Char} : (String.singleton c).endPos = ⟨c.utf8Size⟩ := by
    unfold String.endPos String.utf8ByteSize String.utf8ByteSize.go String.utf8ByteSize.go -- unfold twice
    simp

  theorem toSubstring_singleton {c : Char} : (String.singleton c).toSubstring = ⟨String.singleton c, 0, ⟨c.utf8Size⟩⟩ := by
    dsimp [String.toSubstring]
    rw [endPos_singleton]

  theorem any_singleton {c} {p : Char → Bool} : (String.singleton c).any p = p c := by
    dsimp [String.any]
    rw [String.endPos_singleton]
    unfold String.anyAux
    split_ifs with h₁ h₂
    · rw [String.get_singleton_0] at h₂
      rw [h₂]
    · rw [String.get_singleton_0, Bool.bool_iff_false] at h₂
      rw [h₂]
      unfold String.anyAux
      split_ifs with h₃ h₄
      · rw [String.next_singleton_0, String.endPos_singleton, String.Pos.lt_iff] at h₃
        exact Nat.lt_irrefl _ h₃
      · rw [String.next_singleton_0, String.endPos_singleton, String.Pos.lt_iff] at h₃
        exfalso
        exact Nat.lt_irrefl _ h₃
      · rfl
    · rw [String.Pos.lt_iff, String.Pos.byteIdx_zero, Nat.not_lt_eq, Nat.le_zero] at h₁
      dsimp [Char.utf8Size] at h₁
      split_ifs at h₁

  theorem all_singleton {c} {p : Char → Bool} : (String.singleton c).all p = p c := by
    dsimp [String.all]
    rw [String.any_singleton, Bool.not_eq_eq_eq_not]


  theorem foldl_singleton {α} {c : Char} {f : α → Char → α} {init : α} : String.foldl f init (String.singleton c) = f init c := by
    unfold String.foldl String.foldlAux
    rw [String.endPos_singleton]
    split_ifs with h
    · dsimp
      rw [String.next_singleton_0]
      unfold String.foldlAux
      split_ifs with h'
      · rw [String.endPos_singleton] at h'
        dsimp at h'
        replace h' := Nat.lt_irrefl _ h'
        contradiction
      · rw [String.get_singleton_0]
    · unfold Char.utf8Size at h
      dsimp at h
      split_ifs at h <;> contradiction

  theorem singleton_not_empty {c : Char} : (String.singleton c).isEmpty = false := by
    dsimp [String.isEmpty]
    rw [String.endPos_singleton, beq_eq_false_iff_ne]
    dsimp [Char.utf8Size]
    split_ifs <;> trivial

  theorem singleton_isNat_iff_isDigit {c : Char} : (String.singleton c).isNat ↔ c.isDigit := by
    dsimp [String.isNat]
    rw [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, and_iff_right String.singleton_not_empty,
        String.all_singleton]

  theorem singleton_toNat? {c : Char} : (String.singleton c).toNat? = if c.isDigit then .some (c.toNat - 48) else .none := by
    unfold String.toNat?
    simp [String.singleton_isNat_iff_isDigit]
    split_ifs <;> congr
    rw [String.foldl_singleton]
    simp +arith

  theorem singleton_toInt? {c : Char} : (String.singleton c).toInt? = if c.isDigit then .some (c.toNat - 48) else .none := by
    unfold String.toInt?
    rw [get_singleton_0, toSubstring_singleton, Substring.drop]
    split_ifs with h₁ h₂ h₃
    · subst c; contradiction
    · unfold Substring.toNat? Substring.isNat
      split_ifs with h₃
      · absurd h₃
        rw [Bool.not_eq_true, Bool.and_eq_false_eq_eq_false_or_eq_false, Bool.not_eq_false']
        left
        unfold Substring.isEmpty Substring.bsize Substring.nextn Substring.nextn Substring.next
        dsimp

        have : (0 : String.Pos) + 0 = 0 := by rfl

        rw [this, next_singleton_0, ite_cond_eq_false, endPos_singleton]
        · simp
        · apply eq_false
          apply Pos.ne_of_lt
          apply Char.utf8Size_pos
      · rfl
    · rw [singleton_toNat?, ite_cond_eq_true _ _ (eq_true h₃), Option.map_eq_map, Option.map_some]
      congr
      apply Int.ofNat_sub
      unfold Char.isDigit at h₃
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true, decide_eq_true_iff] at h₃
      exact h₃.left
    · rw [singleton_toNat?, Option.map_eq_map, ite_cond_eq_false _ _ (eq_false h₃), Option.map_none]
end String
