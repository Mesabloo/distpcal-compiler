module

meta import CustomPrelude

public section

namespace String
  def escape : String → String := String.foldl escapeAux ""
  where
    escapeAux (acc : String) : Char → String
      | '\n' => acc ++ "\\n"
      | '\\' => acc ++ "\\\\"
      | '\t' => acc ++ "\\t"
      | c => acc.push c

  -- @[simp]
  -- theorem get_singleton_0 {c : Char} : Pos.Raw.get (singleton c) 0 = c := by
  --   unfold Pos.Raw.get Pos.Raw.utf8GetAux
  --   have : (singleton c).toList = [c] := by simp
  --   rw [this]
  --   rfl

  -- theorem next_singleton_0 {c : Char} : Pos.Raw.next (String.singleton c) 0 = (singleton c).rawEndPos := by
  --   unfold Pos.Raw.next rawEndPos
  --   simp [Pos.Raw.zero_add_char_eq]

  -- theorem rawEndPos_singleton {c : Char} : (String.singleton c).rawEndPos = ⟨c.utf8Size⟩ := by
  --   unfold String.rawEndPos String.utf8ByteSize
  --   grind only [Pos.Raw.mk.injEq, size_toByteArray, utf8ByteSize_singleton]

  -- theorem endPos_singleton {c : Char} : (String.singleton c).endPos = ⟨⟨c.utf8Size⟩, by simp⟩ := by
  --   unfold endPos
  --   simp [rawEndPos_singleton]

  -- theorem startPos_singleton {c : Char} : (String.singleton c).startPos = ⟨0, by simp⟩ := by
  --   rfl

  -- theorem toSubstring_singleton {c : Char} : (String.singleton c).toRawSubstring = ⟨String.singleton c, 0, ⟨c.utf8Size⟩⟩ := by
  --   dsimp [String.toRawSubstring]
  --   rw [rawEndPos_singleton]

  -- theorem toSlice_singleton {c : Char} : (singleton c).toSlice = ⟨singleton c, ⟨0, by simp⟩, ⟨⟨c.utf8Size⟩, by simp⟩, of_decide_eq_true rfl⟩ := by
  --   unfold toSlice
  --   simp [endPos_singleton, startPos_singleton]

  -- theorem any_singleton {c} {p : Char → Bool} : (String.singleton c).any p = p c := by
  --   unfold any contains
  --   rw [toSlice_singleton]
  --   unfold Slice.contains
  --   dsimp
  --   stop
  --   dsimp [String.any, String.contains, String.toSlice]
  --   rw [String.endPos_singleton]
  --   unfold String.anyAux
  --   split_ifs with h₁ h₂
  --   · rw [String.get_singleton_0] at h₂
  --     rw [h₂]
  --   · rw [String.get_singleton_0, Bool.bool_iff_false] at h₂
  --     rw [h₂]
  --     unfold String.anyAux
  --     split_ifs with h₃ h₄
  --     · rw [String.next_singleton_0, String.endPos_singleton, String.Pos.lt_iff] at h₃
  --       exact Nat.lt_irrefl _ h₃
  --     · rw [String.next_singleton_0, String.endPos_singleton, String.Pos.lt_iff] at h₃
  --       exfalso
  --       exact Nat.lt_irrefl _ h₃
  --     · rfl
  --   · rw [String.Pos.lt_iff, String.Pos.byteIdx_zero, Nat.not_lt_eq, Nat.le_zero] at h₁
  --     dsimp [Char.utf8Size] at h₁
  --     split_ifs at h₁

  -- theorem all_singleton {c} {p : Char → Bool} : (String.singleton c).all p = p c := by
  --   dsimp [String.all]
  --   stop
  --   rw [String.any_singleton, Bool.not_eq_eq_eq_not]


  -- theorem foldl_singleton {α} {c : Char} {f : α → Char → α} {init : α} : String.foldl f init (String.singleton c) = f init c := by
  --   stop
  --   unfold String.foldl String.foldlAux
  --   rw [String.endPos_singleton]
  --   split_ifs with h
  --   · dsimp
  --     rw [String.next_singleton_0]
  --     unfold String.foldlAux
  --     split_ifs with h'
  --     · rw [String.endPos_singleton] at h'
  --       dsimp at h'
  --       replace h' := Nat.lt_irrefl _ h'
  --       contradiction
  --     · rw [String.get_singleton_0]
  --   · unfold Char.utf8Size at h
  --     dsimp at h
  --     split_ifs at h <;> contradiction

  -- theorem singleton_not_empty {c : Char} : (String.singleton c).isEmpty = false := by
  --   stop
  --   dsimp [String.isEmpty]
  --   rw [rawEndPos_singleton, beq_eq_false_iff_ne]
  --   dsimp [Char.utf8Size]
  --   split_ifs <;> trivial

  -- theorem singleton_isNat_iff_isDigit {c : Char} : (String.singleton c).isNat ↔ c.isDigit := by
  --   stop
  --   dsimp [String.isNat]
  --   rw [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, and_iff_right String.singleton_not_empty,
  --       String.all_singleton]

  -- theorem singleton_toNat? {c : Char} : (String.singleton c).toNat? = if c.isDigit then .some (c.toNat - 48) else .none := by
  --   stop
  --   unfold String.toNat?
  --   simp [String.singleton_isNat_iff_isDigit]
  --   split_ifs <;> congr
  --   rw [String.foldl_singleton]
  --   simp +arith

  -- theorem singleton_toInt? {c : Char} : (String.singleton c).toInt? = if c.isDigit then .some (c.toNat - 48) else .none := by
  --   stop
  --   unfold String.toInt?
  --   rw [get_singleton_0, toSubstring_singleton, Substring.drop]
  --   split_ifs with h₁ h₂ h₃
  --   · subst c; contradiction
  --   · unfold Substring.toNat? Substring.isNat
  --     split_ifs with h₃
  --     · absurd h₃
  --       rw [Bool.not_eq_true, Bool.and_eq_false_eq_eq_false_or_eq_false, Bool.not_eq_false']
  --       left
  --       unfold Substring.isEmpty Substring.bsize Substring.nextn Substring.nextn Substring.next
  --       dsimp

  --       have : (0 : String.Pos) + 0 = 0 := by rfl

  --       rw [this, next_singleton_0, ite_cond_eq_false, endPos_singleton]
  --       · simp
  --       · apply eq_false
  --         apply Pos.ne_of_lt
  --         apply Char.utf8Size_pos
  --     · rfl
  --   · rw [singleton_toNat?, ite_cond_eq_true _ _ (eq_true h₃), Option.map_eq_map, Option.map_some]
  --     congr
  --     apply Int.ofNat_sub
  --     unfold Char.isDigit at h₃
  --     rw [Bool.and_eq_true_eq_eq_true_and_eq_true, decide_eq_true_iff] at h₃
  --     exact h₃.left
  --   · rw [singleton_toNat?, Option.map_eq_map, ite_cond_eq_false _ _ (eq_false h₃), Option.map_none]

  theorem singleton_toInt! {c : Char} (h : c.isDigit) : (singleton c).toInt! = c.toNat - 48 := by
    have : c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨ c = '5' ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9' := by
      unfold Char.isDigit at h
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true, Bool.decide_iff, Bool.decide_iff] at h
      repeat rw [Char.ext_iff]
      grind

    rcases this with _|_|_|_|_|_|_|_|_|_
      <;> subst c
          -- TODO: get rid of `decide +native`
      <;> decide +native

  theorem toSlice_empty_eq : "".toSlice = ⟨"", ⟨0, by solve_by_elim⟩, ⟨0, by solve_by_elim⟩, by solve_by_elim⟩ := by
    rfl

  namespace Slice
    -- theorem dropWhile_empty_of_empty {ρ : Type} {s : String.Slice} {p : ρ} [Slice.Pattern.ForwardPattern p] (h : s.isEmpty) : (s.dropWhile p).isEmpty := by

    --   admit

    -- theorem all_of_empty {ρ : Type} {s : String.Slice} {p : ρ} [Slice.Pattern.ForwardPattern p] (h : s.isEmpty) : s.all p = true := by
    --   unfold Slice.all
    --   apply dropWhile_empty_of_empty
    --   assumption

    theorem startPos_ne_endPos_of_non_empty {s : Slice} (h : ¬s.isEmpty) : s.startPos ≠ s.endPos := by
      suffices 0 ≠ s.rawEndPos by
        unfold startPos endPos
        grind

      rw [String.Slice.isEmpty_iff] at h
      unfold rawEndPos
      grind only [Pos.Raw.mk_zero, utf8ByteSize_eq]
  end Slice

  -- theorem singleton_not_empty {c : Char} : (singleton c).isEmpty = false := by
  --   rw [singleton_eq_ofList]
  --   unfold isEmpty
  --   simp
  --   exact (Char.utf8Size_pos c).ne'

  -- theorem isEmpty_append_iff {s s' : String} : (s ++ s').isEmpty = (s.isEmpty && s'.isEmpty) := by
  --   unfold isEmpty
  --   grind only [utf8ByteSize_append, utf8ByteSize_empty, utf8ByteSize_eq_zero_iff]

  -- theorem ofList_isEmpty_eq {cs : List Char} : (String.ofList cs).isEmpty = cs.isEmpty := by
  --   cases cs with
  --   | nil =>
  --     rfl
  --   | cons c cs =>
  --     rw [ofList_cons, isEmpty_append_iff, singleton_not_empty, Bool.false_and, List.isEmpty_cons]

  -- theorem front?_append_of_not_empty {s s' : String} (h : ¬s.isEmpty) : (s ++ s').front? = s.front? := by

  --   admit

  -- theorem front?_singleton {c : Char} : (singleton c).front? = some c := by

  --   admit

  -- theorem front?_ofList {cs : List Char} : (ofList cs).front? = cs.head? := by
  --   cases cs with
  --   | nil =>
  --     rw [front?_eq]
  --     rfl
  --   | cons c cs =>
  --     rw [List.head?_cons, ofList_cons, front?_append_of_not_empty (ne_true_of_eq_false singleton_not_empty), front?_singleton]

  -- theorem toSlice_singleton {c : Char} : (singleton c).toSlice = ⟨singleton c, ⟨0, by simp⟩, ⟨⟨c.utf8Size⟩, by simp⟩, of_decide_eq_true rfl⟩ := by
  --   unfold toSlice startPos endPos rawEndPos
  --   simp

  -- theorem singleton_eq' {c : Char} : singleton c = "".push c := rfl
end String

end
