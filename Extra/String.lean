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

  theorem singleton_toInt! {c : Char} (h : c.isDigit) : (singleton c).toInt! = c.toNat - 48 := by
    have : c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨ c = '5' ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9' := by
      unfold Char.isDigit at h
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true, Bool.decide_iff, Bool.decide_iff] at h
      repeat rw [Char.ext_iff]
      grind

    rcases this with _|_|_|_|_|_|_|_|_|_
      <;> subst c
          -- TODO(native-decide): close these ten cases without `decide +native`.
      <;> decide +native

  theorem toSlice_empty_eq : "".toSlice = ⟨"", ⟨0, by solve_by_elim⟩, ⟨0, by solve_by_elim⟩, by solve_by_elim⟩ := by
    rfl

  namespace Slice
    theorem startPos_ne_endPos_of_non_empty {s : Slice} (h : ¬s.isEmpty) : s.startPos ≠ s.endPos := by
      suffices 0 ≠ s.rawEndPos by
        unfold startPos endPos
        grind

      rw [String.Slice.isEmpty_iff] at h
      unfold rawEndPos
      grind only [Pos.Raw.mk_zero, utf8ByteSize_eq]
  end Slice
end String

end
