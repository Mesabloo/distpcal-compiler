import CustomPrelude
import Mathlib.Data.List.Induction
import Batteries.Data.String.Lemmas
import Extra.String

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

  -- theorem le_add_left_of_le {m n o : Nat} (h : m ≤ o) : m ≤ n + o := by omega

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
    all_goals simp_wf
    · have h : n > k := by obtain _|_ := Nat.eq_or_lt_of_not_lt h₂ <;> trivial
      apply div_lt_self
      · trans k
        · trans 1
          · exact Nat.one_pos
          · assumption
        · assumption
      · assumption

  theorem String.get_cons_0 {s : List Char} {c : Char} : (String.mk (c :: s)).get 0 = c := rfl

  theorem String.next_cons_0 {s : List Char} {c : Char} : (String.mk (c :: s)).next 0 = ⟨c.utf8Size⟩ := by
    unfold String.next
    rw [String.get_cons_0]
    apply String.Pos.zero_addChar_eq

  theorem String.utf8GetAux_shunt {s i j p} : String.utf8GetAux s (i + p) (j + p) = String.utf8GetAux s i j := by
    induction s generalizing i p with
    | nil =>
      rfl
    | cons c s IH =>
      unfold String.utf8GetAux
      split_ifs with h₁ h₂ h₃
      · rfl
      · repeat rw [String.Pos.add_eq] at h₁
        rw [String.Pos.ext_iff] at h₁ h₂
        rw [Nat.add_right_cancel h₁] at h₂
        contradiction
      · subst i
        contradiction
      · conv_lhs =>
          enter [2]
          rw [String.Pos.addChar_eq, String.Pos.add_byteIdx, Nat.add_assoc]
          conv => enter [1, 2]; rw [Nat.add_comm]
          rw [← Nat.add_assoc]
          change (i + c) + p
        apply IH

  theorem String.get_skip_first {s : List Char} {c : Char} {i : String.Pos} : (String.mk (c :: s)).get (i + c) = (String.mk s).get i := by
    dsimp [String.get, String.utf8GetAux]
    rw [ite_cond_eq_false]
    · conv_lhs => change String.utf8GetAux s (0 + ⟨c.utf8Size⟩) (i + ⟨c.utf8Size⟩)
      rw [String.utf8GetAux_shunt]
    · apply eq_false
      rw [String.Pos.addChar_eq, String.Pos.ext_iff]
      dsimp

      have : c.utf8Size > 0 := by
        dsimp [Char.utf8Size]
        split_ifs <;> trivial

      omega

  theorem String.utf8GetAux_shunt' {c : Char} {s i} (h : i.byteIdx ≥ c.utf8Size) : String.utf8GetAux s ((0 : String.Pos) + c) i = String.utf8GetAux s 0 (i - ⟨c.utf8Size⟩) := by
    generalize (0 : String.Pos) = k
    induction s generalizing k with
    | nil =>
      rfl
    | cons c' s IH =>
      dsimp [String.utf8GetAux]
      split_ifs with h₁ h₂ h₃
      · rfl
      · subst i
        rw [String.Pos.addChar_eq, String.Pos.sub_eq, String.Pos.ext_iff, Nat.add_sub_cancel_right] at h₂
        contradiction
      · subst k
        rw [String.Pos.addChar_eq, String.Pos.sub_eq, String.Pos.ext_iff, Nat.sub_add_cancel h] at h₁
        contradiction
      · rw [String.Pos.addChar_right_comm, IH]

  theorem add_add_sub_cancel_right {m n k : Nat} (h : k ≥ n) : n + ((k - n) + m) = k + m := by
    omega

  theorem String.next_cons_of_ge {s : List Char} {c : Char} {i : String.Pos} (h : i ≥ ⟨c.utf8Size⟩) : (String.mk (c :: s)).next i = ⟨c.utf8Size⟩ + (String.mk s).next (i - ⟨c.utf8Size⟩) := by
    dsimp [String.next, String.get, String.utf8GetAux]
    split_ifs
    · subst i
      change _ ≤ _ at h
      rw [String.Pos.le_iff, String.Pos.byteIdx_zero, le_zero] at h
      dsimp [Char.utf8Size] at h
      split_ifs at h
    · rw [String.utf8GetAux_shunt' h]
      change _ ≤ _ at h
      rw [String.Pos.le_iff] at h
      repeat rw [String.Pos.add_eq]
      repeat rw [String.Pos.sub_eq]
      dsimp at h ⊢
      rw [add_add_sub_cancel_right h, String.Pos.addChar_eq]

  theorem String.digitChar_isDigit {n : Nat} (h : n < 10) : n.digitChar.isDigit := by
    decide +revert +kernel

  def toDigitsCore.induct' (base : ℕ) {motive : ℕ → ℕ → List Char → Prop}
    (case1 : ∀ (x : ℕ) (ds : List Char), motive 0 x ds)
    (case2 : ∀ (fuel n : ℕ) (ds : List Char), n / base = 0 → motive fuel.succ n ds)
    (case3 : ∀ (fuel n : ℕ) (ds : List Char), ¬n / base = 0 → motive fuel (n / base) ((n % base).digitChar :: ds) → motive fuel.succ n ds)
    (k n : ℕ) (ds : List Char) :
      motive k n ds :=
    Nat.toDigitsCore.induct base motive case1 case2 case3 k n ds

  theorem toDigitsCore_append {base k n : Nat} {ds ds' : List Char} : toDigitsCore base k n (ds ++ ds') = toDigitsCore base k n ds ++ ds' := by
    induction k, n, ds using toDigitsCore.induct' base with
    | case1 n ds =>
      dsimp [toDigitsCore]
    | case2 fuel n ds n_div_base_eq =>
      dsimp [toDigitsCore]
      repeat rw [n_div_base_eq]
      rfl
    | case3 fuel n ds n_div_base_neq IH =>
      dsimp [toDigitsCore]
      repeat rw [ite_cond_eq_false _ _ (eq_false n_div_base_neq)]
      rw [← IH, List.cons_append]

  theorem toDigitsCore_eq_append {base k n : Nat} {ds : List Char} : toDigitsCore base k n ds = toDigitsCore base k n [] ++ ds := by
    conv_lhs => enter [4]; rw [← List.nil_append ds]
    apply toDigitsCore_append

  theorem toDigitsCore_non_empty_of_succ {base k n : Nat} {ds : List Char} : (toDigitsCore base (k.succ) n ds).isEmpty = false := by
    generalize p_eq : k.succ = p
    have p_gt : p > 0 := by subst p; apply zero_lt_succ
    clear p_eq

    induction p, n, ds using toDigitsCore.induct' base with
    | case1 n ds =>
      contradiction
    | case2 fuel n ds n_div_base_eq =>
      dsimp [toDigitsCore]
      rw [n_div_base_eq, ite_cond_eq_true _ _ (eq_true (rfl : 0 = 0))]
      rfl
    | case3 fuel n ds n_div_base_neq IH =>
      dsimp [toDigitsCore]
      rw [ite_cond_eq_false _ _ (eq_false n_div_base_neq)]
      by_cases h : fuel = 0
      · subst fuel
        rfl
      · apply IH
        omega

  theorem String.endPos_empty : "".endPos = 0 := by rfl

  theorem String.endPos_cons {c cs} : (String.mk (c :: cs)).endPos = (String.mk cs).endPos + c := by
    repeat rw [String.endPos, String.utf8ByteSize]
    dsimp
    rw [String.Pos.addChar_eq]

  theorem String.foldl_nil {α} {f : α → Char → α} {init : α} : String.foldl f init "" = init := by
    rw [String.foldl, String.foldlAux, String.endPos_empty]
    split_ifs <;> trivial

  theorem String.Pos.add_comm {p₁ p₂ : String.Pos} : p₁ + p₂ = p₂ + p₁ := by
    rw [String.Pos.add_eq, String.Pos.add_eq, Nat.add_comm]

  -- theorem String.foldlAux_shunt {α} {f : α → Char → α} {init : α} {c : Char} {s : List Char} :
  --     String.foldlAux f {data := c :: s} ({ data := s : String}.endPos + c) { byteIdx := c.utf8Size } init =
  --       String.foldlAux f {data := s} ({data := s : String}.endPos) 0 init := by
  --   conv_lhs => enter [4]; change { byteIdx := c.utf8Size } + 0

  --   fun_induction String.foldlAux f ⟨s⟩ (String.endPos ⟨s⟩) 0 init with
  --   | case1 i init h _ IH =>
  --     unfold String.foldlAux
  --     split_ifs with h'
  --     · dsimp
  --       rw [← IH]
  --       congr 1
  --       · rw [String.next_cons_of_ge]
  --         · repeat rw [String.Pos.add_eq, String.Pos.sub_eq]
  --           congr
  --           simp
  --         · change _ ≤ _ + _
  --           rw [String.Pos.add_eq, String.Pos.le_iff]
  --           simp
  --       · congr 1
  --         conv_lhs => enter [2]; rw [String.Pos.add_comm, String.Pos.add_eq]; change i + c
  --         conv_rhs => rw [← String.get_skip_first (c := c)]
  --     · dsimp
  --       conv at h' => enter [1, 1]; rw [String.Pos.add_comm, String.Pos.add_eq]; change i + c
  --       repeat rw [String.Pos.addChar_eq] at h'
  --       erw [String.Pos.lt_iff, Nat.add_lt_add_iff_right, ← String.Pos.lt_iff] at h'
  --       contradiction
  --   | case2 i init h =>
  --     unfold String.foldlAux
  --     split_ifs with h'
  --     · rw [String.Pos.addChar_eq, String.Pos.add_eq, Nat.add_comm] at h'
  --       dsimp at h'
  --       rw [Nat.add_lt_add_iff_right] at h'
  --       contradiction
  --     · rfl

  theorem String.foldl_eq_foldl {α} {f : α → Char → α} {init : α} {s : String} : String.foldl f init s = List.foldl f init s.data := String.foldl_eq f s init
    -- let ⟨ss⟩ := s
    -- dsimp
    -- induction ss generalizing init with
    -- | nil =>
    --   rw [List.foldl_nil, String.foldl_nil]
    -- | cons c s IH =>
    --   rw [List.foldl_cons, String.foldl, String.foldlAux]
    --   split_ifs with h₁
    --   · dsimp
    --     rw [String.get_cons_0, String.next_cons_0, String.foldlAux_shunt, ← String.foldl]
    --     apply IH
    --   · apply Nat.ge_of_not_lt at h₁
    --     change 0 ≥ _ at h₁
    --     rw [String.endPos_cons, String.Pos.addChar_eq] at h₁

    --     have : c.utf8Size > 0 := by
    --       dsimp [Char.utf8Size]
    --       split_ifs <;> trivial

    --     simp_all

  theorem String.foldl_push {α} {f : α → Char → α} {init : α} {c : Char} {s : String} : String.foldl f init (s.push c) = f (String.foldl f init s) c := by
    let ⟨ss⟩ := s
    rw [String.push, String.foldl_eq_foldl, String.foldl_eq_foldl]
    apply List.foldl_concat

  theorem String.append_push {c} {xs ys : String} : xs ++ ys.push c = (xs ++ ys).push c := by
    change String.append xs (ys.push c) = (String.append xs ys).push c
    rcases xs, ys with ⟨⟨xs⟩, ⟨ys⟩⟩
    unfold String.push String.append
    simp

  theorem String.foldl_append {α} {f : α → Char → α} {init : α} {xs ys : String} : String.foldl f init (xs ++ ys) = String.foldl f (String.foldl f init xs) ys := by
    obtain ⟨ys⟩ := ys
    induction ys using List.reverseRecOn generalizing init with
    | nil => rw [String.foldl_nil, String.append_empty]
    | append_singleton ys y IH =>
      change String.foldl f init (xs ++ String.push ⟨ys⟩ y) = String.foldl f (String.foldl f init xs) (String.push ⟨ys⟩ y)
      erw [String.append_push]
      repeat rw [String.foldl_push]
      rw [IH]

  theorem String.empty_isEmpty : "".isEmpty = true := rfl

  theorem String.cons_non_empty {c : Char} {cs : List Char} : (String.mk (c :: cs)).isEmpty = false := by
    unfold String.isEmpty
    rw [String.endPos_cons, String.Pos.addChar_eq, beq_eq_false_iff_ne]

    have : c.utf8Size > 0 := by
      dsimp [Char.utf8Size]
      split_ifs <;> simp

    apply String.Pos.ne_zero_of_lt (a := 0)
    rw [String.Pos.lt_iff, String.Pos.byteIdx_zero]
    dsimp
    omega

  theorem String.isEmpty_append {s s' : String} : (s ++ s').isEmpty = (s.isEmpty && s'.isEmpty) := by
    let ⟨cs⟩ := s
    let ⟨cs'⟩ := s'
    match cs, cs' with
    | [], [] => rfl
    | [], _ :: _ => erw [String.empty_append, String.empty_isEmpty, Bool.true_and]
    | _ :: _, [] => erw [String.append_empty, String.empty_isEmpty, Bool.and_true]
    | _ :: _, _ :: _ => erw [String.cons_non_empty, String.cons_non_empty, String.cons_non_empty]; rfl

  theorem String.Pos.add_zero {p : String.Pos} : p + 0 = p := by
    rw [String.Pos.add_eq, String.Pos.byteIdx_zero, Nat.add_zero]

  theorem String.Pos.zero_add {p : String.Pos} : 0 + p = p := by
    rw [String.Pos.add_comm, String.Pos.add_zero]

  theorem String.cons_append {c : Char} {cs cs' : List Char} : String.mk (c :: cs) ++ (String.mk cs') = String.mk (c :: (cs ++ cs')) := by
    change String.append _ _ = _
    dsimp [String.append]

  theorem String.endPos_append {s s' : String} : (s ++ s').endPos = s.endPos + s'.endPos := by
    let ⟨cs⟩ := s
    induction cs with
    | nil => rw [String.empty_append, String.endPos_empty, String.Pos.zero_add]
    | cons c cs IH =>
      rw [String.cons_append, String.endPos_cons, String.endPos_cons]
      conv_rhs => rw [String.Pos.addChar_eq, String.Pos.add_eq, Nat.add_assoc, Nat.add_comm c.utf8Size, ← Nat.add_assoc, ← String.Pos.addChar_eq, ← String.Pos.add_eq]
      rw [← IH]
      congr

  theorem String.data_append {s s' : String} : (s ++ s').data = s.data ++ s'.data := rfl

  theorem String.all_append {s s' : String} {p : Char → Bool} : (s ++ s').all p = (s.all p && s'.all p) := by
    rw [Bool.eq_iff_iff, Bool.and_eq_true_eq_eq_true_and_eq_true]
    repeat rw [String.all_iff]
    constructor
    · intro h
      constructor
      · intros c c_in
        apply List.mem_append_left s'.data at c_in
        rw [← String.data_append] at c_in
        apply h
        assumption
      · intros c c_in
        apply List.mem_append_right s.data at c_in
        rw [← String.data_append] at c_in
        apply h
        assumption
    · rintro ⟨h₁, h₂⟩
      intros c c_in
      rw [String.data_append, List.mem_append] at c_in
      obtain c_in|c_in := c_in
      · apply h₁
        assumption
      · apply h₂
        assumption

  theorem String.toNat?_append_singleton {s c} (h : c.isDigit) (h' : s.isEmpty = false) : (s ++ String.singleton c).toNat? = s.toNat? <&> λ k ↦ k * 10 + (c.toNat - 48) := by
    unfold String.toNat?
    split_ifs with h₁ h₂ h₃
    · rw [String.foldl_append, String.foldl_singleton]
      rfl
    · unfold String.isNat at h₁ h₂
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true, Bool.not_eq_true_eq_eq_false] at h₁
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true, Bool.not_eq_true_eq_eq_false, not_and_or, Bool.eq_true_eq_not_eq_false,
          Bool.bool_iff_false] at h₂
      obtain ⟨h₁, h₃⟩ := h₁
      obtain h₂|h₂ := h₂
      · rw [h'] at h₂
        contradiction
      · rw [String.all_append, Bool.and_eq_true_eq_eq_true_and_eq_true] at h₃
        obtain ⟨h₃, _⟩ := h₃
        rw [h₂] at h₃
        contradiction
    · unfold String.isNat at h₁ h₃
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at h₃
      obtain ⟨h₃, h₄⟩ := h₃
      rw [Bool.bool_iff_false, Bool.and_eq_false_eq_eq_false_or_eq_false, or_iff_right] at h₁
      · rw [String.all_append, Bool.and_eq_false_eq_eq_false_or_eq_false, or_iff_right] at h₁
        · rw [String.all_singleton, h] at h₁
          contradiction
        · rwa [Bool.eq_true_eq_not_eq_false]
      · rw [Bool.not_eq_true_eq_eq_false] at h₃
        rw [Bool.eq_true_eq_not_eq_false, Bool.not_eq_true_eq_eq_false, String.isEmpty_append, h₃, Bool.false_and]
    · rfl

  theorem List.asString_append {xs ys : List Char} : (xs ++ ys).asString = xs.asString ++ ys.asString := rfl

  theorem List.asString_singleton {c : Char} : [c].asString = String.singleton c := rfl

  theorem add_ge_add_iff_right {k m n : Nat} : k + n ≥ m + n ↔ k ≥ m := Nat.add_le_add_iff_right

  theorem List.asString_isEmpty {cs : List Char} : cs.asString.isEmpty = cs.isEmpty := by
    unfold List.asString
    cases cs with
    | nil => rfl
    | cons c cs => rw [List.isEmpty_cons, String.cons_non_empty]

  theorem repr_toNat? {n : Nat} : n.repr.toNat? = .some n := by
    unfold Nat.repr Nat.toDigits

    generalize k_eq : n + 1 = k
    have k_ge : k ≥ n + 1 := by simp [*]
    clear k_eq

    induction n using div.induct' 10 (one_lt_succ_succ 8) generalizing k with
    | base₁ n n_le_10 =>
      have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
        omega
      obtain rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl := this <;> {
        obtain ⟨k', rfl⟩ := succ_le_exists_succ k_ge
        dsimp [toDigitsCore, digitChar, List.asString, String.toNat?]
        rw [Option.ite_none_right_eq_some]
        constructor
        · dsimp [String.isNat]
          rw [Bool.and_eq_true_eq_eq_true_and_eq_true, Bool.not_eq_true']
          constructor
          · rfl
          · change String.all (String.singleton _) _ = true
            rw [String.all_singleton]
            rfl
        · congr
          change String.foldl _ _ (String.singleton _) = _
          rw [String.foldl_singleton]
          rfl
      }
    | base₂ =>
      obtain ⟨k', rfl⟩ := succ_le_exists_succ k_ge
      dsimp [toDigitsCore]
      erw [← Nat.add_one, Nat.add_ge_add_iff_right] at k_ge
      obtain ⟨k'', rfl⟩ := succ_le_exists_succ k_ge
      dsimp [toDigitsCore, digitChar, List.asString, String.toNat?]
      rw [Option.ite_none_right_eq_some]

      have ten_eq : "10" = String.singleton '1' ++ String.singleton '0' := rfl

      constructor
      · dsimp [String.isNat]
        rw [Bool.and_eq_true_eq_eq_true_and_eq_true, Bool.not_eq_true']
        constructor
        · rfl
        · rw [ten_eq, String.all_append, String.all_singleton, String.all_singleton]
          rfl
      · congr
        rw [ten_eq, String.foldl_append, String.foldl_singleton, String.foldl_singleton]
        rfl
    | ind n n_gt_10 IH =>
      have : n / 10 ≠ 0 := by omega

      obtain ⟨k', rfl⟩ := succ_le_exists_succ k_ge

      unfold toDigitsCore
      rw [ite_cond_eq_false _ _ (eq_false this), toDigitsCore_eq_append, List.asString_append, List.asString_singleton,
          String.toNat?_append_singleton]
      · erw [IH k' (by omega), Option.map_eq_some_iff]
        exists n / 10, rfl

        have : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
          omega
        obtain h|h|h|h|h|h|h|h|h|h := this <;> {
          rw [h]
          dsimp [digitChar, Char.toNat]
          omega
        }
      · apply String.digitChar_isDigit
        omega
      · rw [List.asString_isEmpty]
        erw [← Nat.add_one, Nat.add_ge_add_iff_right] at k_ge
        obtain ⟨n', rfl⟩ := succ_lt_exists_succ n_gt_10
        obtain ⟨k'', _|_⟩ := succ_le_exists_succ k_ge
        apply toDigitsCore_non_empty_of_succ

  theorem List.data_asString {cs : List Char} : cs.asString.data = cs := rfl

  theorem String.get_0_eq_iff {s : String} {c : Char} : s.get 0 = c ↔ (∃ cs, s.data = c :: cs) ∨ s.data = [] ∧ c = default := by
    dsimp [String.get]
    cases s.data with
    | nil =>
      rw [or_iff_right]
      · dsimp [String.utf8GetAux]
        trans c = default
        · constructor <;> (rintro rfl; rfl)
        · simp
      · nofun
    | cons c cs =>
      dsimp [String.utf8GetAux]
      constructor
      · rintro rfl
        left
        exists cs
      · rintro (⟨_, _|_⟩|⟨_, _⟩)
        · rfl
        · contradiction

  theorem repr_non_neg {n : Nat} : n.repr.get 0 ≠ '-' := by
    have : ∀ c ∈ n.repr.data, c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨ c = '5' ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9' := by
      unfold Nat.repr toDigits

      generalize digits_eq : [] = digits
      generalize n + 1 = k

      have : ∀ c ∈ digits, c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨ c = '5' ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9' := by
        rw [← digits_eq]
        rintro _ (_|_)
      clear digits_eq

      induction k, n, digits using toDigitsCore.induct' 10 with
      | case1 x ds =>
        erwa [List.data_asString]
      | case2 fuel n ds h =>
        dsimp [toDigitsCore]
        rw [h, List.data_asString, ite_cond_eq_true _ _ (eq_true (rfl : 0 = 0))]
        intros c c_in
        apply List.eq_or_mem_of_mem_cons at c_in
        obtain rfl|c_in := c_in
        · have : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
            omega
          obtain h|h|h|h|h|h|h|h|h|h := this <;> {
            rw [h]
            dsimp [digitChar, Char.toNat]
            simp
          }
        · apply this
          assumption
      | case3 fuel n ds h IH =>
        dsimp [toDigitsCore]
        rw [ite_cond_eq_false _ _ (eq_false h)]
        apply IH
        intros c c_in
        apply List.eq_or_mem_of_mem_cons at c_in
        obtain rfl|c_in := c_in
        · have : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
            omega
          obtain h|h|h|h|h|h|h|h|h|h := this <;> {
            rw [h]
            dsimp [digitChar, Char.toNat]
            simp
          }
        · apply this
          assumption

    intro h
    rw [String.get_0_eq_iff] at h
    obtain ⟨cs, h⟩|⟨h, _⟩ := h
    · rw [h] at this
      simp_all
    · unfold Nat.repr toDigits at h
      have : (toDigitsCore 10 (n + 1) n []).isEmpty = false := toDigitsCore_non_empty_of_succ
      rw [List.data_asString] at h
      rw [List.isEmpty_eq_false_iff, h] at this
      contradiction

  theorem repr_toInt? {n : Nat} : n.repr.toInt? = .some n := by
    unfold String.toInt?
    repeat erw [Nat.repr_toNat?];
    split using h
    · absurd h
      exact Nat.repr_non_neg
    · rfl

  theorem repr_toInt! {n : Nat} : n.repr.toInt! = n := by
    unfold String.toInt!
    rw [Nat.repr_toInt?]
end Nat
