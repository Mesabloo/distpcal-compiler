import CustomPrelude
import Mathlib.Data.List.Induction
import Batteries.Data.String.Lemmas
import Batteries.Data.Nat.Digits
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

  theorem le_pred_of_succ_le {m n : ℕ} (h : m + 1 ≤ n) : m ≤ n - 1 := by
    grind only

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
    · have h : n > k := by obtain _|_ := Nat.eq_or_lt_of_not_lt h₂ <;> trivial
      apply div_lt_self
      · trans k
        · trans 1
          · exact Nat.one_pos
          · assumption
        · assumption
      · assumption

  -- https://github.com/leanprover/lean4/pull/12445
  section UpgradeLean

    -- todo: lemmas about `ToString Nat` and `ToString Int`

    variable {n b : Nat}

    private theorem isDigit_of_mem_toDigitsCore {c cs fuel}
        (hc : c ∈ cs → c.isDigit) (hb₁ : 0 < b) (hb₂ : b ≤ 10) (h : c ∈ toDigitsCore b fuel n cs) :
        c.isDigit := by
      induction fuel generalizing n cs with rw [toDigitsCore] at h
      | zero => exact hc h
      | succ _ ih =>
        split at h
        case' isFalse => apply ih (fun h => ?_) h
        all_goals
          cases h with
          | head      => simp [Nat.lt_of_lt_of_le (mod_lt _ hb₁) hb₂]
          | tail _ hm => exact hc hm

    private theorem toDigitsCore_of_lt_base {cs fuel} (hb : n < b) (hf : n < fuel) :
        toDigitsCore b fuel n cs = n.digitChar :: cs := by
      unfold toDigitsCore
      split <;> simp_all [mod_eq_of_lt]

    private theorem toDigitsCore_append {fuel cs₁ cs₂} :
        toDigitsCore b fuel n cs₁ ++ cs₂ = toDigitsCore b fuel n (cs₁ ++ cs₂) := by
      induction fuel generalizing n cs₁ with simp only [toDigitsCore]
      | succ => split <;> simp_all

    private theorem toDigitsCore_eq_toDigitsCore_nil_append {fuel cs₁} :
        toDigitsCore b fuel n cs₁ = toDigitsCore b fuel n [] ++ cs₁ := by
      simp [toDigitsCore_append]

    private theorem toDigitsCore_eq_of_lt_fuel {n} {fuel₁ fuel₂ cs} (hb : 1 < b) (h₁ : n < fuel₁) (h₂ : n < fuel₂) :
        toDigitsCore b fuel₁ n cs = toDigitsCore b fuel₂ n cs := by
      cases fuel₁ <;> cases fuel₂ <;> try contradiction
      simp only [toDigitsCore, Nat.div_eq_zero_iff]
      split
      · simp
      · have := Nat.div_lt_self (by omega : 0 < n) hb
        exact toDigitsCore_eq_of_lt_fuel hb (by omega) (by omega)

    private theorem toDigitsCore_toDigitsCore {d fuel nf df cs}
        (hb : 1 < b) (hn : 0 < n) (hd : d < b) (hf : b * n + d < fuel) (hnf : n < nf) (hdf : d < df) :
        toDigitsCore b nf n (toDigitsCore b df d cs) = toDigitsCore b fuel (b * n + d) cs := by
      cases fuel with
      | zero => contradiction
      | succ fuel =>
        rw [toDigitsCore]
        split
        case isTrue h =>
          have : b ≤ b * n + d := Nat.le_trans (Nat.le_mul_of_pos_right _ hn) (le_add_right _ _)
          cases Nat.div_eq_zero_iff.mp h <;> omega
        case isFalse =>
          have h : (b * n + d) / b = n := by
            rw [mul_add_div (by omega), Nat.div_eq_zero_iff.mpr (.inr hd), Nat.add_zero]
          have := (Nat.lt_mul_iff_one_lt_left hn).mpr hb
          simp only [toDigitsCore_of_lt_base hd hdf, mul_add_mod_self_left, mod_eq_of_lt hd, h]
          apply toDigitsCore_eq_of_lt_fuel hb hnf (by omega)

    theorem toDigits_of_base_le (hb : 1 < b) (h : b ≤ n) :
        toDigits b n = toDigits b (n / b) ++ [digitChar (n % b)] := by
      have := Nat.div_add_mod n b
      rw (occs := [1]) [← Nat.div_add_mod n b,
        ← toDigits_append_toDigits (by omega) (Nat.div_pos_iff.mpr (by omega)) (Nat.mod_lt n (by omega))]
      rw [toDigits_of_lt_base (n := n % b) (Nat.mod_lt n (by omega))]

    theorem toDigits_eq_if (hb : 1 < b) :
        toDigits b n = if n < b then [digitChar n] else toDigits b (n / b) ++ [digitChar (n % b)] := by
      split
      · rw [toDigits_of_lt_base ‹_›]
      · rw [toDigits_of_base_le hb (by omega)]

    theorem length_toDigits_pos {b n : Nat} :
        0 < (Nat.toDigits b n).length := by
      simp [toDigits]
      rw [toDigitsCore]
      split
      · simp
      · rw [toDigitsCore_eq_toDigitsCore_nil_append]
        simp

    theorem length_toDigits_le_iff {n k : Nat} (hb : 1 < b) (h : 0 < k) :
        (Nat.toDigits b n).length ≤ k ↔ n < b ^ k := by
      match k with
      | 0 => contradiction
      | k + 1 =>
        induction k generalizing n
        · rw [toDigits_eq_if hb]
          split <;> simp [*, length_toDigits_pos, ← Nat.pos_iff_ne_zero, - List.length_eq_zero_iff]
        · rename_i ih
          rw [toDigits_eq_if hb]
          split
          · rename_i hlt
            simp [Nat.pow_add]
            refine Nat.lt_of_lt_of_le hlt ?_
            apply Nat.le_mul_of_pos_left
            apply Nat.mul_pos
            · apply Nat.pow_pos
              omega
            · omega
          · simp [ih (n := n / b) (by omega), Nat.div_lt_iff_lt_mul (k := b) (by omega), Nat.pow_add]

    theorem repr_eq_ofList_toDigits {n : Nat} :
        n.repr = .ofList (toDigits 10 n) :=
      (rfl)

    theorem toString_eq_ofList_toDigits {n : Nat} :
        toString n = .ofList (toDigits 10 n) :=
      (rfl)

    @[simp, grind norm]
    theorem toString_eq_repr {n : Nat} :
        toString n = n.repr :=
      (rfl)

    @[simp, grind norm]
    theorem reprPrec_eq_repr {n i : Nat} :
        reprPrec n i = n.repr :=
      (rfl)

    @[simp, grind norm]
    theorem repr_eq_repr {n : Nat} :
        repr n = n.repr :=
      (rfl)

    theorem repr_of_lt {n : Nat} (h : n < 10) :
        n.repr = .singleton (digitChar n) := by
      rw [repr_eq_ofList_toDigits, toDigits_of_lt_base h, String.singleton_eq_ofList]

    theorem repr_of_ge {n : Nat} (h : 10 ≤ n) :
        n.repr = (n / 10).repr ++ .singleton (digitChar (n % 10)) := by
      simp [repr_eq_ofList_toDigits, toDigits_of_base_le (by omega) h, String.singleton_eq_ofList,
        String.ofList_append]

    theorem repr_eq_repr_append_repr {n : Nat} (h : 10 ≤ n) :
        n.repr = (n / 10).repr ++ (n % 10).repr := by
      rw [repr_of_ge h, repr_of_lt (n := n % 10) (by omega)]

    theorem length_repr_pos {n : Nat} :
        0 < n.repr.length := by
      simpa [repr_eq_ofList_toDigits] using length_toDigits_pos

    theorem length_repr_le_iff {n k : Nat} (h : 0 < k) :
        n.repr.length ≤ k ↔ n < 10 ^ k := by
      simpa [repr_eq_ofList_toDigits] using length_toDigits_le_iff (by omega) h

  end UpgradeLean

  theorem String.digitChar_isDigit {n : Nat} (h : n < 10) : n.digitChar.isDigit := by
    decide +revert +kernel

  def toDigitsCore.induct' (base : ℕ) {motive : ℕ → ℕ → List Char → Prop}
    (case1 : ∀ (x : ℕ) (ds : List Char), motive 0 x ds)
    (case2 : ∀ (fuel n : ℕ) (ds : List Char), n / base = 0 → motive fuel.succ n ds)
    (case3 : ∀ (fuel n : ℕ) (ds : List Char), ¬n / base = 0 → motive fuel (n / base) ((n % base).digitChar :: ds) → motive fuel.succ n ds)
    (k n : ℕ) (ds : List Char) :
      motive k n ds :=
    Nat.toDigitsCore.induct base motive case1 case2 case3 k n ds

  theorem toDigitsCore_eq_append {base k n : Nat} {ds : List Char} : toDigitsCore base k n ds = toDigitsCore base k n [] ++ ds := by
    conv_lhs => enter [4]; rw [← List.nil_append ds]
    grind only [toDigitsCore_append]

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

  -- theorem String.endPos_empty : "".endPos = 0 := by rfl

  -- theorem String.endPos_cons {c cs} : (String.mk (c :: cs)).endPos = (String.mk cs).endPos + c := by
  --   repeat rw [String.endPos, String.utf8ByteSize]
  --   dsimp
  --   rw [String.Pos.addChar_eq]

  -- theorem String.foldl_nil {α} {f : α → Char → α} {init : α} : String.foldl f init "" = init := by
  --   rw [String.foldl, String.foldlAux, String.endPos_empty]
  --   split_ifs <;> trivial

  -- theorem String.Pos.add_comm {p₁ p₂ : String.Pos} : p₁ + p₂ = p₂ + p₁ := by
  --   rw [String.Pos.add_eq, String.Pos.add_eq, Nat.add_comm]

  -- -- theorem String.foldlAux_shunt {α} {f : α → Char → α} {init : α} {c : Char} {s : List Char} :
  -- --     String.foldlAux f {data := c :: s} ({ data := s : String}.endPos + c) { byteIdx := c.utf8Size } init =
  -- --       String.foldlAux f {data := s} ({data := s : String}.endPos) 0 init := by
  -- --   conv_lhs => enter [4]; change { byteIdx := c.utf8Size } + 0

  -- --   fun_induction String.foldlAux f ⟨s⟩ (String.endPos ⟨s⟩) 0 init with
  -- --   | case1 i init h _ IH =>
  -- --     unfold String.foldlAux
  -- --     split_ifs with h'
  -- --     · dsimp
  -- --       rw [← IH]
  -- --       congr 1
  -- --       · rw [String.next_cons_of_ge]
  -- --         · repeat rw [String.Pos.add_eq, String.Pos.sub_eq]
  -- --           congr
  -- --           simp
  -- --         · change _ ≤ _ + _
  -- --           rw [String.Pos.add_eq, String.Pos.le_iff]
  -- --           simp
  -- --       · congr 1
  -- --         conv_lhs => enter [2]; rw [String.Pos.add_comm, String.Pos.add_eq]; change i + c
  -- --         conv_rhs => rw [← String.get_skip_first (c := c)]
  -- --     · dsimp
  -- --       conv at h' => enter [1, 1]; rw [String.Pos.add_comm, String.Pos.add_eq]; change i + c
  -- --       repeat rw [String.Pos.addChar_eq] at h'
  -- --       erw [String.Pos.lt_iff, Nat.add_lt_add_iff_right, ← String.Pos.lt_iff] at h'
  -- --       contradiction
  -- --   | case2 i init h =>
  -- --     unfold String.foldlAux
  -- --     split_ifs with h'
  -- --     · rw [String.Pos.addChar_eq, String.Pos.add_eq, Nat.add_comm] at h'
  -- --       dsimp at h'
  -- --       rw [Nat.add_lt_add_iff_right] at h'
  -- --       contradiction
  -- --     · rfl

  -- theorem String.foldl_eq_foldl {α} {f : α → Char → α} {init : α} {s : String} : String.foldl f init s = List.foldl f init s.data := String.foldl_eq f s init
  --   -- let ⟨ss⟩ := s
  --   -- dsimp
  --   -- induction ss generalizing init with
  --   -- | nil =>
  --   --   rw [List.foldl_nil, String.foldl_nil]
  --   -- | cons c s IH =>
  --   --   rw [List.foldl_cons, String.foldl, String.foldlAux]
  --   --   split_ifs with h₁
  --   --   · dsimp
  --   --     rw [String.get_cons_0, String.next_cons_0, String.foldlAux_shunt, ← String.foldl]
  --   --     apply IH
  --   --   · apply Nat.ge_of_not_lt at h₁
  --   --     change 0 ≥ _ at h₁
  --   --     rw [String.endPos_cons, String.Pos.addChar_eq] at h₁

  --   --     have : c.utf8Size > 0 := by
  --   --       dsimp [Char.utf8Size]
  --   --       split_ifs <;> trivial

  --   --     simp_all

  -- theorem String.isEmpty_append {s s' : String} : (s ++ s').isEmpty = (s.isEmpty && s'.isEmpty) := by
  --   let ⟨cs⟩ := s
  --   let ⟨cs'⟩ := s'
  --   match cs, cs' with
  --   | [], [] => rfl
  --   | [], _ :: _ => erw [String.empty_append, String.empty_isEmpty, Bool.true_and]
  --   | _ :: _, [] => erw [String.append_empty, String.empty_isEmpty, Bool.and_true]
  --   | _ :: _, _ :: _ => erw [String.cons_non_empty, String.cons_non_empty, String.cons_non_empty]; rfl

  theorem add_ge_add_iff_right {k m n : Nat} : k + n ≥ m + n ↔ k ≥ m := Nat.add_le_add_iff_right

  theorem repr_not_empty {n : Nat} : ¬n.repr = "" := by
    unfold Nat.repr toDigits toDigitsCore
    extract_lets +lift d n'
    split_ifs with h
    · simp
    · simp [toDigitsCore_eq_append (ds := [d])]

  lemma toNat_digitChar_of_lt_ten {n : Nat} (h : n < 10) : n.digitChar.toNat = n + 48 := by
    have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega

    rcases this with _|_|_|_|_|_|_|_|_|_
      <;> subst n
      <;> rfl

  theorem zero_toNat : '0'.toNat = 48 := (rfl)

  lemma _root_.Bool.or_true_false : (true || false) = true := rfl

  theorem toNat?_append_singleton {s c} (h : c.isDigit) (h' : s.isEmpty = false) : (s ++ String.singleton c).toNat? = (s.dropEndWhile '_').toNat? <&> λ k ↦ k * 10 + (c.toNat - 48) := by
    unfold String.toNat? String.Slice.toNat?

    have h'' : (s ++ String.singleton c).isEmpty = false := by
      grind only [String.isEmpty_append_iff]

    split_ifs with h₁ h₂ h₃
    · congr

      have underscore_not_digit : ¬'_'.isDigit := by simp
      have c_neq : c ≠ '_' := by rintro rfl; contradiction

      repeat erw [String.toSlice_foldl]
      admit
    · exfalso
      admit
    · exfalso
      admit
    · rfl

  theorem repr_toNat? {n : Nat} : n.repr.toNat? = .some n := by
    induction n using div.induct' 10 (by simp only [gt_iff_lt, reduceLT]) with
    | base₁ n n_lt =>
      rw [repr_of_lt n_lt]

      have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega

      rcases this with _|_|_|_|_|_|_|_|_|_
        <;> subst n
        -- TODO: get rid of `decide +native`
        <;> decide +native
    | base₂ =>
      -- TODO: get rid of `decide +native`
      decide +native
    | ind n n_gt IH =>
      apply Nat.le_of_lt at n_gt

      admit
      -- erw [repr_of_ge n_gt, toNat?_append_singleton, IH, Option.some.injEq]
      -- · change (n / 10) * 10 + _ = n

      --   have : n % 10 < 10 := by omega
      --   rw [toNat_digitChar_of_lt_ten this, Nat.add_sub_cancel]
      --   generalize k_eq : n % 10 = k at this ⊢

      --   have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega

      --   rcases this with this|this|this|this|this|this|this|this|this|this
      --     <;> subst this
      --     <;> omega
      -- · grind only [String.digitChar_isDigit]
      -- · grind only [String.isEmpty_iff, repr_not_empty]

  theorem repr_front?_isDigit {n : Nat} {c : Char} (h : n.repr.front? = some c) : c.isDigit := by
    unfold Nat.repr toDigits at h
    rw [String.front?_ofList] at h

    have : toDigitsCore 10 (n + 1) n [] ≠ [] :=
      propext List.isEmpty_eq_false_iff ▸ toDigitsCore_non_empty_of_succ
    obtain ⟨c', _, h'⟩ := List.exists_cons_of_ne_nil this
    rw [h', List.head?_cons] at h
    injection h
    subst c'

    have : c ∈ toDigitsCore 10 (n + 1) n [] := by simp [*]
    exact isDigit_of_mem_toDigitsCore (by simp) (by omega) (by omega) this

  theorem repr_toInt? {n : Nat} : n.repr.toInt? = .some n := by
    unfold String.toInt? String.Slice.toInt?
    split_ifs with h
    · absurd h; clear h

      have n_repr_not_empty : ¬ n.repr.isEmpty := by
        rw [String.isEmpty_iff]
        apply repr_not_empty

      obtain ⟨c, front_eq⟩ : ∃ c, n.repr.front? = some c := by
        have : n.repr.toSlice.startPos ≠ n.repr.toSlice.endPos := by
          rw [← String.isEmpty_toSlice] at n_repr_not_empty
          apply String.Slice.startPos_ne_endPos_of_non_empty
          assumption
        exists n.repr.toSlice.startPos.get this
        unfold String.front? String.Slice.front? String.Slice.Pos.get?
        rw [dif_neg this]

      have := repr_front?_isDigit front_eq
      rw [← String.toSlice_front?] at front_eq
      unfold String.Slice.front
      rw [front_eq]
      rintro rfl
      contradiction
    · rw [← String.toNat?, repr_toNat?]
      rfl

  theorem repr_toInt! {n : Nat} : n.repr.toInt! = n := by
    unfold String.toInt! String.Slice.toInt!
    rw [← String.toInt?, Nat.repr_toInt?]
end Nat
