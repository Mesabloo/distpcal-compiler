import Mathlib.Data.List.Basic
import Init.Data.List.Attach
import Init.Data.List.Zip
import Extra.Prod
import Mathlib.Algebra.Group.Defs
--import Init.Tactics
import Mathlib.Data.List.Sigma
import CustomPrelude
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Dedup

namespace List
  variable {α β γ : Type _}

  inductive Exists (P : α → Prop) : List α → Prop where
    | here {x} (xs) : P x → Exists P (x :: xs)
    | there (x) {xs} : Exists P xs → Exists P (x :: xs)

  theorem exists_iff_exists_mem (p : α → Prop) {xs : List α} : Exists p xs ↔ ∃ x ∈ xs, p x := by
    induction xs with
    | nil =>
      constructor <;> intro h
      · contradiction
      · obtain ⟨_, _|_⟩ := h
    | cons x xs IH =>
      constructor <;> intro h
      · obtain _|⟨_, h⟩ := h
        · refine ⟨x, ?_, ?_⟩
          · exact mem_cons_self
          · assumption
        · obtain ⟨y, y_in_xs, p_y⟩ := IH.mp h
          refine ⟨y, ?_, ?_⟩
          · exact mem_cons_of_mem _ y_in_xs
          · assumption
      · obtain ⟨y, y_in_x_xs, p_y⟩ := h
        obtain _|⟨_, y_in_xs⟩ := y_in_x_xs
        · apply Exists.here
          assumption
        · apply Exists.there
          apply IH.mpr
          refine ⟨y, ?_, ?_⟩
          · assumption
          · assumption

  instance (p : α → Prop) [DecidablePred p] : DecidablePred (Exists p) :=
    λ _ ↦ decidable_of_iff' _ (exists_iff_exists_mem p)

  theorem takeWhile_neg_eq {p : α → Bool} {x} {xs} (h : p x = false) : takeWhile p (x :: xs) = [] := by
    simp only [takeWhile, h]

  theorem takeWhile_pos_eq {p : α → Bool} {x} {xs} (h : p x = true) : takeWhile p (x :: xs) = x :: takeWhile p xs := by
    simp only [takeWhile, h]

  theorem dropWhile_neg_eq {p : α → Bool} {x} {xs} (h : p x = false) : dropWhile p (x :: xs) = x :: xs := by
    simp only [dropWhile, h]

  theorem dropWhile_pos_eq {p : α → Bool} {x} {xs} (h : p x = true) : dropWhile p (x :: xs) = dropWhile p xs := by
    simp only [dropWhile, h]

  private theorem span.loop_eq_takeWhile_dropWhile {xs ys : List _} {p : α → Bool}
    : span.loop p xs ys = (ys.reverse ++ xs.takeWhile p, xs.dropWhile p) := by
      induction xs generalizing ys with
        | nil => simp [loop, takeWhile, dropWhile]
        | cons x xs IH =>
          cases h : p x with
            | false => simp [loop, h, takeWhile_neg_eq h, dropWhile_neg_eq h]
            | true => simp [takeWhile_pos_eq h, dropWhile_pos_eq h, loop, h, @IH (x :: ys)]

  -- theorem span_eq_takeWhile_dropWhile {xs : List _} {p : α → Bool} : xs.span p = (xs.takeWhile p, xs.dropWhile p) := by
  --   simpa using span.loop_eq_takeWhile_dropWhile

  theorem mem_takeWhile {p : α → Bool} {x y} {ys} (h : x ∈ takeWhile p (y :: ys)) : (x = y ∧ p x) ∨ x ∈ takeWhile p ys := by
    unfold takeWhile at h
    split at h
    · rcases List.mem_cons.mp h
      · subst_eqs
        exact Or.inl ⟨Eq.refl x, ‹_›⟩
      · exact Or.inr ‹_›
    · contradiction

  theorem mem_takeWhile_satisfies {xs : List _} {p : α → Bool} {x} (h : x ∈ xs.takeWhile p) : p x := by
    induction xs with
      | nil => contradiction
      | cons y ys IH =>
        if h' : x = y then
          rcases mem_takeWhile h with ⟨_, h''⟩|h''
          · assumption
          · exact IH h''
        else if h' : p y then
          rw [takeWhile_pos_eq h'] at h
          rcases mem_cons.mp h with _|h''
          · contradiction
          · exact IH h''
        else
          simp [takeWhile_neg_eq (eq_false_of_ne_true h')] at h

  theorem elem_iff_mem [BEq α] [LawfulBEq α] {x : α} {ys : List α} : List.elem x ys ↔ x ∈ ys :=
    ⟨mem_of_elem_eq_true, elem_eq_true_of_mem⟩

  private theorem not_iff_not : ∀ {b : Bool}, !b ↔ ¬b := by simp

  theorem notElem_iff_not_mem [BEq α] [LawfulBEq α] {x : α} {ys : List α} : !List.elem x ys ↔ x ∉ ys := by
    rw [not_iff_not]
    exact not_congr elem_iff_mem

  theorem mem_removeAll_iff [BEq α] [LawfulBEq α] {x : α} {xs ys : List α}
    : x ∈ removeAll xs ys ↔ x ∈ xs ∧ x ∉ ys := by
    calc
      x ∈ removeAll xs ys ↔ x ∈ filter (λ y => !elem y ys) xs := by rw [removeAll]
      _ ↔ x ∈ xs ∧ !elem x ys := mem_filter
      _ ↔ x ∈ xs ∧ x ∉ ys := by rw [notElem_iff_not_mem]

  theorem sum_replicate_eq {m n : Nat} : (replicate m n).sum = m * n := by
    induction m with
    | zero => simp +arith
    | succ m IH => simp +arith [List.replicate_succ, IH, Nat.add_one_mul]

  theorem sum_map_const {n : Nat} {xs : List α} : (List.map (λ _ => n) xs).sum = xs.length * n := by
    simp

  theorem sum_map_length {f : α → List β} {xs : List α} (h : ∃ x ∈ xs, (f x).length > 0) : (List.map (List.length ∘ f) xs).sum > 0 := by
    induction xs with
    | nil => obtain ⟨_, _|_, _⟩ := h
    | cons x xs IH =>
      obtain ⟨y, _|⟨_, y_in_xs⟩, f_y_length_gt_0⟩ := h
      · rw [List.sum, List.map_cons, List.foldr_cons]
        exact Nat.add_pos_left f_y_length_gt_0 _
      · specialize IH ⟨y, y_in_xs, f_y_length_gt_0⟩
        rw [List.sum, List.map_cons, List.foldr_cons]
        exact Nat.add_pos_right _ IH

  theorem mem_map_if_mem {x : α} {xs : List α} {f : α → β} : x ∈ xs → f x ∈ xs.map f := by
    induction xs with
    | nil => nofun
    | cons y xs IH =>
      rintro (_|⟨_, x_in_xs⟩) <;> rw [List.map_cons]
      · exact mem_cons_self --(f x) (map f xs)
      · exact mem_cons_of_mem (f y) (IH x_in_xs)

  theorem prefix_append' {xs ys zs : List α} : xs <+: ys → xs <+: ys ++ zs := by
    rintro ⟨ws, xs_append_ws_eq_ys⟩
    refine ⟨ws ++ zs, ?_⟩
    rw [← append_assoc, xs_append_ws_eq_ys]

  theorem attachWith_eq_cons_exists_cons {zs} {Q : α → Prop} (R : ∀ z ∈ zs, Q z) {x xs} : zs.attachWith Q R = x :: xs → ∃ z zs', zs = z :: zs' := by
    cases zs with
    | nil => nofun
    | cons z zs =>
      intro _
      exists z, zs

  theorem forall₂_attachWith (P : α → β → Prop) {Q : α → Prop} (xs : List α) (R : ∀ x ∈ xs, Q x) (ys : List β) :
    Forall₂ (λ x y ↦ P x.val y) (xs.attachWith Q R) ys ↔ Forall₂ P xs ys where
      mp forall_xs_ys := by
        generalize xs'_eq : xs.attachWith Q R = xs' at forall_xs_ys
        induction forall_xs_ys generalizing xs with
        | nil =>
          obtain rfl := attachWith_eq_nil_iff.mp xs'_eq
          exact Forall₂.nil
        | @cons x y xs ys Pxy _ IH =>
          obtain ⟨z, zs', rfl⟩ := attachWith_eq_cons_exists_cons _ xs'_eq
          rw [attachWith_cons] at xs'_eq
          injection xs'_eq with x_eq xs_eq
          apply Forall₂.cons
          · subst x_eq
            exact Pxy
          · apply IH zs'
            exact xs_eq
      mpr forall_xs_ys := by
        induction forall_xs_ys with
        | nil => exact Forall₂.nil
        | @cons x y xs ys Pxy _ IH =>
          rw [attachWith_cons]
          apply Forall₂.cons
          · exact Pxy
          · apply IH

  def induction₂ {α β : Type _} {motive : (xs : List α) → (ys : List β) → xs.length = ys.length → Prop} (nil_nil : motive [] [] rfl) (cons_cons : ∀ x xs y ys, (len_eq : xs.length = ys.length) → motive xs ys len_eq → motive (x :: xs) (y :: ys) (Nat.succ_inj.mpr len_eq)) :
    (xs : List α) → (ys : List β) → (len_eq : xs.length = ys.length) → motive xs ys len_eq
    | [], [], _ => nil_nil
    | _ :: _, _ :: _, len_eq => cons_cons _ _ _ _ (Nat.succ_inj.mp len_eq) (List.induction₂ nil_nil cons_cons _ _ _)

  def induction₂' {α β : Type _} {motive : List α → List β → Sort _} (nil_nil : motive [] []) (nil_cons : ∀ y ys, motive [] (y :: ys)) (cons_nil : ∀ x xs, motive (x :: xs) []) (cons_cons : ∀ x y xs ys, motive xs ys → motive (x :: xs) (y :: ys)) :
      (xs : List α) → (ys : List β) → motive xs ys
    | [], [] => nil_nil
    | [], y :: ys => nil_cons y ys
    | x :: xs, [] => cons_nil x xs
    | x :: xs, y :: ys => cons_cons x y xs ys (induction₂' nil_nil nil_cons cons_nil cons_cons xs ys)

  private lemma forall₂_of_equiv_lists {α} (P : α → Prop) {xs : List α} {ys : List {x // P x}} (R : (x : α) → P x → α → Prop) (R_refl : ∀ x : α, (h : P x) → R x h x) (list_eq : xs = ys.map Subtype.val) :
    List.Forall₂ (λ ⟨x, h⟩ y ↦ R x h y) ys xs := by
      have len_eq : xs.length = ys.length := by
        rw [list_eq, List.length_map]

      induction xs, ys, len_eq using List.induction₂ with
      | nil_nil => apply List.Forall₂.nil
      | cons_cons x xs y ys _ IH =>
        injection list_eq with x_eq xs_eq
        apply List.Forall₂.cons
        · subst x_eq
          apply R_refl
        · apply IH
          exact xs_eq

  theorem forall₂_of_attachWith {α} {xs : List α} (P : α → Prop) (H : ∀ (x : α), x ∈ xs → P x)
                                (R : (x : α) → P x → α → Prop) (R_refl : ∀ x : α, (h : P x) → R x h x) :
    List.Forall₂ (λ ⟨x, h⟩ y ↦ R x h y) (xs.attachWith P H) xs := by
      apply forall₂_of_equiv_lists
      · exact R_refl
      · rw [List.attachWith, List.map_pmap, List.pmap_eq_map, List.map_id']

  theorem forall₂_of_attachWith' {α} {xs : List α} (P : α → Prop) (H : ∀ (x : α), x ∈ xs → P x)
                                 (R : {x // P x} → α → Prop) (R_refl : ∀ x : α, (h : P x) → R ⟨x, h⟩ x) :
    List.Forall₂ (λ x y ↦ R x y) (xs.attachWith P H) xs :=
      forall₂_of_attachWith P H _ R_refl

  theorem forall₂_transitivity {α β γ} {xs : List α} {ys : List β} {zs : List γ}
                               (P : α → β → Prop) (Q : β → γ → Prop) (R : α → γ → Prop)
                               (P_Q_imp_R : ∀ x y z, P x y → Q y z → R x z) :
    List.Forall₂ P xs ys → List.Forall₂ Q ys zs → List.Forall₂ R xs zs := by
      intros P_xs_ys Q_ys_zs

      induction P_xs_ys generalizing zs <;> obtain _|_ := Q_ys_zs
      case nil => apply List.Forall₂.nil
      case cons IH _ _ _ _ =>
        apply List.Forall₂.cons
        · apply P_Q_imp_R <;> assumption
        · apply IH
          assumption

  theorem Forall₂.flip_iff {α β} {xs : List α} {ys : List β} (R : α → β → Prop) : Forall₂ (_root_.flip R) ys xs ↔ Forall₂ R xs ys := by
    constructor
    · exact flip
    · exact flip

  theorem forall₂_iff_forall₂_attach {α β} {xs : List α} {ys : List β} (R : α → β → Prop) :
    List.Forall₂ (λ x y ↦ R x.val y.val) xs.attach ys.attach ↔ List.Forall₂ R xs ys := by
      calc
        _ ↔ List.Forall₂ (λ x y ↦ R x.val y.val) (xs.attachWith (λ x ↦ x ∈ xs) (λ _ ↦ id)) (ys.attachWith (λ x ↦ x ∈ ys) (λ _ ↦ id)) := Iff.rfl
        _ ↔ List.Forall₂ (λ x y ↦ R x y.val) xs (ys.attachWith (λ x ↦ x ∈ ys) (λ _ ↦ id)) := forall₂_attachWith (λ x y ↦ R x y.val) _ _ (ys.attachWith (λ x ↦ x ∈ ys) (λ _ ↦ id))
        _ ↔ List.Forall₂ (λ y x ↦ R x y.val) (ys.attachWith (λ x ↦ x ∈ ys) (λ _ ↦ id)) xs := Forall₂.flip_iff _
        _ ↔ List.Forall₂ (flip R) ys xs := forall₂_attachWith (flip R) _ _ _
        _ ↔ List.Forall₂ R xs ys := Forall₂.flip_iff _

  def filterWhile {α β : Type _} (f : α → Option β) : List α → List β
    | [] => []
    | x :: xs => match f x with
      | some x => x :: xs.filterWhile f
      | none => []

  @[inline]
  def zip₃ {α β γ : Type _} : List α → List β → List γ → List (α × β × γ) := zipWith₃ (·, ·, ·)

  def unzip₃ {α β γ : Type _} : List (α × β × γ) → List α × List β × List γ
    | [] => ⟨[], [], []⟩
    | ⟨x, y, z⟩ :: ts => let ⟨xs, ys, zs⟩ := unzip₃ ts; ⟨x :: xs, y :: ys, z :: zs⟩

  lemma unzip₃_length {α β γ} {xs : List (α × β × γ)} : (unzip₃ xs).fst.length = (unzip₃ xs).snd.fst.length ∧ (unzip₃ xs).snd.fst.length = (unzip₃ xs).snd.snd.length := by
    induction xs with
    | nil => trivial
    | cons _ _ IH => simp [unzip₃, IH]

  lemma unzip₃_snd {α β γ} {xs : List (α × β × γ)} : (unzip₃ xs).snd = unzip (unzip xs).snd := by
    induction xs with
    | nil => rfl
    | cons x xs IH => simp [unzip₃, unzip, IH]

  lemma length_cons_eq_if {α β} {x : α} {xs} {y : β} {ys} (h : xs.length = ys.length) : (x :: xs).length = (y :: ys).length := Nat.succ_inj.mpr h

  lemma max?_of_map_const_getD_eq {α β} [Max β] [Std.IdempotentOp (max : β → β → β)] [Std.Associative (max : β → β → β)] {xs : List α} {n : β} (f : α → β) (f_const : ∀ x, f x = n) : (xs.map f).max?.getD n = n := by
    induction xs with
    | nil => simp
    | cons x xs IH =>
      simp only [map_cons, max?_cons', List.foldl_max, Option.getD_some, f_const, IH, Std.IdempotentOp.idempotent]

  lemma prop_satisfies_elem_of_unattach {α} {p : α → Prop} {xs : List {x : α // p x}} : ∀ x ∈ xs.unattach, p x := by
    intros y xs_in_unattach
    generalize ys_eq : xs.unattach = ys at xs_in_unattach
    induction xs_in_unattach generalizing xs with
    | head ys' =>
      rw [List.unattach, List.map_eq_cons_iff] at ys_eq
      obtain ⟨x, xs', rfl, rfl, _⟩ := ys_eq
      exact x.property
    | tail _ _ IH =>
      rw [List.unattach, List.map_eq_cons_iff] at ys_eq
      obtain ⟨x, xs', rfl, rfl, _⟩ := ys_eq
      apply IH
      assumption

  def unzipWith {α β γ} (f : α → β) (g : α → γ) : List α → List β × List γ
    | [] => ⟨[], []⟩
    | x :: xs => Prod.map (cons <| f x) (cons <| g x) <| xs.unzipWith f g

  -- `unzip` is a special case of `unzipWith`
  theorem unzip_eq_unzipWith {α β} {xs : List (α × β)} : xs.unzip = xs.unzipWith Prod.fst Prod.snd := by
    induction xs with
    | nil => rfl
    | cons x xs IH => simp [unzipWith.eq_2, IH, Prod.map]

  instance {α : Type _} : Monoid (List α) where
    mul := (· ++ ·)
    mul_assoc := List.append_assoc
    one := []
    one_mul := List.nil_append
    mul_one := List.append_nil

  theorem mem_concat {α} {x y : α} {xs : List α} : x ∈ xs.concat y ↔ x ∈ xs ∨ x = y := by simp

  def foldlRecOn₂ {α β γ} {motive : β → γ → Sort _} :
    ∀ (l : List α) (op₁ : β → α → β) (op₂ : γ → α → γ) (b : β) (c : γ)
      (_ : motive b c) (_ : ∀ (b : β) (c : γ) {x : α} (_ : x ∈ l) (_ : motive b c), motive (op₁ b x) (op₂ c x)),
      motive (List.foldl op₁ b l) (List.foldl op₂ c l)
    | [], _, _, _, _, hl, _ => hl
    | x :: xs, op₁, op₂, b, c, hl, hb =>
      List.foldlRecOn₂ xs op₁ op₂ (op₁ b x) (op₂ c x) (hb b c List.mem_cons_self hl)
        λ b c _ x_in_l ↦ hb b c (List.mem_cons_of_mem _ x_in_l)

  def foldrRecOn₂ {α β γ} {motive : β → γ → Sort _} :
      ∀ (l : List α) (op₁ : α → β → β) (op₂ : α → γ → γ) (b : β) (c : γ)
        (_ : motive b c) (_ : ∀ (b : β) (c : γ) {x : α} (_ : x ∈ l) (_ : motive b c), motive (op₁ x b) (op₂ x c)),
        motive (List.foldr op₁ b l) (List.foldr op₂ c l)
    | [], _, _, _, _, hl, _ => hl
    | _ :: xs, op₁, op₂, b, c, hl, hb =>
      hb _ _ List.mem_cons_self <| List.foldrRecOn₂ xs op₁ op₂ b c hl
        λ b c _ x_in_l ↦ hb b c (List.mem_cons_of_mem _ x_in_l)

  theorem map_eq_foldl_concat {f : α → β} {xs : List α} : List.map f xs = List.foldl (init := []) (λ xs x ↦ xs.concat (f x)) xs := by
    change [] ++ List.map f xs = _
    generalize [] = r
    induction xs generalizing r with
    | nil => rw [List.foldl_nil, List.map_nil, List.append_nil]
    | cons x xs IH => rw [List.foldl_cons, List.map_cons, List.append_cons, ← List.concat_eq_append, IH]

  theorem foldl_concat_eq_append {xs ys : List α} : List.foldl (λ xs x ↦ xs.concat x) xs ys = xs ++ ys := by
    induction ys generalizing xs with
    | nil => rw [List.foldl_nil, List.append_nil]
    | cons y ys IH => rw [List.foldl_cons, IH, concat_append]

  theorem kreplace_nil.{v, u} {α : Type u} [DecidableEq α] {β : α → Type v} {k : α} {v : β k} : kreplace k v [] = [] := by
    rfl

  theorem kreplace_cons.{v, u} {α : Type u} [DecidableEq α] {β : α → Type v} {xs : List (Sigma β)} {k k' : α} {v : β k} {v' : β k'} :
    kreplace k v (⟨k', v'⟩ :: xs) = if k = k' then ⟨k, v⟩ :: xs else ⟨k', v'⟩ :: kreplace k v xs := by
      unfold kreplace
      by_cases k_eq : k = k'
      · conv_lhs => apply lookmap_cons_some _ _ (by simp [k_eq]; rfl)
        simp [k_eq]
      · conv_lhs => apply lookmap_cons_none _ _ (by simp [k_eq])
        simp [k_eq]

  theorem dlookup_kreplace.{v, u} {α : Type u} [DecidableEq α] {β : α → Type v} {x : List (Sigma β)} {k : α} {v : β k} :
    dlookup k (kreplace k v x) = Functor.mapConst v (dlookup k x) := by
      induction x with
      | nil => rfl
      | cons x xs IH =>
        let ⟨k', v'⟩ := x
        rw [kreplace_cons]
        by_cases k_eq : k = k'
        · subst k
          conv_lhs => enter [2]; apply ite_cond_eq_true _ _ (eq_true rfl)
          repeat rw [dlookup_cons_eq]
          rfl
        · conv_lhs => enter [2]; apply ite_cond_eq_false _ _ (eq_false k_eq)
          repeat rw [dlookup_cons_ne _ ⟨k', v'⟩ k_eq]
          exact IH

  theorem dlookup_kreplace_ne.{v, u} {α : Type u} [DecidableEq α] {β : α → Type v} {x : List (Sigma β)} {k k' : α} {v : β k'} (k_ne : k ≠ k') :
    dlookup k (kreplace k' v x) = dlookup k x := by
      induction x with
      | nil => rfl
      | cons x xs IH =>
        let ⟨k'', v''⟩ := x
        rw [kreplace_cons]
        by_cases k'_eq : k' = k''
        · subst k'
          conv_lhs => enter [2]; apply ite_cond_eq_true _ _ (eq_true rfl)
          repeat rw [dlookup_cons_ne _ ⟨k'', _⟩ k_ne]
        · conv_lhs => enter [2]; apply ite_cond_eq_false _ _ (eq_false k'_eq)
          by_cases k_eq : k = k''
          · subst k
            repeat rw [dlookup_cons_eq]
          · repeat rw [dlookup_cons_ne _ ⟨k'', _⟩ k_eq]
            exact IH

  -- theorem forIn_append {α β} {m : _ → _} [Monad m] [LawfulMonad m] {xs ys : List α} {b : β} {f : α → β → m (ForInStep β)} (h : ∀ x y, ∃ z, f x y = pure (ForInStep.yield z)) :
  --   forIn (xs ++ ys) b f = (do forIn ys (← forIn xs b f) f) := by
  --     induction xs generalizing b with
  --     | nil => simp_rw [nil_append, forIn_nil, pure_bind]
  --     | cons y ys IH =>
  --       simp_rw [cons_append, forIn_cons, IH]
  --       obtain ⟨z, eq⟩ := h y b
  --       simp [eq]

  -- theorem forIn'.loop.cons {m : _ → _} [Monad m] [LawfulMonad m] {α β} {xs ys : List α} {y : α} {f : (x : α) → x ∈ xs → β → m (ForInStep β)} {b : β}
  --   (h : ∃ zs, zs ++ y :: ys = xs) : forIn'.loop xs f (y :: ys) b h =
  --     (do match ← f y (by obtain ⟨bs, rfl⟩ := h; exact mem_append_right _ (Mem.head ..)) b with | .done b => pure b | .yield b => forIn'.loop xs f ys b (have ⟨bs, h⟩ := h; ⟨bs ++ [y], by rw [← h, append_cons _ y ys]⟩)) := by
  --   rfl

  theorem getLast_sizeOf_lt [SizeOf α] {xs : List α} (h : xs ≠ []) : sizeOf (xs.getLast h) < sizeOf xs := by
    fun_induction List.getLast xs h
    · simp +arith
    · rename sizeOf _ < sizeOf _ => IH
      trans
      · exact IH
      · simp +arith

  theorem dropLast_sizeOf_le [SizeOf α] {xs : List α} : sizeOf xs.dropLast ≤ sizeOf xs := by
    fun_induction List.dropLast xs
    · rfl
    · simp +arith [*]
    · simp +arith [*]

  theorem dropLast_getLast_add_sizeOf_eq [SizeOf α] {xs : List α} (h : xs ≠ []) : 1 + sizeOf xs.dropLast + sizeOf (xs.getLast h) = sizeOf xs := by
    fun_induction List.getLast xs h
    · simp +arith
    · rename 1 + sizeOf _ + sizeOf _ = sizeOf _ => IH
      simp_rw [List.cons.sizeOf_spec] at IH ⊢
      simp +arith [← IH]

  theorem forall₂_singleton {R : α → β → Prop} {x : α} {y : β} : List.Forall₂ R [x] [y] ↔ R x y := by
    simp

  theorem infix_append_of_infix {xs ys zs : List α} (h : xs <:+: ys) : xs <:+: zs ++ ys := by
    induction zs with
    | nil => exact h
    | cons z zs IH =>
      apply List.infix_cons
      exact IH

  theorem infix_flatMap_of_mem' {x : α} {xs : List α} (h : x ∈ xs) (f : α → List β) : f x <:+: xs.flatMap f := by
    induction h with
    | head xs =>
      rw [List.flatMap_cons]
      apply List.infix_append' []
    | tail x _ IH =>
      rw [List.flatMap_cons]
      apply infix_append_of_infix IH

  theorem not_mem_singleton {x y : α} : x ∉ [y] ↔ x ≠ y := by
    simp

  theorem concat_flatMap {f : α → List β} {xs : List α} {x : α} : List.flatMap f (List.concat xs x) = List.flatMap f xs ++ f x := by
    simp

  theorem not_mem_append_iff {x : α} {xs ys : List α} : x ∉ xs ++ ys ↔ x ∉ xs ∧ x ∉ ys := by
    simp

  theorem not_mem_cons_iff {x y : α} {xs : List α} : x ∉ y :: xs ↔ x ≠ y ∧ x ∉ xs := by
    simp

  theorem traverse_nil' {α β F} [Applicative F] {f : α → F β} : List.traverse f [] = pure [] :=
    rfl

  theorem traverse_cons' {α β F} [Applicative F] {f : α → F β} {x xs} :
      List.traverse f (x :: xs) = (· :: ·) <$> f x <*> List.traverse f xs :=
    rfl

  def zipper_induction {motive : List α → List α → Sort _} (xs ys : List α)
    (nil : ∀ xs, motive xs []) (cons : ∀ xs y ys, motive (xs ++ [y]) ys → motive xs (y :: ys)) : motive xs ys := match ys with
    | [] => nil _
    | y :: ys => cons _ _ _ (zipper_induction (xs ++ [y]) ys nil cons)

  def not_mem_union_iff [DecidableEq α] {x : α} {l₁ l₂ : List α} : x ∉ l₁ ∪ l₂ ↔ x ∉ l₁ ∧ x ∉ l₂ := by
    rw [List.mem_union_iff, not_or]

  theorem concat_perm_of_perm {x : α} {xs ys : List α} (h : xs ~ ys) : (xs.concat x) ~ (x :: ys) := by
    rwa [← reverse_perm', concat_eq_append, reverse_concat', perm_cons, reverse_perm']

  theorem union_nil [BEq α] [LawfulBEq α] {xs : List α} (h : xs.Nodup) : xs ∪ [] = xs := by
    rw [List.union_def]
    induction h with
    | nil => rfl
    | cons x xs IH =>
      rw [List.foldr_cons, IH, List.insert_of_not_mem]
      rwa [← List.forall_mem_ne]

  theorem union_insert [BEq α] [LawfulBEq α] {xs ys : List α} {x : α} (h : xs.Nodup) : xs ∪ (ys.insert x) = xs.concat x ∪ ys := by
    repeat rw [List.union_def]
    induction h with
    | nil =>
      rw [List.foldr_nil, List.concat_eq_append, List.nil_append, List.foldr_cons, List.foldr_nil]
    | cons x xs IH =>
      rw [List.foldr_cons, List.concat_eq_append, List.cons_append, List.foldr_cons, IH, List.concat_eq_append]

  theorem not_elem_iff [BEq α] [LawfulBEq α] {a : α} {as : List α} : List.elem a as = false ↔ a ∉ as := by
    rw [iff_not_comm, Bool.eq_true_eq_not_eq_false, elem_iff]

  theorem suffix_union [BEq α] [LawfulBEq α] {xs ys : List α} : ys <:+ xs ∪ ys := by
    rw [List.union_def]
    apply List.foldrRecOn
    · apply suffix_refl
    · intros ys' IH x x_in_xs
      rw [List.insert_eq]
      split_ifs
      · assumption
      · rw [suffix_cons_iff]
        right
        assumption

  -- theorem dedup_cons {x : α} {xs : List α} [DecidableEq α] : (x :: xs).dedup = if x ∈ xs then xs.dedup else x :: xs.dedup := by
  --   split_ifs with h
  --   · exact dedup_cons_of_mem h
  --   · exact dedup_cons_of_not_mem h

  theorem union_eq_append [DecidableEq α] {xs ys : List α} : ys ∪ xs = (ys.removeAll xs).dedup ++ xs := by
    rw [union_def]
    induction ys generalizing xs with
    | nil => rw [foldr_nil, nil_removeAll, dedup_nil, List.nil_append]
    | cons y ys IH =>
      rw [foldr_cons, cons_removeAll, IH, List.insert_eq]
      split_ifs with h₁ h₂ h₃
      · have : y ∈ ys.removeAll xs := by simp_all
        rw [dedup_cons_of_mem this]
      · rfl
      · have : y ∉ ys.removeAll xs := by simp_all
        rw [dedup_cons_of_notMem this, cons_append]
      · have : y ∈ xs := by simp_all
        rw [not_mem_append_iff] at h₁
        absurd this
        exact h₁.right

  theorem removeAll_perm_of_perm [DecidableEq α] {xs ys zs : List α} (h : xs ~ ys) : xs.removeAll zs ~ ys.removeAll zs := by
    induction h with
    | nil => rfl
    | cons x _ _ =>
      repeat rw [List.cons_removeAll]
      split_ifs
      · apply Perm.cons
        assumption
      · assumption
    | swap x y l =>
      repeat rw [List.cons_removeAll]
      split_ifs
      · apply Perm.swap
      · rfl
      · rfl
      · rfl
    | trans _ _ _ _ =>
      apply Perm.trans <;> assumption

  @[simp] theorem nil_concat {x : α} : [].concat x = [x] := by rfl

  @[simp] theorem not_contains_iff [BEq α] [LawfulBEq α] {x : α} {xs : List α} : List.contains xs x = false ↔ x ∉ xs := by
    simp

  theorem removeAll_cons_of_mem [BEq α] [LawfulBEq α] {xs ys : List α} {x : α} (h : x ∈ ys) : (x :: xs).removeAll ys = xs.removeAll ys := by
    simpa [cons_removeAll]

  theorem removeAll_cons_of_not_mem [BEq α] [LawfulBEq α] {xs ys : List α} {x : α} (h : x ∉ ys) : (x :: xs).removeAll ys = x :: xs.removeAll ys := by
    simpa [cons_removeAll]

  theorem removeAll_concat_of_not_mem [DecidableEq α] {xs ys : List α} {y : α} (h : y ∉ ys) : (xs.removeAll ys).concat y = (xs.concat y).removeAll ys := by
    induction xs with
    | nil =>
      simp [removeAll, filter_singleton, Bool.cond_eq_if, ite_cond_eq_false _ _ (eq_false h)]
    | cons x xs IH =>
      simp [cons_removeAll, -concat_eq_append]
      split_ifs
      · rw [IH, concat_cons, removeAll_cons_of_mem ‹_›]
      · rw [concat_cons, IH, concat_cons, removeAll_cons_of_not_mem ‹_›]

  theorem filter_ne_of_nodup [DecidableEq α] {xs ys zs : List α} {x : α} (h : xs.Nodup) (h' : xs = ys ++ [x] ++ zs) : List.filter (decide <| · ≠ x) xs = ys ++ zs := by
    induction xs, ys using induction₂' with
    | nil_nil => contradiction
    | nil_cons y ys => contradiction
    | cons_nil x xs =>
      rw [nil_append, singleton_append] at h'
      injections
      subst x xs
      rw [nil_append, filter_cons]
      split_ifs with h''
      · rw [decide_eq_true_eq] at h''
        contradiction
      · rw [List.filter_eq_self]
        intros y y_in
        rw [decide_eq_true_eq]
        have : x ∉ zs := by simp_all
        exact ne_of_mem_of_not_mem y_in this
    | cons_cons x y xs ys IH =>
      simp_rw [List.cons_append] at h' ⊢
      injections
      subst x xs

      have : y ≠ x := by simp_all

      rw [filter_cons, ite_cond_eq_true _ _ (eq_true _)]
      · congr
        apply IH
        · simp_all
        · rw [append_assoc]
      · simp [*]

  theorem dedup_singleton [DecidableEq α] {x : α} : [x].dedup = [x] := rfl

  theorem cons_perm_concat [DecidableEq α] {x : α} {xs : List α} : (x :: xs) ~ (xs ++ [x]) := by
    apply perm_cons_append_cons
    rw [append_nil]

  @[simp] theorem singleton_subset {x : α} {xs : List α} : [x] ⊆ xs ↔ x ∈ xs := by
    simp

  theorem non_empty_induction {motive : (xs : List α) → xs ≠ [] → Prop}
    (singleton : ∀ x, motive [x] (cons_ne_nil _ _))
    (cons : ∀ x xs, (h : xs ≠ []) → motive xs h → motive (x :: xs) (cons_ne_nil _ _)) : ∀ xs, (h : xs ≠ []) → motive xs h
  | [x], _ => singleton x
  | x :: y :: xs, _ => cons x (y :: xs) (cons_ne_nil _ _) (non_empty_induction singleton cons _ _)

  theorem forall₂_singleton_right_iff {R : α → β → Prop} {xs} {y} : List.Forall₂ R xs [y] ↔ ∃ x, R x y ∧ xs = [x] := by
    calc
      List.Forall₂ R xs [y] ↔ ∃ x xs', R x y ∧ List.Forall₂ R xs' [] ∧ xs = x :: xs' := List.forall₂_cons_right_iff
      _ ↔ ∃ x, R x y ∧ List.Forall₂ R [] [] ∧ xs = [x] := by simp
      _ ↔ ∃ x, R x y ∧ xs = [x] := by simp

  theorem forall₂_singleton_left_iff {R : α → β → Prop} {x} {ys} : List.Forall₂ R [x] ys ↔ ∃ y, R x y ∧ ys = [y] := by
    rw [← Forall₂.flip_iff, forall₂_singleton_right_iff]
    rfl

  theorem attach_eq_cons {xs ys} {y : {x : α // x ∈ xs}} (h : xs.attach = y :: ys) :
      ∃ x xs', ∃ (h' : xs = x :: xs'), x = ↑y ∧ ys = xs'.attach.map (λ ⟨y, h⟩ => ⟨y, h' ▸ mem_cons_of_mem x h⟩) := by
    cases xs <;> try contradiction
    rw [attach_cons] at h
    injections
    subst y ys
    refine ⟨_, _, rfl, rfl, rfl⟩

  theorem traverse_map {F : Type _ → Type _} [Applicative F] {f : β → F γ} {g : α → β} {xs} :
      List.traverse f (List.map g xs) = List.traverse (f ∘ g) xs := by
    induction xs with
    | nil => rfl
    | cons x xs IH =>
      rw [List.map_cons, List.traverse_cons', List.traverse_cons', IH]
      rfl

  theorem attach_singleton {x : α} : [x].attach = [⟨x, mem_cons_self⟩] := rfl

  theorem traverse_singleton {α β F} [Applicative F] [LawfulApplicative F] {f : α → F β} {x} : List.traverse f [x] = (· :: []) <$> f x := by
    rw [traverse_cons', traverse_nil', seq_pure, Functor.map_map]

  def sup [SemilatticeSup α] [OrderBot α] (xs : List β) (f : β → α) := List.foldl (· ⊔ f ·) ⊥ xs

  inductive RPerm (R : α → α → Prop) : List α → List α → Prop
    | nil : RPerm R [] []
    | cons (x y : α) {xs ys : List α} : R x y → RPerm R xs ys → RPerm R (x :: xs) (y :: ys)
    | swap (x y : α) {xs : List α} : RPerm R (y :: x :: xs) (x :: y :: xs)
    | trans {xs ys zs : List α} : RPerm R xs ys → RPerm R ys zs → RPerm R xs zs

  theorem rperm_eq_iff_perm {xs ys : List α} : RPerm (· = ·) xs ys ↔ Perm xs ys := by
    iff_intro rperm perm
    · induction rperm with
      | nil => apply Perm.nil
      | cons x _ _ _ IH => subst x; apply Perm.cons; assumption
      | swap x y => apply Perm.swap
      | trans _ _ _ _ => apply Perm.trans <;> assumption
    · induction perm with
      | nil => apply RPerm.nil
      | cons x _ _ => apply RPerm.cons <;> trivial
      | swap x y l => apply RPerm.swap
      | trans _ _ _ _ => apply RPerm.trans <;> assumption

  theorem ne_nil_iff_exists_snoc {xs : List α} : xs ≠ [] ↔ ∃ xs' x, xs = xs' ++ [x] := by
    iff_rintro h ⟨xs', x, rfl⟩
    · rw [← List.dropLast_concat_getLast h]
      refine ⟨_, _, rfl⟩
    · simp

  theorem revInduction {motive : List α → Prop} (xs : List α)
    (nil : motive []) (snoc : ∀ xs x, motive xs → motive (xs ++ [x])) :
      motive xs := by
    by_cases h : xs.isEmpty
    · obtain rfl := List.nil_of_isEmpty h
      exact nil
    · rw [Bool.not_eq_true, List.isEmpty_eq_false_iff, ne_nil_iff_exists_snoc] at h
      obtain ⟨xs, _, rfl⟩ := h
      exact snoc _ _ <| revInduction xs nil snoc
  termination_by xs.length

  theorem map_concat' {f : α → β} {xs : List α} {x : α} : List.map f (xs ++ [x]) = List.map f xs ++ [f x] := by
    simp

  @[simp]
  theorem drop_snoc {i} {xs : List α} {x} (_ : 0 < i) (h' : i - 1 ≤ xs.length) : List.drop (i - 1) (xs ++ [x]) = List.drop (i - 1) xs ++ [x] := by
    apply List.drop_append_of_le_length
    assumption

  private lemma drop_all_but_one_eq {xs : List α} {h : xs.length - 1 < xs.length} (h' : xs ≠ []) : drop (xs.length - 1) xs = [xs[xs.length - 1]] := by
    obtain ⟨xs, x, rfl⟩ := ne_nil_iff_exists_snoc.mp h'
    simp

  private lemma len_ge_two_iff_exists_snoc_snoc {xs : List α} : xs.length ≥ 2 ↔ ∃ xs' x y, xs = xs' ++ [x, y] := by
    iff_rintro h ⟨xs, x, y, rfl⟩
    · exists xs.take (xs.length - 2), xs[xs.length - 2], xs[xs.length - 1]
      convert_to xs = take (xs.length - 2) xs ++ xs.drop (xs.length - 2)
      · congr
        have xs_ne_nil : xs ≠ [] := by grind only [= length_nil]
        have xs_tail_ne_nil : xs.tail ≠ [] := by
          rw [← List.length_pos_iff]
          grind only [= length_tail, cases Or]
        have drop_one_xs_ne_nil : xs.drop 1 ≠ [] := by rwa [List.drop_one]

        rw [ne_nil_iff_exists_snoc] at drop_one_xs_ne_nil
        obtain ⟨xs, x, rfl⟩ := ne_nil_iff_exists_snoc.mp xs_ne_nil
        obtain ⟨xs', y, drop_one_append⟩ := drop_one_xs_ne_nil

        have : xs.length > 0 := by
          grind only [= length_append, → nil_of_isEmpty, = drop_append, = length_nil, = tail_append, = length_cons]
        have h' : xs.length + 1 - 2 = xs.length - 1 := by simp

        simp_rw [length_append, length_singleton, Nat.add_one_sub_one, h']
        trans xs.drop (xs.length - 1) ++ [x]
        · convert_to [(xs ++ [x])[xs.length - 1]] ++ [x] = List.drop _ xs ++ [x]
          · simp
          · congr

            have xs_ne_nil : xs ≠ [] := by grind
            have : xs.length - 1 < xs.length := by grind

            rw [getElem_append_left this, drop_all_but_one_eq xs_ne_nil]
        · apply List.drop_append_of_le_length ?_ |>.symm
          simp
      · simp
    · simp

  theorem evenRevInduction {motive : (xs : List α) → Even xs.length → Prop}
    (nil : motive [] Even.zero)
    (snoc_snoc : ∀ xs x y, (h : Even xs.length) → motive xs h → motive (xs ++ [x, y]) (List.length_append ▸ Even.add h even_two))
    (xs : List α) (h : Even xs.length) :
      motive xs h := by
    if h₁ : xs.length = 0 then
      simp_all
    else if h₂ : xs.length = 1 then
      grind only [= Nat.even_iff]
    else if h₃ : xs.length ≥ 2 then
      rw [len_ge_two_iff_exists_snoc_snoc] at h₃
      obtain ⟨xs, x, y, rfl⟩ := h₃
      fapply snoc_snoc
      · grind only [= length_append, = length_nil, = Nat.even_add, = length_cons, = Nat.even_iff]
      · exact evenRevInduction nil snoc_snoc xs _
    else
      grind only

  private lemma even_len_cons_cons_of_even_len {ys : List α} {y₁ y₂ : α} (even_ys_len : Even ys.length) : Even (y₁ :: y₂ :: ys).length := by
    simp [*]

  def zipperEvenInduction {motive : (xs : List α) → (ys : List α) → Even xs.length → Even ys.length → Prop} (xs ys : List α) (even_xs_len : Even xs.length) (even_ys_len : Even ys.length)
    (nil : ∀ xs even_xs_len, motive xs [] even_xs_len Even.zero)
    (cons_cons : ∀ xs y₁ y₂ ys even_xs_len even_ys_len,
      motive (xs ++ [y₁, y₂]) ys (length_append ▸ Even.add even_xs_len even_two) even_ys_len →
      motive xs (y₁ :: y₂ :: ys) even_xs_len (even_len_cons_cons_of_even_len even_ys_len)) :
      motive xs ys even_xs_len even_ys_len := match ys, even_ys_len with
    | [], _ => nil _ _
    | [_], even_ys_len => by
      grind only [= Nat.even_add, = length_nil, = length_cons, = Nat.even_iff]
    | y₁ :: y₂ :: ys, even_ys_len =>
      have even_ys_len : Even ys.length := by grind only [= Nat.even_add, = length_cons, = Nat.even_iff]
      cons_cons _ _ _ _ even_xs_len even_ys_len
        (zipperEvenInduction (xs ++ [y₁, y₂]) ys (length_append ▸ Even.add even_xs_len even_two) even_ys_len nil cons_cons)

  theorem exists_mem_zip_right_of_mem_left {α β} {xs : List α} {ys : List β} {x} (h : xs.length = ys.length) (h' : x ∈ xs) :
      ∃ y, (x, y) ∈ xs.zip ys := by
    induction xs, ys, h using List.induction₂ with
    | nil_nil =>
      contradiction
    | cons_cons x' xs y' ys len_eq IH =>
      obtain h'|⟨_, h'⟩ := h'
      · exists y'
        simp
      · obtain ⟨y, y_in⟩ := IH h'
        exists y
        simp [y_in]

  theorem rel_of_forall₂_of_mem_zip {α β} {xs : List α} {ys : List β} {R} {x y}
    (mem_zip : (x, y) ∈ xs.zip ys) (rel : Forall₂ R xs ys) :
      R x y := by
    rw [forall₂_iff_zip] at rel
    exact rel.2 mem_zip

  theorem traverse_fmap {α β γ} {F : Type _ → Type _} {xs : List α} [Applicative F] [LawfulApplicative F] {f : β → γ} {g : α → F β} :
      List.traverse (λ x ↦ f <$> g x) xs = List.map f <$> List.traverse g xs := by
    induction xs with
    | nil =>
      rw [traverse_nil', traverse_nil', map_pure, map_nil]
    | cons x xs IH =>
      rw [traverse_cons', IH, traverse_cons', map_seq, Functor.map_map, Applicative.map_seq_map, Functor.map_map]
      rfl

  theorem traverse_ext {F : _ → _} [Applicative F] {xs : List α} {f g : α → F β} (h : ∀ x ∈ xs, f x = g x) :
      List.traverse f xs = List.traverse g xs := by
    induction xs with
    | nil =>
      repeat rw [List.traverse_nil']
    | cons x xs IH =>
      repeat rw [List.traverse_cons']
      rw [h _ List.mem_cons_self, IH]
      · intros x x_in
        apply h _ <| List.mem_cons_of_mem _ x_in
end List
