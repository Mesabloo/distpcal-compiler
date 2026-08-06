module

meta import CustomPrelude
public import Mathlib.Data.Rel
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.OmegaCompletePartialOrder
public import Extra.AesopRuleSets
import Extra.Set
import Mathlib.Data.Nat.Find

public section

theorem todo_rename {α β γ : Type*} (f : SetRel α β) (g : SetRel β γ) (A : Set α) (B : Set β) (C : Set γ)
  (h₁ : B ⊆ f.image A) (h₂ : C ⊆ g.image B) : C ⊆ (f.comp g).image A := by
    calc
      C ⊆ SetRel.image g B := h₂
      _ ⊆ SetRel.image g (SetRel.image f A) := SetRel.image_subset_image h₁
      _ = SetRel.image (SetRel.comp f g) A := SetRel.image_comp _ _ _ |>.symm

-- Exposed: proofs about these relations destructure membership directly with `rintro`, which needs
-- the set-builder body to reduce.
@[expose]
def Relation.lcomp₁ {α β γ : Type _} [Monoid β] (R₁ : Set (α × β × γ)) (W : Set (γ × β)) : Set (α × β) :=
  {(x, c) | ∃ y a b, (x, a, y) ∈ R₁ ∧ (y, b) ∈ W ∧ c = a * b}

@[expose]
def Relation.lcomp₂ {α β γ δ : Type _} [Monoid β] (R₁ : Set (α × β × γ)) (R₂ : Set (γ × β × δ)) : Set (α × β × δ) :=
  {(x, c, z) | ∃ y a b, (x, a, y) ∈ R₁ ∧ (y, b, z) ∈ R₂ ∧ c = a * b}

@[inherit_doc] infixr:140 " ∘ᵣ₁ " => Relation.lcomp₁
@[inherit_doc] infixr:140 " ∘ᵣ₂ " => Relation.lcomp₂

@[mono, gcongr]
theorem Relation.lcomp₁.mono {α β γ : Type _} [Monoid β] {R₁ R₁' : Set (α × β × γ)} {W₂ W₂' : Set (γ × β)} (R₁_sub : R₁ ≤ R₁') (W₂_sub : W₂ ≤ W₂') : R₁ ∘ᵣ₁ W₂ ≤ R₁' ∘ᵣ₁ W₂' := by
  dsimp [Relation.lcomp₁] at *
  rw [Set.setOf_subset_setOf]
  rintro ⟨x, a⟩ ⟨y, b, c, yR₁x, xW₂, a_eq⟩
  dsimp at *
  have xR₁'y : (x, b, y) ∈ R₁' := R₁_sub yR₁x
  have yW₂' : (y, c) ∈ W₂' := W₂_sub xW₂
  exists y, b, c

@[mono, gcongr]
theorem Relation.lcomp₂.mono {α β γ δ : Type _} [Monoid β] {R₁ R₁' : Set (α × β × γ)} {R₂ R₂' : Set (γ × β × δ)} (R₁_sub : R₁ ≤ R₁') (R₂_sub : R₂ ≤ R₂') : R₁ ∘ᵣ₂ R₂ ≤ R₁' ∘ᵣ₂ R₂' := by
  dsimp [Relation.lcomp₂] at *
  rw [Set.setOf_subset_setOf]
  rintro ⟨x, a, z⟩ ⟨y, b, c, zR₁y, yR₂z, a_eq⟩
  dsimp at *
  have zR₁'y : (x, b, y) ∈ R₁' := R₁_sub zR₁y
  have yR₂'z : (y, c, z) ∈ R₂' := R₂_sub yR₂z
  exists y, b, c

theorem Relation.mem_lcomp₂ {α β γ δ : Type _} [Monoid β] {R₁ : Set (α × β × γ)} {R₂ : Set (γ × β × δ)} {a c} {e} :
  (a, e, c) ∈ R₁ ∘ᵣ₂ R₂ ↔ ∃ b e₁ e₂, (a, e₁, b) ∈ R₁ ∧ (b, e₂, c) ∈ R₂ ∧ e = e₁ * e₂ := by rfl

theorem Relation.mem_lcomp₁ {α β γ : Type _} [Monoid β] {R₁ : Set (α × β × γ)} {W : Set (γ × β)} {a} {e} :
  (a, e) ∈ R₁ ∘ᵣ₁ W ↔ ∃ b e₁ e₂, (a, e₁, b) ∈ R₁ ∧ (b, e₂) ∈ W ∧ e = e₁ * e₂ := by rfl

/-- `sem_red`'s composed goals (`sem_step`, later) leave a two-piece existential in this shape —
`.intro` lets `sem_side` close it with one `apply` instead of unfolding `∘ᵣ₂` by hand. -/
@[aesop safe apply (rule_sets := [sem])]
theorem Relation.lcomp₂.intro {α β γ δ : Type _} [Monoid β] {R₁ : Set (α × β × γ)} {R₂ : Set (γ × β × δ)}
    {a b c} {e₁ e₂} (h₁ : (a, e₁, b) ∈ R₁) (h₂ : (b, e₂, c) ∈ R₂) : (a, e₁ * e₂, c) ∈ R₁ ∘ᵣ₂ R₂ :=
  ⟨b, e₁, e₂, h₁, h₂, rfl⟩

@[inherit_doc Relation.lcomp₂.intro, aesop safe apply (rule_sets := [sem])]
theorem Relation.lcomp₁.intro {α β γ : Type _} [Monoid β] {R₁ : Set (α × β × γ)} {W : Set (γ × β)}
    {a b} {e₁ e₂} (h₁ : (a, e₁, b) ∈ R₁) (h₂ : (b, e₂) ∈ W) : (a, e₁ * e₂) ∈ R₁ ∘ᵣ₁ W :=
  ⟨b, e₁, e₂, h₁, h₂, rfl⟩

theorem Relation.lcomp₂.right_union_eq_union {α β γ δ : Type _} [Monoid β] {R : Set (α × β × γ)} {x y : Set (γ × β × δ)} :
    R ∘ᵣ₂ (x ∪ y) = R ∘ᵣ₂ x ∪ R ∘ᵣ₂ y := by
  ext ⟨a, e, b⟩
  iff_rintro ⟨c, e₁, e₂, _, _|_, _, rfl⟩ (⟨c, e₁, e₂, _, _, _, rfl⟩|⟨c, e₁, e₂, _, _, _, rfl⟩)
  · left
    use c, e₁, e₂
  · right
    use c, e₁, e₂
  · use c, e₁, e₂, ?_, ?_
    · assumption
    · left
      assumption
  · use c, e₁, e₂, ?_, ?_
    · assumption
    · right
      assumption

theorem Relation.lcomp₁.right_union_eq_union {α β γ : Type _} [Monoid β] {R : Set (α × β × γ)} {x y : Set (γ × β)} : R ∘ᵣ₁ (x ∪ y) = R ∘ᵣ₁ x ∪ R ∘ᵣ₁ y := by
  unfold Relation.lcomp₁
  ext ⟨b, e⟩
  constructor
  · rintro ⟨a, e₁, e₂, aRb, _|_, rfl⟩ <;> rw [← Set.setOf_or]
    · left
      exists a, e₁, e₂
    · right
      exists a, e₁, e₂
  · rw [← Set.setOf_or]
    rintro (⟨a, e₁, e₂, aRb, _, rfl⟩|⟨a, e₁, e₂, aRb, _, rfl⟩)
    · exists a, e₁, e₂
      (and_intros <;> try left) <;> trivial
    · exists a, e₁, e₂
      (and_intros <;> try right) <;> trivial

-- theorem Relation.lcomp₁.right_inter_is_inter {α β γ : Type _} [Monoid β] {R : Set (α × β × γ)} {x y : Set (γ × β)} : R ∘ᵣ₁ (x ∩ y) = R ∘ᵣ₁ x ∩ R ∘ᵣ₁ y := by
--   ext ⟨b, e⟩
--   constructor
--   · rintro ⟨a, e₁, e₂, aRb, ⟨b_in_x, b_in_y⟩, rfl⟩
--     constructor
--     · exists a, e₁, e₂
--     · exists a, e₁, e₂
--   · rintro ⟨⟨a₁, e₁₁, e₂₁, _, _, _⟩, ⟨a₂, _, e₂₂, _, _, _⟩⟩
--     exists a₁, e₁₁, e₂₁
--     done

theorem Relation.lcomp₁.subset_of_subset_right {α β γ : Type _} [Monoid β] {R : Set (α × β × γ)} {x y : Set (γ × β)} (x_sub_y : x ⊆ y) : R ∘ᵣ₁ x ⊆ R ∘ᵣ₁ y :=
  Relation.lcomp₁.mono le_rfl x_sub_y

theorem Relation.lcomp₁.subset_of_subset_left {α β γ : Type _} [Monoid β] {R₁ R₂ : Set (α × β × γ)} {x : Set (γ × β)} (R₁_sub_R₂ : R₁ ⊆ R₂) : R₁ ∘ᵣ₁ x ⊆ R₂ ∘ᵣ₁ x :=
  Relation.lcomp₁.mono R₁_sub_R₂ le_rfl

theorem Relation.lcomp₁.right_empty_eq_empty {α β γ : Type _} [Monoid β] {R : Set (α × β × γ)} : R ∘ᵣ₁ ∅ = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro ⟨a, e⟩ ⟨b, e₁, e₂, b_in_r, _|_, _⟩

theorem Relation.lcomp₂.left_id_eq {α β γ : Type _} [Monoid β] {R : Set (α × β × γ)} : {⟨x, e, y⟩ | x = y ∧ e = 1} ∘ᵣ₂ R = R := by
  ext ⟨a, e, c⟩
  constructor
  · rintro ⟨b, e₁, e₂, ⟨rfl, rfl⟩, _, rfl⟩
    rwa [Monoid.one_mul]
  · intro
    exists a, 1, e
    and_intros
    · rfl
    · rfl
    · assumption
    · rw [Monoid.one_mul]

theorem Relation.lcomp₁.left_id_eq {α β : Type _} [Monoid β] {R : Set (α × β)} : {⟨x, e, y⟩ | x = y ∧ e = 1} ∘ᵣ₁ R = R := by
  ext ⟨a, e⟩
  constructor
  · rintro ⟨b, e₁, e₂, ⟨rfl, rfl⟩, _, rfl⟩
    rwa [Monoid.one_mul]
  · intro
    exists a, 1, e
    and_intros <;> try trivial
    rw [Monoid.one_mul]

theorem Relation.lcomp₂.right_id_eq {α β γ : Type _} [Monoid β] {R : Set (α × β × γ)} : R ∘ᵣ₂ {⟨x, e, y⟩ | x = y ∧ e = 1} = R := by
  ext ⟨a, e, c⟩
  constructor
  · rintro ⟨b, e₁, e₂, _, ⟨rfl, rfl⟩, rfl⟩
    rwa [Monoid.mul_one]
  · intro
    exists c, e, 1
    and_intros
    · assumption
    · rfl
    · rfl
    · rw [Monoid.mul_one]

theorem Relation.lcomp₂.assoc {α β γ δ ε : Type _} [Monoid β] {R₁ : Set (α × β × γ)} {R₂ : Set (γ × β × δ)} {R₃ : Set (δ × β × ε)} :
  R₁ ∘ᵣ₂ (R₂ ∘ᵣ₂ R₃) = (R₁ ∘ᵣ₂ R₂) ∘ᵣ₂ R₃ := by
    ext ⟨a, e, d⟩
    constructor
    · rintro ⟨b, e₁, e₂, aR₁b, ⟨c, e₃, e₄, bR₂c, cR₃d, rfl⟩, rfl⟩
      rw [← mul_assoc]
      exists c, e₁ * e₃, e₄
      and_intros
      · exists b, e₁, e₃
      · assumption
      · rfl
    · rintro ⟨c, e₁, e₂, ⟨b, e₃, e₄, aR₁b, bR₂c, rfl⟩, cR₃d, rfl⟩
      rw [mul_assoc]
      exists b, e₃, e₄ * e₂
      and_intros
      · assumption
      · exists c, e₄, e₂
      · rfl

theorem Relation.lcomp₁.left_lcomp₂_eq {α β γ δ : Type _} [Monoid β] {R₁ : Set (α × β × γ)} {R₂ : Set (γ × β × δ)} {R₃ : Set (δ × β)} : (R₁ ∘ᵣ₂ R₂) ∘ᵣ₁ R₃ = R₁ ∘ᵣ₁ (R₂ ∘ᵣ₁ R₃) := by
  ext ⟨a, e⟩
  constructor
  · rintro ⟨c, _, e₃, ⟨b, e₁, e₂, _, _, rfl⟩, _, rfl⟩
    rw [mul_assoc]
    exists b, e₁, e₂ * e₃
    and_intros <;> try trivial
    exists c, e₂, e₃
  · rintro ⟨b, e₁, e₂, _, ⟨c, e₂, e₃, _, _, rfl⟩, rfl⟩
    rw [← mul_assoc]
    exists c, e₁ * e₂, e₃
    and_intros <;> try trivial
    exists b, e₁, e₂





-----------------

theorem Set.ωSup_is_iUnion {α : Type _} {chain : OmegaCompletePartialOrder.Chain (Set α)} : OmegaCompletePartialOrder.ωSup chain = ⋃ i, chain i := rfl

theorem Set.ωSup_is_iInter {α : Type _} {chain : OmegaCompletePartialOrder.Chain (Set α)ᵒᵈ} : OmegaCompletePartialOrder.ωSup chain = ⋂ i, chain i := rfl

theorem Relation.lcomp₁.ωcontinuous {α β γ : Type _} [Monoid β] (R : Set (α × β × γ)) :
    OmegaCompletePartialOrder.ωScottContinuous (R ∘ᵣ₁ ·) := by
  apply OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup

  have : Monotone (R ∘ᵣ₁ ·) := by intros _ _ _; mono
  exists this
  intro chain

  ext ⟨a, e⟩
  iff_rintro ⟨b, e₁, e₂, bRa, a_in_ωsup, rfl⟩ ⟨B, B_in, a_in_comp⟩
  · rw [Set.ωSup_is_iUnion, Set.mem_iUnion] at a_in_ωsup ⊢
    obtain ⟨i, a_in⟩ := a_in_ωsup
    exists i
    rw [OmegaCompletePartialOrder.Chain.coe_map, OrderHom.coe_mk, Function.comp_def]
    exists b, e₁, e₂
  · change ∃ i, R ∘ᵣ₁ chain i = B at B_in
    obtain ⟨i, rfl⟩ := B_in
    obtain ⟨b, e₁, e₂, bRa, _, rfl⟩ := a_in_comp
    exists b, e₁, e₂
    and_intros
    · assumption
    · rw [Set.ωSup_is_iUnion, Set.mem_iUnion]
      exists i
    · rfl

theorem Relation.lcomp₁.ωcontinuous_of_union {α β γ : Type _} [Monoid β] (R₁ : Set (α × β)) (R₂ : Set (α × β × γ)) :
    OmegaCompletePartialOrder.ωScottContinuous (R₁ ∪ R₂ ∘ᵣ₁ ·) := by
  apply OmegaCompletePartialOrder.ωScottContinuous.comp
  · apply CompleteLattice.ωScottContinuous.sup
    · apply OmegaCompletePartialOrder.ωScottContinuous.const
    · apply OmegaCompletePartialOrder.ωScottContinuous.id
  · apply Relation.lcomp₁.ωcontinuous

theorem Relation.lcomp₂.ωcontinuous {α β γ δ : Type _} [Monoid β] (R : Set (α × β × γ)) :
    OmegaCompletePartialOrder.ωScottContinuous (R ∘ᵣ₂ · : Set (γ × β × δ) → Set (α × β × δ)) := by
  apply OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup

  have : Monotone (R ∘ᵣ₂ · : Set (γ × β × δ) → Set (α × β × δ)) := by intros _ _ _; mono
  exists this
  intro chain

  ext ⟨a, e, c⟩
  iff_rintro ⟨b, e₁, e₂, aRb, b_in_ωsup, rfl⟩ ⟨B, B_in, a_in_comp⟩
  · rw [Set.ωSup_is_iUnion, Set.mem_iUnion] at b_in_ωsup ⊢
    obtain ⟨i, b_in⟩ := b_in_ωsup
    exists i
    rw [OmegaCompletePartialOrder.Chain.coe_map, OrderHom.coe_mk, Function.comp_def]
    exists b, e₁, e₂
  · change ∃ i, R ∘ᵣ₂ chain i = B at B_in
    obtain ⟨i, rfl⟩ := B_in
    obtain ⟨b, e₁, e₂, bRa, _, rfl⟩ := a_in_comp
    exists b, e₁, e₂
    and_intros
    · assumption
    · rw [Set.ωSup_is_iUnion, Set.mem_iUnion]
      exists i
    · rfl

/- theorem Relation.lcomp₁.ωcocontinuous {α β γ : Type _} [Monoid β] (R₁ : Set (α × β × γ)) :
 -     OmegaCompletePartialOrder.ωScottContinuous (OrderHom.dual { toFun := λ X ↦ R₁ ∘ᵣ₁ X,
 -                                                                 monotone' := by intro X Y X_sub; exact Relation.lcomp₁.subset_of_subset_right X_sub
 -                                                               }) := by
 -   apply OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
 -
 -   have : Monotone (α := (Set (γ × β))ᵒᵈ) (β := (Set (α × β))ᵒᵈ) (R₁ ∘ᵣ₁ ·) := by
 -     intros _ _ _
 -     apply Relation.lcomp₁.subset_of_subset_right
 -     assumption
 -   exists this
 -   intro chain
 -
 -   ext ⟨a, e⟩
 -   iff_rintro ⟨b, e₁, e₂, aRb, b_in_ωsup, rfl⟩ h
 -   · erw [Set.ωSup_is_iInter, Set.mem_iInter] at b_in_ωsup ⊢
 -     intro i
 -     specialize b_in_ωsup i
 -     rw [OmegaCompletePartialOrder.Chain.coe_map, OrderHom.coe_mk, Function.comp_def]
 -     exists b, e₁, e₂
 -   · erw [Set.ωSup_is_iInter] at h ⊢
 -     rw [OrderHom.dual_apply_coe, Function.comp_def, Function.comp_def, OrderDual.ofDual_toDual, OrderHom.coe_mk]
 -     erw [OmegaCompletePartialOrder.Chain.coe_map, OrderHom.coe_mk (f := ⇑(OrderHom.dual _)), Function.comp_def, Set.mem_iInter] at h
 -     conv at h =>
 -       enter [i, 1]; erw [OrderHom.dual_apply_coe, Function.comp_def, Function.comp_def, OrderHom.coe_mk (f := λ X ↦ R₁ ∘ᵣ₁ X)]
 -     beta_reduce at h ⊢
 -     admit -/

theorem OrderHom.lfp_induction₂ {α β : Type _} [CompleteLattice α] [CompleteLattice β] (f : α →o α) (g : β →o β) {p : α → β → Prop}
  (step : ∀ (a : α) (b : β), p a b → a ≤ OrderHom.lfp f → b ≤ OrderHom.lfp g → p (f a) (g b))
  (hSup : ∀ (A : Set α) (B : Set β),
    (∀ x ∈ A, ∃ y ∈ B, p x y) →
    (∀ y ∈ B, ∃ x ∈ A, p x y) →
    p (sSup A) (sSup B)) :
    p (OrderHom.lfp f) (OrderHom.lfp g) := by
  let s := { ⟨x, y⟩ : α × β | x ≤ lfp f ∧ y ≤ lfp g ∧ p x y}

  have key := hSup ((·.1) '' s) ((·.2) '' s)
    (by rintro x ⟨t, ht, rfl⟩; exact ⟨_, ⟨t, ht, rfl⟩, ht.2.2⟩)
    (by rintro y ⟨t, ht, rfl⟩; exact ⟨_, ⟨t, ht, rfl⟩, ht.2.2⟩)

  have h₁ : sSup ((·.1) '' s) ≤ lfp f := sSup_le (by rintro x ⟨t, ht, rfl⟩; exact ht.1)
  have h₂ : sSup ((·.2) '' s) ≤ lfp g := sSup_le (by rintro y ⟨t, ht, rfl⟩; exact ht.2.1)

  have mem : (f (sSup ((·.1) '' s)), g (sSup ((·.2) '' s))) ∈ s :=
    ⟨f.map_le_lfp h₁, g.map_le_lfp h₂, step _ _ key h₁ h₂⟩

  have e₁ : sSup ((·.1) '' s) = lfp f := h₁.antisymm <| lfp_le _ <| le_sSup ⟨_, mem, rfl⟩
  have e₂ : sSup ((·.2) '' s) = lfp g := h₂.antisymm <| lfp_le _ <| le_sSup ⟨_, mem, rfl⟩

  rwa [e₁, e₂] at key

theorem OrderHom.lfp_induction₃ {α β γ : Type _} [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] (f : α →o α) (g : β →o β) (h : γ →o γ) {p : α → β → γ → Prop}
  (step : ∀ (a : α) (b : β) (c : γ), p a b c → a ≤ OrderHom.lfp f → b ≤ OrderHom.lfp g → c ≤ OrderHom.lfp h → p (f a) (g b) (h c))
  (hSup : ∀ (A : Set α) (B : Set β) (C : Set γ),
    (∀ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, p x y z) →
    (∀ y ∈ B, ∃ x ∈ A, ∃ z ∈ C, p x y z) →
    (∀ z ∈ C, ∃ x ∈ A, ∃ y ∈ B, p x y z) →
    p (sSup A) (sSup B) (sSup C)) :
    p (OrderHom.lfp f) (OrderHom.lfp g) (OrderHom.lfp h) := by
  let s := { ⟨x, y, z⟩ : α × β × γ | x ≤ lfp f ∧ y ≤ lfp g ∧ z ≤ lfp h ∧ p x y z}

  have key := hSup ((·.1) '' s) ((·.2.1) '' s) ((·.2.2) '' s)
    (by rintro x ⟨t, ht, rfl⟩; exact ⟨_, ⟨t, ht, rfl⟩, _, ⟨t, ht, rfl⟩, ht.2.2.2⟩)
    (by rintro y ⟨t, ht, rfl⟩; exact ⟨_, ⟨t, ht, rfl⟩, _, ⟨t, ht, rfl⟩, ht.2.2.2⟩)
    (by rintro z ⟨t, ht, rfl⟩; exact ⟨_, ⟨t, ht, rfl⟩, _, ⟨t, ht, rfl⟩, ht.2.2.2⟩)

  have h₁ : sSup ((·.1) '' s) ≤ lfp f := sSup_le (by rintro x ⟨t, ht, rfl⟩; exact ht.1)
  have h₂ : sSup ((·.2.1) '' s) ≤ lfp g := sSup_le (by rintro y ⟨t, ht, rfl⟩; exact ht.2.1)
  have h₃ : sSup ((·.2.2) '' s) ≤ lfp h := sSup_le (by rintro z ⟨t, ht, rfl⟩; exact ht.2.2.1)

  have mem : (f (sSup ((·.1) '' s)), g (sSup ((·.2.1) '' s)), h (sSup ((·.2.2) '' s))) ∈ s :=
    ⟨f.map_le_lfp h₁, g.map_le_lfp h₂, h.map_le_lfp h₃, step _ _ _ key h₁ h₂ h₃⟩

  have e₁ : sSup ((·.1) '' s) = lfp f := h₁.antisymm <| lfp_le _ <| le_sSup ⟨_, mem, rfl⟩
  have e₂ : sSup ((·.2.1) '' s) = lfp g := h₂.antisymm <| lfp_le _ <| le_sSup ⟨_, mem, rfl⟩
  have e₃ : sSup ((·.2.2) '' s) = lfp h := h₃.antisymm <| lfp_le _ <| le_sSup ⟨_, mem, rfl⟩

  rwa [e₁, e₂, e₃] at key

/-!
## Composing relations

Two ways of combining relations, both used to say how a refinement's trace relation is built from
its factors' (`VerifiedCompiler/Trace.lean`). They are different monoid structures on relations and
should not be confused: `∘ᵣ`'s unit is the diagonal, `⊗ᵣ`'s is the relation holding only of the two
units.

Relations are heterogeneous throughout — a source and a target need not draw their traces from the
same type.
-/

/-- Relational composition is mathlib's `Relation.Comp`; only the notation is ours, since mathlib
declares its `∘r` `local`. Named to match this file's `∘ᵣ₁`/`∘ᵣ₂`. -/
@[inherit_doc Relation.Comp] infixr:140 " ∘ᵣ " => Relation.Comp

/-- Pointwise product through the two monoids: the left-hand sides multiply and so do the
right-hand sides, each factor related by its own relation. Composing two refinements in sequence
combines their trace relations this way, since the traces concatenate. -/
@[expose]
def Relation.rmul {α β : Type _} [Monoid α] [Monoid β] (P Q : Rel α β) : Rel α β :=
  λ a b ↦ ∃ a₁ a₂ b₁ b₂, a = a₁ * a₂ ∧ b = b₁ * b₂ ∧ P a₁ b₁ ∧ Q a₂ b₂

@[inherit_doc] infixl:70 " ⊗ᵣ " => Relation.rmul

/-- Every right-hand element is related to by some left-hand one. For a trace relation this says
the target can emit nothing the source could not have emitted. -/
@[expose]
def Relation.LeftTotal {α β : Type _} (R : Rel α β) : Prop := ∀ b, ∃ a, R a b

/-- Closed under multiplication: as a subset of `α × β`, a submonoid. For a trace relation this is
the statement that the relation is preserved by concatenation, which is what a fixed-point
refinement needs of it. -/
@[expose]
def Relation.MulClosed {α β : Type _} [Monoid α] [Monoid β] (R : Rel α β) : Prop :=
  ∀ a b c d, R a b → R c d → R (a * c) (b * d)

/-- Any extension of the right-hand side can be matched by some extension of the left. Not an extra
assumption: it is what `LeftTotal` and `MulClosed` give together, and it is the form horizontal
composition actually consumes. -/
theorem Relation.right_extend {α β : Type _} [Monoid α] [Monoid β] {R : Rel α β}
    (tot : Relation.LeftTotal R) (cl : Relation.MulClosed R) {a : α} {b : β} (h : R a b) (z : β) :
    ∃ z', R (a * z') (b * z) := by
  obtain ⟨z', hz'⟩ := tot z
  exact ⟨z', cl _ _ _ _ h hz'⟩

/-! # Infinite iteration

  `R^∞`: the executions that take infinitely many `R`-steps. Defined **directly**, from a sequence
  of states and a sequence of emitted traces, rather than as the greatest fixed point of
  `X ↦ R ∘ᵣ₁ X`.

  The gfp is the wrong denotation, in a way that has nothing to do with how hard it is to reason
  about. A step emitting the empty trace makes that functional non-contractive — `R ∘ᵣ₁ x ⊇ x` — so
  at `R = {(σ, 1, σ)}` it is the identity, whose greatest fixed point is `⊤`: every trace
  whatsoever, paired with a state that merely diverges silently. `R^∞` gives that execution the
  trace `1`, which is what it actually emits. The two agree only when `R` has no infinite chain of
  empty-trace steps, which `Algebra.step` certainly does (`while TRUE { x := x + 1 }`).
-/

/-- `e 0 * ⋯ * e (n-1)`, and `1` when `n = 0`. -/
@[expose] def Monoid.partialProd {ε : Type _} [Monoid ε] (e : ℕ → ε) : ℕ → ε
  | 0 => 1
  | n + 1 => Monoid.partialProd e n * e n

@[simp] theorem Monoid.partialProd_zero {ε : Type _} [Monoid ε] {e : ℕ → ε} :
    Monoid.partialProd e 0 = 1 := rfl

@[simp] theorem Monoid.partialProd_succ {ε : Type _} [Monoid ε] {e : ℕ → ε} {n : ℕ} :
    Monoid.partialProd e (n + 1) = Monoid.partialProd e n * e n := rfl

/-- The same product peeled from the left instead of the right. `partialProd` folds right-to-left,
but a run built forwards from a starting state produces its factors left-to-right, so relating the
two is what lets a prefix of a run be recognised as a `partialProd`. -/
theorem Monoid.partialProd_succ' {ε : Type _} [Monoid ε] (e : ℕ → ε) (n : ℕ) :
    Monoid.partialProd e (n + 1) = e 0 * Monoid.partialProd (λ i ↦ e (i + 1)) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Monoid.partialProd_succ, ih, Monoid.partialProd_succ, mul_assoc]

/-- A monoid in which an infinite sequence of factors has a product.

A mixin over `Monoid` rather than an extension of it, so that the existing `[Monoid ε]` binders
throughout the refinement framework are untouched and no instance diamond arises.

Deliberately carries no laws yet. The one law the refinement proofs turn out to need —
`partialProd_dvd`, that every finite prefix of the product divides it — is passed explicitly to the
lemmas that consume it, until it is clear that every intended instance satisfies it. -/
class OmegaProd (ε : Type _) [Monoid ε] where
  /-- The product of infinitely many factors. -/
  ωProd : (ℕ → ε) → ε

/-- Every finite prefix of an infinite product divides it. Stated as a predicate rather than an
`OmegaProd` field: it is what the aborting branch of a divergence refinement consumes, and stating
it separately keeps instances cheap to register. -/
@[expose]
def OmegaProd.HasPartialProdDvd (ε : Type _) [Monoid ε] [OmegaProd ε] : Prop :=
  ∀ (e : ℕ → ε) (n : ℕ), ∃ r, OmegaProd.ωProd e = Monoid.partialProd e n * r

/-- `R^∞` — the states from which `R` can step forever, paired with the trace the whole infinite
run emits. -/
@[expose]
def Relation.omega {α ε : Type _} [Monoid ε] [OmegaProd ε] (R : Set (α × ε × α)) : Set (α × ε) :=
  {x | ∃ (σs : ℕ → α) (es : ℕ → ε),
    σs 0 = x.1 ∧ (∀ i, (σs i, es i, σs (i + 1)) ∈ R) ∧ x.2 = OmegaProd.ωProd es}

theorem Relation.omega.mono {α ε : Type _} [Monoid ε] [OmegaProd ε] {R S : Set (α × ε × α)}
    (h : R ≤ S) : Relation.omega R ≤ Relation.omega S := by
  rintro ⟨σ, ε⟩ ⟨σs, es, h₀, hstep, hε⟩
  exact ⟨σs, es, h₀, λ i ↦ h (hstep i), hε⟩

/-! # Finite iteration

  `R*`. Stated in the same ℕ-indexed shape as `Relation.omega` rather than reusing
  `Relation.TraceReflTransGen` (`VerifiedCompiler/Relation.lean`), which is `Prop`-valued and
  defined downstream of this file. Sharing the shape is what lets the two refinement lemmas —
  one for `R*`, one for `R^∞` — be proved by the same kind of induction over the index.
-/

/-- `R*` — finitely many `R`-steps, with the concatenated trace. -/
@[expose]
def Relation.star {α ε : Type _} [Monoid ε] (R : Set (α × ε × α)) : Set (α × ε × α) :=
  {x | ∃ (n : ℕ) (σs : ℕ → α) (es : ℕ → ε),
    σs 0 = x.1 ∧ σs n = x.2.2 ∧ (∀ i, i < n → (σs i, es i, σs (i + 1)) ∈ R) ∧
      x.2.1 = Monoid.partialProd es n}

/-- Zero steps. -/
theorem Relation.star.refl {α ε : Type _} [Monoid ε] {R : Set (α × ε × α)} (a : α) :
    (a, (1 : ε), a) ∈ Relation.star R :=
  ⟨0, λ _ ↦ a, λ _ ↦ 1, rfl, rfl, by omega, rfl⟩

/-- One step in front of a run. -/
theorem Relation.star.head {α ε : Type _} [Monoid ε] {R : Set (α × ε × α)} {a b c : α} {e e' : ε}
    (h : (a, e, b) ∈ R) (h' : (b, e', c) ∈ Relation.star R) :
    (a, e * e', c) ∈ Relation.star R := by
  obtain ⟨n, σs, es, h₀, hn, hsteps, he⟩ := h'
  dsimp only at h₀ hn he
  refine ⟨n + 1, λ i ↦ Nat.rec a (λ j _ ↦ σs j) i, λ i ↦ Nat.rec e (λ j _ ↦ es j) i, rfl, hn, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero =>
      show (a, e, σs 0) ∈ R
      rw [h₀]
      exact h
    | succ i => exact hsteps i (by omega)
  · show e * e' = _
    rw [Monoid.partialProd_succ' _ n, he]
    rfl

theorem Relation.star.mono {α ε : Type _} [Monoid ε] {R S : Set (α × ε × α)}
    (h : R ≤ S) : Relation.star R ≤ Relation.star S := by
  rintro ⟨a, e, b⟩ ⟨n, σs, es, h₀, hn, hsteps, he⟩
  exact ⟨n, σs, es, h₀, hn, λ i hi ↦ h (hsteps i hi), he⟩

/-- A run is either empty or a step followed by a run. The eliminator the closed form below needs,
since `Relation.star` is indexed by a length rather than defined inductively. -/
theorem Relation.star.dest {α ε : Type _} [Monoid ε] {R : Set (α × ε × α)} {a c : α} {e : ε}
    (h : (a, e, c) ∈ Relation.star R) :
    (a = c ∧ e = 1) ∨
      ∃ b e₁ e₂, (a, e₁, b) ∈ R ∧ (b, e₂, c) ∈ Relation.star R ∧ e = e₁ * e₂ := by
  obtain ⟨n, σs, es, h₀, hn, hsteps, he⟩ := h
  dsimp only at h₀ hn he
  cases n with
  | zero => exact Or.inl ⟨h₀.symm.trans hn, he⟩
  | succ n =>
    refine Or.inr ⟨σs 1, es 0, Monoid.partialProd (λ i ↦ es (i + 1)) n, ?_, ?_, ?_⟩
    · rw [← h₀]
      exact hsteps 0 (by omega)
    · exact ⟨n, λ i ↦ σs (i + 1), λ i ↦ es (i + 1), rfl, hn, λ i hi ↦ hsteps (i + 1) (by omega), rfl⟩
    · rw [he, Monoid.partialProd_succ']

/-! # The closed form of a diverging fixed point

The paper (arXiv 2404.17297, 5:36) states

```
gfp (λ x, Y ∪ X ∘ᵣ₁ x)  =  (X* ∘ᵣ₁ Y) ∪ X^∞
```

and computes with the right-hand side. Only one inclusion is unconditional. The functional is not
contractive when `X` can step emitting nothing, so its greatest fixed point overshoots: at
`X = {(σ, 1, σ)}` and `Y = ∅` the functional is the identity and its greatest fixed point is `⊤`,
pairing `σ` with every trace whatsoever, while the right-hand side gives `{(σ, 1)}` — the trace that
execution actually emits. The leak is entirely on the gfp side, which is why this development takes
the closed form as the *definition* of divergence (`Relation.omega`) and keeps the identity below as
a characterization of when the two agree.

`Relation.Productive` is the exact boundary, not merely a convenient sufficient condition: it is
what fails in the counterexample. It is deliberately *not* satisfied by the semantics this
development compiles — `while TRUE { x := x + 1 }` diverges silently — so nothing in the refinement
framework may depend on these three theorems.
-/

/-- No infinite run of `R` emits nothing forever.

Stated as a negated existential rather than as "infinitely many steps emit something", because the
run whose productivity is at stake is produced by dependent choice: its states are not known in
advance, so there is nothing to quantify over positively. -/
@[expose]
def Relation.Productive {α ε : Type _} [Monoid ε] (R : Set (α × ε × α)) : Prop :=
  ¬∃ σ : ℕ → α, ∀ i, (σ i, (1 : ε), σ (i + 1)) ∈ R

/-- The first factor of an infinite product comes out in front.

A law of `OmegaProd`, stated as a predicate for the same reason as
`OmegaProd.HasPartialProdDvd`: instances stay cheap to register, and the lemmas that consume it say
so in their signatures. -/
@[expose]
def OmegaProd.HasUnfold (ε : Type _) [Monoid ε] [OmegaProd ε] : Prop :=
  ∀ e : ℕ → ε, OmegaProd.ωProd e = e 0 * OmegaProd.ωProd (λ i ↦ e (i + 1))

/-- An element having every partial product of a sequence as a left factor *is* that sequence's
infinite product, provided the sequence keeps contributing.

The proviso is essential and is where productivity enters: without it the partial products stabilize
at some finite `p`, every element of the form `p * r` has them all as left factors, and the infinite
product is not pinned down. -/
@[expose]
def OmegaProd.HasProductLimit (ε : Type _) [Monoid ε] [OmegaProd ε] : Prop :=
  ∀ (e r : ℕ → ε) (x : ε), (∀ n, x = Monoid.partialProd e n * r n) →
    (∀ n, ∃ m, n ≤ m ∧ e m ≠ 1) → x = OmegaProd.ωProd e

/-- The functional whose greatest fixed point the paper takes as the denotation of divergence: one
`X`-step in front of the rest, or stop in `Y`. -/
@[expose]
def Relation.divFun {α ε : Type _} [Monoid ε] (X : Set (α × ε × α)) (Y : Set (α × ε)) :
    Set (α × ε) →o Set (α × ε) where
  toFun x := Y ∪ X ∘ᵣ₁ x
  monotone' _ _ h := Set.union_subset_union le_rfl (Relation.lcomp₁.mono le_rfl h)

@[simp] theorem Relation.divFun_apply {α ε : Type _} [Monoid ε] {X : Set (α × ε × α)}
    {Y x : Set (α × ε)} : Relation.divFun X Y x = Y ∪ X ∘ᵣ₁ x := rfl

/-- The closed form is below the greatest fixed point, unconditionally: it is a post-fixed point.
This is the half of the paper's identity that always holds. -/
theorem Relation.closedForm_le_gfp {α ε : Type _} [Monoid ε] [OmegaProd ε]
    (hunfold : OmegaProd.HasUnfold ε) {X : Set (α × ε × α)} {Y : Set (α × ε)} :
    (Relation.star X ∘ᵣ₁ Y) ∪ Relation.omega X ≤ OrderHom.gfp (Relation.divFun X Y) := by
  apply OrderHom.le_gfp
  rintro ⟨σ, e⟩ (⟨σ', e₁, e₂, hstar, hY, rfl⟩ | ⟨σs, es, h₀, hstep, rfl⟩)
  · rcases Relation.star.dest hstar with ⟨rfl, rfl⟩ | ⟨b, f₁, f₂, hR, hstar', rfl⟩
    · apply Or.inl
      rwa [one_mul]
    · refine Or.inr ⟨b, f₁, f₂ * e₂, hR, Or.inl ⟨σ', f₂, e₂, hstar', hY, rfl⟩, ?_⟩
      rw [mul_assoc]
  · dsimp only at h₀ ⊢
    subst h₀
    refine Or.inr ⟨σs 1, es 0, OmegaProd.ωProd (λ i ↦ es (i + 1)), hstep 0, Or.inr ?_, hunfold es⟩
    exact ⟨λ i ↦ σs (i + 1), λ i ↦ es (i + 1), rfl, λ i ↦ hstep (i + 1), rfl⟩

/-- The converse inclusion, under productivity. Unfolding the fixed point greedily either reaches
`Y` — a finite run, hence `X* ∘ᵣ₁ Y` — or never does, and dependent choice then produces an infinite
run whose partial products are all left factors of the trace. Productivity turns that into an
equality with the infinite product; without it the trace is never pinned down, which is exactly the
counterexample. -/
theorem Relation.gfp_le_closedForm {α ε : Type _} [Monoid ε] [OmegaProd ε]
    (lim : OmegaProd.HasProductLimit ε) {X : Set (α × ε × α)} {Y : Set (α × ε)}
    (prod : Relation.Productive X) :
    OrderHom.gfp (Relation.divFun X Y) ≤ (Relation.star X ∘ᵣ₁ Y) ∪ Relation.omega X := by classical
  rintro ⟨σ, e⟩ hmem
  haveI : Nonempty α := ⟨σ⟩
  have unf : ∀ p : α × ε, p ∈ OrderHom.gfp (Relation.divFun X Y) → p ∉ Y →
      ∃ q : ε × α × ε, (p.1, q.1, q.2.1) ∈ X ∧
        q.2 ∈ OrderHom.gfp (Relation.divFun X Y) ∧ p.2 = q.1 * q.2.2 := by
    rintro ⟨a, x⟩ hp hpY
    rw [← OrderHom.map_gfp] at hp
    rcases hp with h | ⟨b, e₁, e₂, hX, hb, he⟩
    · absurd h
      exact hpY
    · exact ⟨(e₁, b, e₂), hX, hb, he⟩
  choose! g hgX hgmem hgtrace using unf
  set P : ℕ → α × ε := λ n ↦ Nat.rec (σ, e) (λ _ p ↦ (g p).2) n
  set es : ℕ → ε := λ n ↦ (g (P n)).1
  have inv : ∀ n, (∀ i, i < n → P i ∉ Y) →
      P n ∈ OrderHom.gfp (Relation.divFun X Y) ∧ e = Monoid.partialProd es n * (P n).2 ∧
        ∀ i, i < n → ((P i).1, es i, (P (i + 1)).1) ∈ X := by
    intro n
    induction n with
    | zero => exact λ _ ↦ ⟨hmem, (one_mul e).symm, by omega⟩
    | succ n ih =>
      intro hY
      obtain ⟨hg, htr, hst⟩ := ih (λ i hi ↦ hY i (by omega))
      have hnY : P n ∉ Y := hY n (by omega)
      refine ⟨hgmem _ hg hnY, ?_, ?_⟩
      · rw [Monoid.partialProd_succ, mul_assoc, ← hgtrace _ hg hnY]
        exact htr
      · intro i hi
        rcases Nat.lt_or_ge i n with h | h
        · exact hst i h
        · rw [show i = n by omega]
          exact hgX _ hg hnY
  by_cases hstop : ∃ n, P n ∈ Y
  · obtain ⟨-, htr, hst⟩ := inv (Nat.find hstop) (λ j hj ↦ Nat.find_min hstop hj)
    exact Or.inl ⟨(P (Nat.find hstop)).1, Monoid.partialProd es (Nat.find hstop),
      (P (Nat.find hstop)).2, ⟨Nat.find hstop, λ i ↦ (P i).1, es, rfl, rfl, hst, rfl⟩,
      Nat.find_spec hstop, htr⟩
  · have hall : ∀ n, P n ∈ OrderHom.gfp (Relation.divFun X Y) ∧
        e = Monoid.partialProd es n * (P n).2 ∧
        ∀ i, i < n → ((P i).1, es i, (P (i + 1)).1) ∈ X :=
      λ n ↦ inv n (λ i _ h ↦ hstop ⟨i, h⟩)
    have hne : ∀ n, ∃ m, n ≤ m ∧ es m ≠ 1 := by
      intro n
      by_contra! hc
      apply prod
      refine ⟨λ i ↦ (P (n + i)).1, λ i ↦ ?_⟩
      have hs := (hall (n + i + 1)).2.2 (n + i) (by omega)
      rwa [hc (n + i) (by omega)] at hs
    refine Or.inr ⟨λ i ↦ (P i).1, es, rfl, λ i ↦ (hall (i + 1)).2.2 i (by omega), ?_⟩
    exact lim es (λ n ↦ (P n).2) e (λ n ↦ (hall n).2.1) hne

/-- The paper's identity, with the hypothesis it needs. -/
theorem Relation.gfp_eq_closedForm {α ε : Type _} [Monoid ε] [OmegaProd ε]
    (hunfold : OmegaProd.HasUnfold ε) (lim : OmegaProd.HasProductLimit ε)
    {X : Set (α × ε × α)} {Y : Set (α × ε)} (prod : Relation.Productive X) :
    OrderHom.gfp (Relation.divFun X Y) = (Relation.star X ∘ᵣ₁ Y) ∪ Relation.omega X :=
  le_antisymm (Relation.gfp_le_closedForm lim prod) (Relation.closedForm_le_gfp hunfold)

end
