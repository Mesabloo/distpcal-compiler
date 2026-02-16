import CustomPrelude
import Mathlib.Data.Rel
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Order.CompletePartialOrder
import Extra.Set

theorem todo_rename {α β γ : Type*} (f : SetRel α β) (g : SetRel β γ) (A : Set α) (B : Set β) (C : Set γ)
  (h₁ : B ⊆ f.image A) (h₂ : C ⊆ g.image B) : C ⊆ (f.comp g).image A := by
    calc
      C ⊆ SetRel.image g B := h₂
      _ ⊆ SetRel.image g (SetRel.image f A) := SetRel.image_subset_image h₁
      _ = SetRel.image (SetRel.comp f g) A := SetRel.image_comp _ _ _ |>.symm

def Relation.lcomp₁ {α β γ : Type _} [Monoid β] (R₁ : Set (α × β × γ)) (W : Set (γ × β)) : Set (α × β) :=
  {(x, c) | ∃ y a b, (x, a, y) ∈ R₁ ∧ (y, b) ∈ W ∧ c = a * b}

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
    rw [OmegaCompletePartialOrder.Chain.map_coe, OrderHom.coe_mk, Function.comp_def]
    exists b, e₁, e₂
  · rw [Set.mem_range, OmegaCompletePartialOrder.Chain.map_coe, OrderHom.coe_mk, Function.comp_def] at B_in
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
    rw [OmegaCompletePartialOrder.Chain.map_coe, OrderHom.coe_mk, Function.comp_def]
    exists b, e₁, e₂
  · rw [Set.mem_range, OmegaCompletePartialOrder.Chain.map_coe, OrderHom.coe_mk, Function.comp_def] at B_in
    obtain ⟨i, rfl⟩ := B_in
    obtain ⟨b, e₁, e₂, bRa, _, rfl⟩ := a_in_comp
    exists b, e₁, e₂
    and_intros
    · assumption
    · rw [Set.ωSup_is_iUnion, Set.mem_iUnion]
      exists i
    · rfl

theorem OrderHom.lfp_induction₂ {α β : Type _} [CompleteLattice α] [CompleteLattice β] (f : α →o α) (g : β →o β) {p : α → β → Prop}
  (step : ∀ (a : α) (b : β), p a b → a ≤ OrderHom.lfp f → b ≤ OrderHom.lfp g → p (f a) (g b))
  (hSup : ∀ (s : Set (α × β)), (∀ x ∈ s, p x.1 x.2) → p (Prod.fst <| sSup s) (Prod.snd <| sSup s)) :
    p (OrderHom.lfp f) (OrderHom.lfp g) := by
  set s := { ⟨x, y⟩ : _ × _ | x ≤ lfp f ∧ y ≤ lfp g ∧ p x y}

  specialize hSup s λ x x_in ↦ x_in.2.2

  suffices sSup s = (lfp f, lfp g) by
    rwa [this] at hSup

  obtain ⟨h₁, h₂⟩ : sSup s ≤ (lfp f, lfp g) := by
    apply sSup_le
    rintro ⟨x, y⟩ ⟨x_le_lfp_f, y_le_lfp_g, -⟩
    grw [x_le_lfp_f, y_le_lfp_g]

  have : (f (sSup s).1, g (sSup s).2) ∈ s := by
    refine ⟨?_, ?_, ?_⟩
    · grw [map_le_lfp f]; assumption
    · grw [map_le_lfp g]; assumption
    · apply step _ _ hSup <;> assumption

  apply LE.le.antisymm
  · exact ⟨h₁, h₂⟩
  · constructor
    · apply lfp_le
      apply le_sSup
      exact Set.mem_image_fst_of_mem _ this
    · apply lfp_le
      apply le_sSup
      exact Set.mem_image_snd_of_mem _ this

theorem OrderHom.lfp_induction₃ {α β γ : Type _} [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] (f : α →o α) (g : β →o β) (h : γ →o γ) {p : α → β → γ → Prop}
  (step : ∀ (a : α) (b : β) (c : γ), p a b c → a ≤ OrderHom.lfp f → b ≤ OrderHom.lfp g → c ≤ OrderHom.lfp h → p (f a) (g b) (h c))
  (hSup : ∀ (s : Set (α × β × γ)), (∀ x ∈ s, p x.1 x.2.1 x.2.2) → p (Prod.fst <| sSup s) (Prod.fst <| Prod.snd <| sSup s) (Prod.snd <| Prod.snd <| sSup s)) :
    p (OrderHom.lfp f) (OrderHom.lfp g) (OrderHom.lfp h) := by
  set s := { ⟨x, y, z⟩ : _ × _ × _ | x ≤ lfp f ∧ y ≤ lfp g ∧ z ≤ lfp h ∧ p x y z}

  specialize hSup s λ x x_in ↦ x_in.2.2.2

  suffices sSup s = (lfp f, lfp g, lfp h) by
    rwa [this] at hSup

  obtain ⟨h₁, h₂, h₃⟩ : sSup s ≤ (lfp f, lfp g, lfp h) := by
    apply sSup_le
    rintro ⟨x, y, z⟩ ⟨x_le_lfp_f, y_le_lfp_g, z_le_lfp_h, -⟩
    grw [x_le_lfp_f, y_le_lfp_g, z_le_lfp_h]

  have : (f (sSup s).1, g (sSup s).2.1, h (sSup s).2.2) ∈ s := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · grw [map_le_lfp f]; assumption
    · grw [map_le_lfp g]; assumption
    · grw [map_le_lfp h]; assumption
    · apply step _ _ _ hSup <;> assumption

  apply LE.le.antisymm
  · exact ⟨h₁, h₂, h₃⟩
  · refine ⟨?_, ?_, ?_⟩
    · apply lfp_le
      apply le_sSup
      exact Set.mem_image_fst_of_mem _ this
    · apply lfp_le
      apply le_sSup
      apply Set.mem_image_fst_of_mem
      exact Set.mem_image_snd_of_mem _ this
    · apply lfp_le
      apply le_sSup
      apply Set.mem_image_snd_of_mem
      exact Set.mem_image_snd_of_mem _ this
