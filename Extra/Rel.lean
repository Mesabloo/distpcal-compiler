module

meta import CustomPrelude
public import Mathlib.Data.Rel
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.OmegaCompletePartialOrder
public import Extra.AesopRuleSets
import Extra.Set

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

/-- `Set.union_subset_union` restated at `≤`. Mathlib tags only the `⊆` form for `gcongr`, while
the two composition lemmas above are tagged at `≤`, so a goal mixing a union with a composition —
which is every monotonicity obligation of a semantic functional — matches at neither relation and
`gcongr` reports no progress. Registering the `≤` form is what lets it descend through both. -/
@[gcongr]
theorem Set.union_le_union {α : Type _} {s s' t t' : Set α} (h₁ : s ≤ s') (h₂ : t ≤ t') : s ∪ t ≤ s' ∪ t' :=
  Set.union_subset_union h₁ h₂

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
  iff_rintro ⟨b, e₁, e₂, ⟨rfl, rfl⟩, _, rfl⟩ _
  · rwa [Monoid.one_mul]
  · exists a, 1, e
    and_intros
    · rfl
    · rfl
    · assumption
    · rw [Monoid.one_mul]

theorem Relation.lcomp₁.left_id_eq {α β : Type _} [Monoid β] {R : Set (α × β)} : {⟨x, e, y⟩ | x = y ∧ e = 1} ∘ᵣ₁ R = R := by
  ext ⟨a, e⟩
  iff_rintro ⟨b, e₁, e₂, ⟨rfl, rfl⟩, _, rfl⟩ _
  · rwa [Monoid.one_mul]
  · exists a, 1, e
    and_intros <;> try trivial
    rw [Monoid.one_mul]

theorem Relation.lcomp₂.right_id_eq {α β γ : Type _} [Monoid β] {R : Set (α × β × γ)} : R ∘ᵣ₂ {⟨x, e, y⟩ | x = y ∧ e = 1} = R := by
  ext ⟨a, e, c⟩
  iff_rintro ⟨b, e₁, e₂, _, ⟨rfl, rfl⟩, rfl⟩ _
  · rwa [Monoid.mul_one]
  · exists c, e, 1
    and_intros
    · assumption
    · rfl
    · rfl
    · rw [Monoid.mul_one]

theorem Relation.lcomp₂.assoc {α β γ δ ε : Type _} [Monoid β] {R₁ : Set (α × β × γ)} {R₂ : Set (γ × β × δ)} {R₃ : Set (δ × β × ε)} :
  R₁ ∘ᵣ₂ (R₂ ∘ᵣ₂ R₃) = (R₁ ∘ᵣ₂ R₂) ∘ᵣ₂ R₃ := by
    ext ⟨a, e, d⟩
    iff_rintro ⟨b, e₁, e₂, aR₁b, ⟨c, e₃, e₄, bR₂c, cR₃d, rfl⟩, rfl⟩ ⟨c, e₁, e₂, ⟨b, e₃, e₄, aR₁b, bR₂c, rfl⟩, cR₃d, rfl⟩
    · rw [← mul_assoc]
      exists c, e₁ * e₃, e₄
      and_intros
      · exists b, e₁, e₃
      · assumption
      · rfl
    · rw [mul_assoc]
      exists b, e₃, e₄ * e₂
      and_intros
      · assumption
      · exists c, e₄, e₂
      · rfl

theorem Relation.lcomp₁.left_lcomp₂_eq {α β γ δ : Type _} [Monoid β] {R₁ : Set (α × β × γ)} {R₂ : Set (γ × β × δ)} {R₃ : Set (δ × β)} : (R₁ ∘ᵣ₂ R₂) ∘ᵣ₁ R₃ = R₁ ∘ᵣ₁ (R₂ ∘ᵣ₁ R₃) := by
  ext ⟨a, e⟩
  iff_rintro ⟨c, _, e₃, ⟨b, e₁, e₂, _, _, rfl⟩, _, rfl⟩ ⟨b, e₁, e₂, _, ⟨c, e₂, e₃, _, _, rfl⟩, rfl⟩
  · rw [mul_assoc]
    exists b, e₁, e₂ * e₃
    and_intros <;> try trivial
    exists c, e₂, e₃
  · rw [← mul_assoc]
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

Deliberately carries no laws, so that registering an instance costs nothing. The laws refinement
proofs consume are stated as separate predicates over this class and passed explicitly to the
lemmas that need them — `OmegaProd.HasPartialProdDvd` and friends, in
`VerifiedCompiler/ClosedForm.lean`, which is downstream of every semantics file. -/
class OmegaProd (ε : Type _) [Monoid ε] where
  /-- The product of infinitely many factors. -/
  ωProd : (ℕ → ε) → ε

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

/-- Dropping the first step of an infinite run leaves an infinite run. Every proof that
destructures a `Relation.omega` membership and then has to put the tail back together needs this,
so it is stated once here rather than re-instantiated at each site. -/
theorem Relation.omega.tail {α ε : Type _} [Monoid ε] [OmegaProd ε] {R : Set (α × ε × α)}
    {σs : ℕ → α} {es : ℕ → ε} (hstep : ∀ i, (σs i, es i, σs (i + 1)) ∈ R) :
    (σs 1, OmegaProd.ωProd (λ i ↦ es (i + 1))) ∈ Relation.omega R :=
  ⟨λ i ↦ σs (i + 1), λ i ↦ es (i + 1), rfl, λ i ↦ hstep (i + 1), rfl⟩


/-! ## Finite iteration

`R*`. Stated in the same ℕ-indexed shape as `Relation.omega` rather than reusing
`Relation.TraceReflTransGen` (`VerifiedCompiler/Relation.lean`), which is `Prop`-valued. Sharing the
shape is what lets the two refinement lemmas — one for `R*`, one for `R^∞` — be proved by the same
kind of induction over the index.
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

/-- A step in front of a run-then-`Y` is again a run-then-`Y`.

This is the absorption side condition that the aborting and diverging refinements both need in order
to place an abort reached after `n` steps in the aborting set itself rather than in
`semⁿ ∘ᵣ₁ sem'`. Stated at the closed form it is a theorem; at an arbitrary aborting semantics it
has to be assumed, which is what `Diverging.omega`'s and `Diverging.star`'s `abs` binder is. -/
theorem Relation.star.lcomp₁_absorb {α ε : Type _} [Monoid ε] {R : Set (α × ε × α)}
    {Y : Set (α × ε)} : R ∘ᵣ₁ (Relation.star R ∘ᵣ₁ Y) ≤ Relation.star R ∘ᵣ₁ Y := by
  rintro ⟨σ, e⟩ ⟨b, e₁, e₂, hR, ⟨c, e₃, e₄, hs, hy, rfl⟩, rfl⟩
  rw [← mul_assoc]
  apply Relation.lcomp₁.intro (Relation.star.head hR hs) hy

/-- `Y` itself is a run-then-`Y`, the run being empty. The base case of the absorption above, and
what lets an aborting refinement of `Y` be read as one of `R* ∘ᵣ₁ Y`. -/
theorem Relation.star.le_lcomp₁ {α ε : Type _} [Monoid ε] {R : Set (α × ε × α)}
    {Y : Set (α × ε)} : Y ≤ Relation.star R ∘ᵣ₁ Y := by
  rintro ⟨σ, e⟩ hy
  rw [← one_mul e]
  apply Relation.lcomp₁.intro (Relation.star.refl σ) hy

end
