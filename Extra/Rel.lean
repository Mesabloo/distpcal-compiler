module

meta import CustomPrelude
public import Mathlib.Data.Rel
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.OmegaCompletePartialOrder
public import Extra.AesopRuleSets
public import Extra.Prod
import Extra.Set
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic

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

/-- The idle transition: no state change, empty trace. Unit of both compositions above
(`lcomp₁.left_id_eq`, `lcomp₂.left_id_eq`/`.right_id_eq`), base case of a statement list's semantics
(`GuardedPlusCal.Block.listReducing`), semantics of a branch with no precondition
(`AtomicBranch.reducing`), and the reflexive half of `Relation.starFun`.

Exposed for the same reason the two compositions are: proofs destructure membership directly with
`rintro ⟨rfl, rfl⟩`. -/
@[expose]
def Relation.Idle {α β : Type _} [Monoid β] : Set (α × β × α) := {⟨x, e, y⟩ | x = y ∧ e = 1}

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

theorem Relation.lcomp₁.subset_of_subset_right {α β γ : Type _} [Monoid β] {R : Set (α × β × γ)} {x y : Set (γ × β)} (x_sub_y : x ⊆ y) : R ∘ᵣ₁ x ⊆ R ∘ᵣ₁ y :=
  Relation.lcomp₁.mono le_rfl x_sub_y

theorem Relation.lcomp₁.subset_of_subset_left {α β γ : Type _} [Monoid β] {R₁ R₂ : Set (α × β × γ)} {x : Set (γ × β)} (R₁_sub_R₂ : R₁ ⊆ R₂) : R₁ ∘ᵣ₁ x ⊆ R₂ ∘ᵣ₁ x :=
  Relation.lcomp₁.mono R₁_sub_R₂ le_rfl

theorem Relation.lcomp₁.right_empty_eq_empty {α β γ : Type _} [Monoid β] {R : Set (α × β × γ)} : R ∘ᵣ₁ ∅ = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro ⟨a, e⟩ ⟨b, e₁, e₂, b_in_r, _|_, _⟩

theorem Relation.lcomp₂.left_id_eq {α β γ : Type _} [Monoid β] {R : Set (α × β × γ)} : Relation.Idle ∘ᵣ₂ R = R := by
  ext ⟨a, e, c⟩
  iff_rintro ⟨b, e₁, e₂, ⟨rfl, rfl⟩, _, rfl⟩ _
  · rwa [Monoid.one_mul]
  · exists a, 1, e
    and_intros
    · rfl
    · rfl
    · assumption
    · rw [Monoid.one_mul]

theorem Relation.lcomp₁.left_id_eq {α β : Type _} [Monoid β] {R : Set (α × β)} : Relation.Idle ∘ᵣ₁ R = R := by
  ext ⟨a, e⟩
  iff_rintro ⟨b, e₁, e₂, ⟨rfl, rfl⟩, _, rfl⟩ _
  · rwa [Monoid.one_mul]
  · exists a, 1, e
    and_intros <;> try trivial
    rw [Monoid.one_mul]

theorem Relation.lcomp₂.right_id_eq {α β γ : Type _} [Monoid β] {R : Set (α × β × γ)} : R ∘ᵣ₂ Relation.Idle = R := by
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

/-- Refolding a two-step run's aborting set: the abort that happens after both steps can be attached
to the second step alone. Read left to right it is how a `cons` of aborting semantics is taken apart;
read right to left it is how the tail of an induction is put back together. -/
theorem Relation.lcomp₁.union_lcomp₂ {α β γ δ : Type _} [Monoid β] {R : Set (α × β × γ)}
    {S : Set (γ × β × δ)} {A : Set (α × β)} {X : Set (γ × β)} {Y : Set (δ × β)} :
    (A ∪ R ∘ᵣ₁ X) ∪ (R ∘ᵣ₂ S) ∘ᵣ₁ Y = A ∪ R ∘ᵣ₁ (X ∪ S ∘ᵣ₁ Y) := by
  rw [Relation.lcomp₁.left_lcomp₂_eq, Relation.lcomp₁.right_union_eq_union, Set.union_assoc]

/-- A step that changes nothing can be dropped off the front of a run that fails after it. -/
theorem Relation.lcomp₁.le_of_left_le_idle {α β : Type _} [Monoid β] {R : Set (α × β × α)}
    {X : Set (α × β)} (h : R ≤ Relation.Idle) : R ∘ᵣ₁ X ≤ X :=
  calc R ∘ᵣ₁ X ≤ Relation.Idle ∘ᵣ₁ X := by gcongr
    _ = X := Relation.lcomp₁.left_id_eq

/-- **One step of an "aborting commutes past" induction.** `Q` is the statement being moved leftwards
and `R` what it is moved past; `Qa`/`Ra` are their aborting sets, `Q'`/`Qa'` what `Q` becomes on the
far side.

The three hypotheses are the three things such a step ever needs: that the *reducing* relations
commute (`hcomm`), that `Q`'s own aborts are covered once it has crossed `R` (`hhead`), and that the
rest of the run is covered (`htail`). `hmid` absorbs a preceding inclusion — the induction hypothesis,
where there is one, and `le_rfl` where the run is already in this shape.

Stated on bare relations because every user is the same algebra over different statements: a guard
substituted into, a guard whose index was bumped, and a whole walk. -/
theorem Relation.lcomp₁.commute_step {α β : Type _} [Monoid β] {Q Q' R : Set (α × β × α)}
    {Qa Qa' Ra Xa Ya Z : Set (α × β)} (hcomm : Q ∘ᵣ₂ R = R ∘ᵣ₂ Q')
    (hhead : Qa ∪ Q ∘ᵣ₁ Ra ≤ Ra ∪ R ∘ᵣ₁ Qa') (hmid : Z ≤ Ra ∪ R ∘ᵣ₁ Xa)
    (htail : Qa' ∪ Q' ∘ᵣ₁ Xa ≤ Ya) :
    Qa ∪ Q ∘ᵣ₁ Z ≤ Ra ∪ R ∘ᵣ₁ Ya :=
  calc Qa ∪ Q ∘ᵣ₁ Z
      ≤ Qa ∪ Q ∘ᵣ₁ (Ra ∪ R ∘ᵣ₁ Xa) := by gcongr
    _ = (Qa ∪ Q ∘ᵣ₁ Ra) ∪ (Q ∘ᵣ₂ R) ∘ᵣ₁ Xa := Relation.lcomp₁.union_lcomp₂.symm
    _ ≤ (Ra ∪ R ∘ᵣ₁ Qa') ∪ (R ∘ᵣ₂ Q') ∘ᵣ₁ Xa := by
        rw [hcomm]
        exact Set.union_le_union hhead le_rfl
    _ = Ra ∪ R ∘ᵣ₁ (Qa' ∪ Q' ∘ᵣ₁ Xa) := Relation.lcomp₁.union_lcomp₂
    _ ≤ Ra ∪ R ∘ᵣ₁ Ya := by gcongr
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

/-- A product splits wherever its index does. What lets the trace of two runs concatenated be read
as the two runs' traces multiplied. -/
theorem Monoid.partialProd_add {ε : Type _} [Monoid ε] (e : ℕ → ε) (n₁ n₂ : ℕ) :
    Monoid.partialProd e (n₁ + n₂) =
      Monoid.partialProd e n₁ * Monoid.partialProd (λ i ↦ e (n₁ + i)) n₂ := by
  induction n₂ with
  | zero => simp
  | succ n₂ ih => rw [← Nat.add_assoc, Monoid.partialProd_succ, ih, Monoid.partialProd_succ,
      mul_assoc]

/-- A product of ones is one. -/
theorem Monoid.partialProd_eq_one {ε : Type _} [Monoid ε] {e : ℕ → ε} {n : ℕ}
    (h : ∀ i < n, e i = 1) : Monoid.partialProd e n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Monoid.partialProd_succ, ih (λ i hi ↦ h i (Nat.lt_succ_of_lt hi)),
      h n (Nat.lt_succ_self n), mul_one]

/-- **Skipping a stretch of ones.** Extending a product past factors that are all `1` does not
change it — the gap-splitting fact a reindexed product needs, since deleting `1`s from a sequence is
exactly refusing to extend across them. `partialProd_add` does the splitting; this says the second
factor is trivial. -/
theorem Monoid.partialProd_eq_of_ones {ε : Type _} [Monoid ε] {e : ℕ → ε} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ i, a ≤ i → i < b → e i = 1) :
    Monoid.partialProd e b = Monoid.partialProd e a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  have hones : Monoid.partialProd (λ i ↦ e (a + i)) d = 1 := by
    refine Monoid.partialProd_eq_one (λ i hi ↦ ?_)
    exact h (a + i) (Nat.le_add_right _ _) (Nat.add_lt_add_left hi a)
  rw [Monoid.partialProd_add, hones, mul_one]

/-- A monoid in which an infinite sequence of factors has a well-behaved product. A mixin over
`Monoid` rather than an extension of it, so that the existing `[Monoid ε]` binders throughout the
refinement framework are untouched and no instance diamond arises. Carries the five laws refinement
proofs consume, so that they read them from the instance instead of threading them as explicit
hypotheses. -/
class ωMonoid (ε : Type _) [Monoid ε] where
  /-- The product of infinitely many factors. -/
  ωProd : (ℕ → ε) → ε
  /-- Every finite prefix of an infinite product divides it. -/
  partialProd_dvd : ∀ (e : ℕ → ε) (n : ℕ), ∃ r, ωProd e = Monoid.partialProd e n * r
  /-- The first factor of an infinite product comes out in front. -/
  unfold : ∀ e : ℕ → ε, ωProd e = e 0 * ωProd (λ i ↦ e (i + 1))
  /-- An element having every partial product as a left factor *is* the infinite product, provided
  the sequence keeps contributing. -/
  productLimit : ∀ (e r : ℕ → ε) (x : ε), (∀ n, x = Monoid.partialProd e n * r n) →
    (∀ n, ∃ m, n ≤ m ∧ e m ≠ 1) → x = ωProd e
  /-- Deleting factors that are `1` does not change the product. -/
  ωProd_comp : ∀ (e : ℕ → ε) (n : ℕ → ℕ), StrictMono n →
    (∀ i, (∀ j, n j ≠ i) → e i = 1) → ωProd e = ωProd (e ∘ n)

/-- `R^∞` — the states from which `R` can step forever, paired with the trace the whole infinite
run emits. -/
@[expose]
def Relation.omega {α ε : Type _} [Monoid ε] [ωMonoid ε] (R : Set (α × ε × α)) : Set (α × ε) :=
  {x | ∃ (σs : ℕ → α) (es : ℕ → ε),
    σs 0 = x.1 ∧ (∀ i, (σs i, es i, σs (i + 1)) ∈ R) ∧ x.2 = ωMonoid.ωProd es}

theorem Relation.omega.mono {α ε : Type _} [Monoid ε] [ωMonoid ε] {R S : Set (α × ε × α)}
    (h : R ≤ S) : Relation.omega R ≤ Relation.omega S := by
  rintro ⟨σ, ε⟩ ⟨σs, es, h₀, hstep, hε⟩
  exact ⟨σs, es, h₀, λ i ↦ h (hstep i), hε⟩

open Classical in
/-- **Deleting idle steps from an infinite run.** A run in which every index either steps or stands
still — emitting `1` when it stands still — is a run of the stepping relation alone, provided it
steps *cofinally often*.

This is what a stuttering simulation needs and cannot get from `Relation.omega.mono`:
`Relation.omega (R ∪ Idle) ≤ Relation.omega R` is false outright, since standing still forever is a
witness of the left and of nothing on the right. Cofinality is exactly the missing side condition,
and a caller supplies it from whatever well-founded measure forbids an infinite idle tail.

The compressed run is indexed by the *moving* indices, so its product is the original's with the
idle factors deleted; `ωMonoid.ωProd_comp` handles that. -/
theorem Relation.omega.of_idle {α ε : Type _} [Monoid ε] [ωMonoid ε] {R : Set (α × ε × α)}
    {σs : ℕ → α} {es : ℕ → ε}
    (hstep : ∀ i, (σs i, es i, σs (i + 1)) ∈ R ∨ (σs (i + 1) = σs i ∧ es i = 1))
    (hinf : ∀ N, ∃ i, N ≤ i ∧ (σs i, es i, σs (i + 1)) ∈ R) :
    (σs 0, ωMonoid.ωProd es) ∈ Relation.omega R := by
  -- the moving indices, enumerated in order: the least one, then the least one after each
  let Moves (i : ℕ) : Prop := (σs i, es i, σs (i + 1)) ∈ R
  have hex (N : ℕ) : ∃ i, N ≤ i ∧ Moves i := hinf N
  let n : ℕ → ℕ := Nat.rec (Nat.find (hex 0)) (λ j m ↦ Nat.find (hex (m + 1)))
  have hn_zero : Moves (n 0) := (Nat.find_spec (hex 0)).2
  have hn_succ : ∀ j, n j + 1 ≤ n (j + 1) ∧ Moves (n (j + 1)) := λ j ↦ Nat.find_spec (hex (n j + 1))
  have hmono : StrictMono n := strictMono_nat_of_lt_succ (λ j ↦ (hn_succ j).1)
  have hmoves : ∀ j, Moves (n j) := by
    rintro (_ | j)
    · exact hn_zero
    · exact (hn_succ j).2
  -- every moving index is enumerated: below `n 0` nothing moves, and nothing moves strictly between
  -- consecutive values either, both by the minimality `Nat.find` gives
  have hrange : ∀ j i, i < n j → Moves i → ∃ j', j' < j ∧ n j' = i := by
    intro j
    induction j with
    | zero =>
      intro i hi hm
      absurd Nat.find_min (hex 0) hi
      exact ⟨Nat.zero_le i, hm⟩
    | succ j ih =>
      intro i hi hm
      rcases Nat.lt_trichotomy i (n j) with h | h | h
      · obtain ⟨j', hj', hnj'⟩ := ih i h hm
        exact ⟨j', Nat.lt_succ_of_lt hj', hnj'⟩
      · exact ⟨j, Nat.lt_succ_self j, h.symm⟩
      · absurd Nat.find_min (hex (n j + 1)) hi
        exact ⟨h, hm⟩
  have hidle : ∀ i, (∀ j, n j ≠ i) → σs (i + 1) = σs i ∧ es i = 1 := by
    intro i hi
    rcases hstep i with hm | hidle
    · obtain ⟨j', -, hnj'⟩ := hrange (i + 1) i (Nat.lt_of_lt_of_le (Nat.lt_succ_self i)
        hmono.le_apply) hm
      absurd hi j'
      exact hnj'
    · exact hidle
  -- an idle stretch leaves the state where it was
  have hfix : ∀ a b, a ≤ b → (∀ i, a ≤ i → i < b → (∀ j, n j ≠ i)) → σs b = σs a := by
    intro a b hab
    induction b with
    | zero =>
      intro _
      obtain rfl : a = 0 := Nat.le_zero.mp hab
      rfl
    | succ b ih =>
      intro hoff
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · have hb : σs b = σs a := ih (Nat.le_of_lt_succ h) (λ i hi hib ↦ hoff i hi
          (Nat.lt_succ_of_lt hib))
        rw [(hidle b (hoff b (Nat.le_of_lt_succ h) (Nat.lt_succ_self b))).1, hb]
      · obtain rfl : a = b + 1 := Nat.le_antisymm hab h
        rfl
  refine ⟨λ j ↦ σs (n j), λ j ↦ es (n j), ?_, ?_, ?_⟩
  · refine hfix 0 (n 0) (Nat.zero_le _) (λ i _ hi j hj ↦ ?_)
    absurd Nat.not_lt.mpr (hmono.monotone (Nat.zero_le j))
    exact hj ▸ hi
  · intro j
    have hgap : σs (n (j + 1)) = σs (n j + 1) := by
      refine hfix (n j + 1) (n (j + 1)) (hn_succ j).1 (λ i hi hlt j' hj' ↦ ?_)
      subst hj'
      have h₁ : j < j' := hmono.lt_iff_lt.mp hi
      have h₂ : j' < j + 1 := hmono.lt_iff_lt.mp hlt
      omega
    show (σs (n j), es (n j), σs (n (j + 1))) ∈ R
    rw [hgap]
    exact hmoves j
  · exact ωMonoid.ωProd_comp es n hmono (λ i hi ↦ (hidle i hi).2)

/-- Dropping the first step of an infinite run leaves an infinite run. Every proof that
destructures a `Relation.omega` membership and then has to put the tail back together needs this,
so it is stated once here rather than re-instantiated at each site. -/
theorem Relation.omega.tail {α ε : Type _} [Monoid ε] [ωMonoid ε] {R : Set (α × ε × α)}
    {σs : ℕ → α} {es : ℕ → ε} (hstep : ∀ i, (σs i, es i, σs (i + 1)) ∈ R) :
    (σs 1, ωMonoid.ωProd (λ i ↦ es (i + 1))) ∈ Relation.omega R :=
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

/-- One step is a run. -/
theorem Relation.star.single {α ε : Type _} [Monoid ε] {R : Set (α × ε × α)} :
    R ≤ Relation.star R := by
  rintro ⟨a, e, b⟩ h
  rw [← mul_one e]
  exact Relation.star.head h (Relation.star.refl b)

/-- Two runs end to end. Proved by peeling the first step of the left-hand run rather than by
concatenating the two index-wise: `Relation.star.head` already knows how to put a step in front, so
the induction only has to keep the trace's factors in the same order — which is
`Monoid.partialProd_succ'`. -/
theorem Relation.star.trans {α ε : Type _} [Monoid ε] {R : Set (α × ε × α)} {a b c : α} {e₁ e₂ : ε}
    (h₁ : (a, e₁, b) ∈ Relation.star R) (h₂ : (b, e₂, c) ∈ Relation.star R) :
    (a, e₁ * e₂, c) ∈ Relation.star R := by
  obtain ⟨n, σs, es, hz, hn, hst, rfl⟩ := h₁
  dsimp only at hz hn ⊢
  induction n generalizing a σs es with
  | zero =>
    obtain rfl : a = b := hz.symm.trans hn
    rw [Monoid.partialProd_zero, one_mul]
    exact h₂
  | succ n ih =>
    rw [Monoid.partialProd_succ', mul_assoc]
    exact Relation.star.head (hz ▸ hst 0 (by omega))
      (ih (λ i ↦ σs (i + 1)) (λ i ↦ es (i + 1)) (λ i hi ↦ hst (i + 1) (by omega)) rfl hn)

/-- Runs of runs are runs. What lets a refinement whose *source* side already absorbs a whole run
per target step be lifted to the whole iteration: instantiating `StrongRefinement.Terminating.star`
at `Relation.star R` produces `R**` on the source, and this collapses it back. -/
theorem Relation.star.star_eq {α ε : Type _} [Monoid ε] {R : Set (α × ε × α)} :
    Relation.star (Relation.star R) = Relation.star R := by
  refine le_antisymm ?_ Relation.star.single
  rintro ⟨a, e, b⟩ ⟨n, σs, es, hz, hn, hst, rfl⟩
  dsimp only at hz hn ⊢
  induction n generalizing a σs es with
  | zero =>
    obtain rfl : a = b := hz.symm.trans hn
    exact Relation.star.refl _
  | succ n ih =>
    rw [Monoid.partialProd_succ']
    exact Relation.star.trans (hz ▸ hst 0 (by omega))
      (ih (σs 1) (λ i ↦ σs (i + 1)) (λ i ↦ es (i + 1)) (λ i hi ↦ hst (i + 1) (by omega)) rfl hn)

/-- A whole **run** in front of a run-then-`Y` is again a run-then-`Y`. The absorption law at the
shape a refinement whose *source* absorbs a run per target step produces
(`StrongRefinement.Terminating.starStutter`): there the side condition arrives with `Relation.star R`
where `lcomp₁_absorb` has `R`.

`lcomp₁_absorb` at `R := Relation.star R`, with `star_eq` collapsing the `R**` it leaves behind. -/
theorem Relation.star.star_lcomp₁_absorb {α ε : Type _} [Monoid ε] {R : Set (α × ε × α)}
    {Y : Set (α × ε)} :
    Relation.star R ∘ᵣ₁ (Relation.star R ∘ᵣ₁ Y) ≤ Relation.star R ∘ᵣ₁ Y := by
  have h := Relation.star.lcomp₁_absorb (R := Relation.star R) (Y := Y)
  rwa [Relation.star.star_eq] at h

end
