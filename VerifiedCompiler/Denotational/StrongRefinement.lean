import VerifiedCompiler.Trace
import Mathlib.Data.Rel
import Extra.Rel

namespace StrongRefinement
  variable {τ : Type _} [Trace τ] {α β : Type _} (R : Rel α β)

  /--
    Behavior refinement in the terminating case.

    - `semₛ` is the reducing semantics for the source language.
    - `semₛ'` is the aborting semantics for the source language.
    - `semₜ` is the reducing semantics for the target language.
  -/
  protected def Terminating (semₛ : Set (α × τ × α)) (semₛ' : Set (α × τ)) (semₜ : Set (β × τ × β)) : Prop :=
    ∀ (σₜ σₜ' : β) (ε : τ) (σₛ : α), R σₛ σₜ → (σₜ, ε, σₜ') ∈ semₜ →
      (∃ (σₛ' : α), R σₛ' σₜ' ∧ (σₛ, ε, σₛ') ∈ semₛ) ∨ (∃ ε' ≤ ε, (σₛ, ε') ∈ semₛ')

  protected theorem Terminating.Comp {semₛ semᵤ : Set (α × τ × α)} {semₛ' semᵤ' : Set (α × τ)} {semₜ semᵥ : Set (β × τ × β)} :
      StrongRefinement.Terminating R semₛ semₛ' semₜ → StrongRefinement.Terminating R semᵤ semᵤ' semᵥ →
      StrongRefinement.Terminating R (semₛ ∘ᵣ₂ semᵤ) (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₜ ∘ᵣ₂ semᵥ) := by
    rintro ref_semₜ ref_semᵥ σₜ σᵥ'' ε σₛ σₛRσₜ ⟨σᵥ', ε₁, ε₂, red_σₜ_σᵥ', red_σᵥ'_σᵥ'', rfl⟩
    obtain ⟨σₛ', σₛ'Rσᵥ', _⟩|⟨ε', _, _⟩ := ref_semₜ _ _ _ _ σₛRσₜ red_σₜ_σᵥ'
    · obtain ⟨σᵤ, _, _⟩|⟨ε', _, _⟩ := ref_semᵥ _ _ _ _ σₛ'Rσᵥ' red_σᵥ'_σᵥ''
      · left
        exists σᵤ
        and_intros <;> try assumption
        exists σₛ', ε₁, ε₂
      · right
        exists ε₁ * ε'
        and_intros
        · apply Trace.le_mul_right_inj
          assumption
        · right
          exists σₛ', ε₁, ε'
    · right
      exists ε'
      and_intros
      · apply Trace.le_extend_mul
        assumption
      · left
        assumption

  protected theorem Terminating.Mono {R}
    {semᵣ semₛ : Set (α × τ × α)} {semᵣ' semₛ' : Set (α × τ)} {semₜ semᵤ : Set (β × τ × β)}
    (hyp₁ : semₛ ≤ semᵣ) (hyp₂ : semₛ' ≤ semᵣ') (concl : semᵤ ≤ semₜ) :
      StrongRefinement.Terminating R semₛ semₛ' semₜ ≤ StrongRefinement.Terminating R semᵣ semᵣ' semᵤ := by
    intros ref σᵤ σᵤ' ε σᵣ' R_σᵣ'_σᵤ' sem_σᵤ'
    obtain ⟨σₛ', R_σₛ'_σᵤ', sem_σₛ'⟩|⟨ε', ε'_le_ε, sem_σₛ'⟩ := ref _ _ ε _ R_σᵣ'_σᵤ' (Set.mem_of_subset_of_mem concl sem_σᵤ')
    · left
      use σₛ', R_σₛ'_σᵤ', Set.mem_of_subset_of_mem hyp₁ sem_σₛ'
    · right
      use ε', ε'_le_ε, Set.mem_of_subset_of_mem hyp₂ sem_σₛ'

  protected theorem Terminating.Id {X} :
      StrongRefinement.Terminating R {(x, ε, y) : α × τ × α | x = y ∧ ε = Trace.τ} X {(x, ε, y) | x = y ∧ ε = Trace.τ} := by
    rintro σₜ σₜ' ε σₛ σₛRσₜ ⟨rfl, rfl⟩
    left
    exists σₛ

  protected theorem Terminating.sup {A : Set (Set (α × τ × α))} {B} {C}
    (sup : ∀ y ∈ B, ∃ x ∈ A, ∃ z ∈ C, StrongRefinement.Terminating R x z y) :
      StrongRefinement.Terminating R (⋃₀ A) (⋃₀ C) (⋃₀ B) := by
    rintro σₜ σₜ' ε σₛ R_σₛ_σₜ sem_σₜ_σₜ'

    rw [Set.mem_sUnion] at sem_σₜ_σₜ'
    obtain ⟨semₜ, semₜ_in_B, sem_σₜ_σₜ'⟩ := sem_σₜ_σₜ'
    obtain ⟨semₛ, semₛ_in_A, abortₛ, abortₛ_in_C, ref⟩ := sup semₜ semₜ_in_B
    obtain ⟨σₛ', R_σₛ'_σₜ', sem_σₛ_σₛ'⟩|⟨ε', ε'_le_ε, abortₛ_σₛ⟩ := ref _ _ _ _ R_σₛ_σₜ sem_σₜ_σₜ'
    · left
      exists σₛ', R_σₛ'_σₜ'
      exact Set.mem_sUnion_of_mem sem_σₛ_σₛ' semₛ_in_A
    · right
      exists ε', ε'_le_ε
      exact Set.mem_sUnion_of_mem abortₛ_σₛ abortₛ_in_C

  protected theorem Terminating.lfp {f : Set (α × τ × α) →o _} {g : Set (β × τ × β) →o _} {h : Set (α × τ) →o _}
    (IH : ∀ x y z, StrongRefinement.Terminating R x y z → StrongRefinement.Terminating R (f x) (h y) (g z)) :
      StrongRefinement.Terminating R (OrderHom.lfp f) (OrderHom.lfp h) (OrderHom.lfp g) := by
    apply OrderHom.lfp_induction₃ (p := λ x y z ↦ StrongRefinement.Terminating R x y z)
    · intros A B C ref_A_B_C A_le_lfp B_le_lfp C_le_lfp
      apply IH
      assumption
    · intros S hSup
      apply Terminating.sup
      intros y y_in
      obtain ⟨z, h⟩ := Set.exists_mem_of_mem_image_snd y_in
      obtain ⟨x, x_in⟩ := Set.exists_mem_of_mem_image_snd h
      use x, ?_, z, ?_, ?_
      3:    exact hSup _ x_in
      1,2:  grind only [= Set.mem_image, = Set.image_image]

  /--
    Behavior refinement in the diverging case.

    - `semₛ` is the diverging semantics for the source language.
    - `semₛ'` is the aborting semantics for the source language.
    - `semₜ` is the diverging semantics for the target language.
  -/
  protected def Diverging (semₛ semₛ' : Set (α × τ)) (semₜ : Set (β × τ)) : Prop :=
    ∀ (σₜ : β) (ε : τ) (σₛ : α), R σₛ σₜ → (σₜ, ε) ∈ semₜ →
      ((σₛ, ε) ∈ semₛ) ∨ (∃ ε' ≤ ε, (σₛ, ε') ∈ semₛ')

  /-- Vertical composition. -/
  protected theorem Diverging.Comp {semₛ : Set (α × τ × α)} {semₛ' semₛ'' semᵤ' semᵤ'' : Set (α × τ)} {semₜ : Set (β × τ × β)} {semₜ'' semᵥ'' : Set (β × τ)} :
      StrongRefinement.Diverging R semₛ'' semₛ' semₜ'' →
      StrongRefinement.Diverging R semᵤ'' semᵤ' semᵥ'' →
      StrongRefinement.Terminating R semₛ semₛ' semₜ →
      StrongRefinement.Diverging R (semₛ'' ∪ semₛ ∘ᵣ₁ semᵤ'') (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₜ'' ∪ semₜ ∘ᵣ₁ semᵥ'') := by
    rintro ref₁ ref₂ ref₃ σₜ ε σₛ R_σₛ_σₜ (semₜ''_σₜ|⟨σₜ', ε₁, ε₂, semₜ_σₜ_σₜ', semᵥ''_σₜ', rfl⟩)
    · obtain semₛ''_σₛ|⟨ε', ε'_le_ε, semₛ'_σₛ⟩ := ref₁ _ _ _ R_σₛ_σₜ semₜ''_σₜ
      · left; left
        exact semₛ''_σₛ
      · right
        exists ε', ε'_le_ε
        left
        exact semₛ'_σₛ
    · obtain ⟨σₛ', R_σₛ'_σₜ', semₛ_σₛ_σₛ'⟩|⟨ε', ε'_le_ε₁, semₛ'_σₛ⟩ := ref₃ _ _ _ _ R_σₛ_σₜ semₜ_σₜ_σₜ'
      · obtain semᵤ''_σₛ'|⟨ε', ε'_le_ε₂, semᵤ'_σₛ'⟩ := ref₂ _ _ _ R_σₛ'_σₜ' semᵥ''_σₜ'
        · left; right
          exists σₛ', ε₁, ε₂
        · right
          exists ε₁ * ε', Trace.le_mul_right_inj ε'_le_ε₂
          right
          exists σₛ', ε₁, ε'
      · right
        exists ε', Trace.le_extend_mul ε'_le_ε₁
        left
        exact semₛ'_σₛ

  protected theorem Diverging.Mono {R}
    {semᵣ'' semᵣ' semₛ'' semₛ' : Set (α × τ)} {semₜ'' semᵤ'' : Set (β × τ)}
    (hyp₁ : semₛ'' ≤ semᵣ'') (hyp₂ : semₛ' ≤ semᵣ') (concl : semᵤ'' ≤ semₜ'') :
      StrongRefinement.Diverging R semₛ'' semₛ' semₜ'' ≤ StrongRefinement.Diverging R semᵣ'' semᵣ' semᵤ'' := by
    intros ref σᵤ' ε σᵣ' R_σᵣ'_σᵤ' sem_σᵤ''
    obtain sem_σₛ''|⟨ε', ε'_le_ε, sem_σₛ'⟩ := ref _ ε _ R_σᵣ'_σᵤ' (Set.mem_of_subset_of_mem concl sem_σᵤ'')
    · left
      apply Set.mem_of_subset_of_mem hyp₁ sem_σₛ''
    · right
      use ε', ε'_le_ε, Set.mem_of_subset_of_mem hyp₂ sem_σₛ'

  protected theorem Diverging.Empty {semₛ'' semₛ' : Set (α × τ)} :
      StrongRefinement.Diverging R semₛ'' semₛ' ∅ := by
    rintro _ _ _ _ (_|_)


  protected theorem Diverging.inf {A : Set (Set (α × τ))} {B} {C}
    (sup : ∀ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, StrongRefinement.Diverging R x z y) :
      StrongRefinement.Diverging R (⋂₀ A) (⋃₀ C) (⋂₀ B) := by
    rintro σₜ ε σₛ R_σₛ_σₜ sem_σₜ_σₜ'

    rw [Set.mem_sInter] at sem_σₜ_σₜ' ⊢

    convert_to ∀ t ∈ A, (σₛ, ε) ∈ t ∨ ∃ ε' ≤ ε, (σₛ, ε') ∈ ⋃₀ C
    · grind only [cases Or]
    · intros semₛ semₛ_in_A
      obtain ⟨semₜ, semₜ_in_B, abortₛ, abortₛ_in_C, ref⟩ := sup _ semₛ_in_A
      specialize sem_σₜ_σₜ' _ semₜ_in_B
      obtain ⟨sem_σₛ_σₛ'⟩|⟨ε', ε'_le_ε, abortₛ_σₛ⟩ := ref _ _ _ R_σₛ_σₜ sem_σₜ_σₜ'
      · left
        assumption
      · right
        exists ε', ε'_le_ε
        exact Set.mem_sUnion_of_mem abortₛ_σₛ abortₛ_in_C

  protected theorem Diverging.gfp {f : Set (α × τ) →o _} {g : Set (β × τ) →o _} {h : Set (α × τ) →o _}
    (IH : ∀ x y z, StrongRefinement.Diverging R x y z → StrongRefinement.Diverging R (f x) (h y) (g z)) :
      StrongRefinement.Diverging R (OrderHom.gfp f) (OrderHom.lfp h) (OrderHom.gfp g) := by
    apply OrderHom.lfp_induction₃ f.dual h g.dual
    · intros A B C ref_A_B_C A_le_lfp B_le_lfp C_le_lfp
      apply IH
      assumption
    · intros S hSup
      apply Diverging.inf

      intros x x_in
      obtain ⟨⟨y, z⟩, h⟩ := Set.exists_mem_of_mem_image_fst x_in

      use z, ?_, y, ?_, ?_
      · apply Set.mem_image_snd_of_mem
        apply Set.mem_image_snd_of_mem _ h
      · apply Set.mem_image_fst_of_mem
        apply Set.mem_image_of_mem _ h
      · exact hSup _ h

  ------------------------------------

  /--
    Behavior refinement in the aborting case.

    - `semₛ'` is the aborting semantics for the source language.
    - `semₛ'` is the aborting semantics for the source language.
  -/
  protected def Aborting (semₛ' : Set (α × τ)) (semₜ' : Set (β × τ)) : Prop :=
    ∀ (σₜ : β) (ε : τ) (σₛ : α), R σₛ σₜ → (σₜ, ε) ∈ semₜ' → ∃ ε' ≤ ε, (σₛ, ε') ∈ semₛ'

  /-- Horizontal composition. -/
  protected theorem Terminating.Trans {γ} {R₁ R₂}
    {semₛ : Set (α × τ × α)} {semₛ' : Set (α × τ)}
    {semₜ : Set (β × τ × β)} {semₜ' : Set (β × τ)}
    {semᵤ : Set (γ × τ × γ)} :
      StrongRefinement.Terminating R₁ semₛ semₛ' semₜ →
      StrongRefinement.Aborting R₁ semₛ' semₜ' →
      StrongRefinement.Terminating R₂ semₜ semₜ' semᵤ →
      StrongRefinement.Terminating (Relation.Comp R₁ R₂) semₛ semₛ' semᵤ := by
    rintro ref₁ ref₃ ref₂ σᵤ σᵤ' ε σₛ ⟨σₜ, R₁_σₛ_σₜ, R₂_σₜ_σᵤ⟩ semᵤ_σᵤ_σᵤ'
    obtain ⟨σₜ', R₂_σₜ'_σᵤ', semₜ_σₜ_σₜ'⟩|⟨ε', ε'_le_ε, semₜ'_σₜ⟩ := ref₂ _ _ _ _ R₂_σₜ_σᵤ semᵤ_σᵤ_σᵤ'
    · obtain ⟨σₛ', R₁_σₛ'_σₜ', semₛ_σₛ_σₛ'⟩|⟨ε', ε'_le_ε, semₛ'_σₛ⟩ := ref₁ _ _ _ _ R₁_σₛ_σₜ semₜ_σₜ_σₜ'
      · left
        exists σₛ', ⟨σₜ', R₁_σₛ'_σₜ', R₂_σₜ'_σᵤ'⟩
      · right
        exists ε', ε'_le_ε
    · obtain ⟨ε'', ε''_le_ε', semₛ'_σₛ⟩ := ref₃ σₜ ε' σₛ R₁_σₛ_σₜ semₜ'_σₜ
      right
      exists ε'', le_trans ε''_le_ε' ε'_le_ε

  /-- Horizontal composition. -/
  protected theorem Diverging.Trans {γ} {R₁ R₂}
    {semₛ'' semₛ' : Set (α × τ)} {semₜ'' semₜ' : Set (β × τ)} {semᵤ'' : Set (γ × τ)} :
      StrongRefinement.Diverging R₁ semₛ'' semₛ' semₜ'' →
      StrongRefinement.Aborting R₁ semₛ' semₜ' →
      StrongRefinement.Diverging R₂ semₜ'' semₜ' semᵤ'' →
      StrongRefinement.Diverging (Relation.Comp R₁ R₂) semₛ'' semₛ' semᵤ'' := by
    rintro ref₁ ref₃ ref₂ σᵤ ε σₛ ⟨σₜ, R₁_σₛ_σₜ, R₂_σₜ_σᵤ⟩ semᵤ''_σᵤ
    obtain semₜ''_σₜ|⟨ε', ε'_le_ε, semₜ'_σₜ⟩ := ref₂ _ ε _ R₂_σₜ_σᵤ semᵤ''_σᵤ
    · obtain semₛ''_σₛ|⟨ε', ε'_le_ε, semₛ'_σₛ⟩ := ref₁ _ ε _ R₁_σₛ_σₜ semₜ''_σₜ
      · left
        exact semₛ''_σₛ
      · right
        exists ε'
    · obtain ⟨ε'', ε''_le_ε', semₛ'_σₛ⟩ := ref₃ _ _ _ R₁_σₛ_σₜ semₜ'_σₜ
      right
      exists ε'', le_trans ε''_le_ε' ε'_le_ε

  /-- Vertical composition. -/
  protected theorem Aborting.Comp {semₛ : Set (α × τ × α)} {semₛ' semᵤ' : Set (α × τ)} {semₜ : Set (β × τ × β)} {semₜ' semᵥ' : Set (β × τ)} :
      StrongRefinement.Aborting R semₛ' semₜ' →
      StrongRefinement.Aborting R semᵤ' semᵥ' →
      StrongRefinement.Terminating R semₛ semₛ' semₜ →
      StrongRefinement.Aborting R (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₜ' ∪ semₜ ∘ᵣ₁ semᵥ') := by
    rintro ref₁ ref₂ ref₃ σₜ ε σₛ R_σₛ_σₜ (sem|⟨σₜ', ε₁, ε₂, sem₁, sem₂, rfl⟩)
    · refine (ref₁ _ _ _ R_σₛ_σₜ sem).imp λ _ h ↦ h.imp_right ?_
      exact Or.inl
    · obtain ⟨σₛ', R_σₛ'_σₜ', sem₃⟩|⟨ε', ε'_le_ε, sem₃⟩ := ref₃ _ _ _ _ R_σₛ_σₜ sem₁ <;> clear ref₃
      · obtain ⟨ε', ε'_le_ε₂, sem⟩ := ref₂ _ _ _ R_σₛ'_σₜ' sem₂
        exists ε₁ * ε', ?_
        · exact Trace.le_mul_right_inj ε'_le_ε₂
        · right
          use σₛ', ε₁, ε'
      · use ε', ?_, Or.inl sem₃
        exact Trace.le_extend_mul ε'_le_ε

  /-- Horizontal composition. -/
  protected theorem Aborting.Trans {γ} {R₁ R₂}
    {semₛ' : Set (α × τ)} {semₜ' : Set (β × τ)} {semᵤ' : Set (γ × τ)} :
      StrongRefinement.Aborting R₁ semₛ' semₜ' →
      StrongRefinement.Aborting R₂ semₜ' semᵤ' →
      StrongRefinement.Aborting (Relation.Comp R₁ R₂) semₛ' semᵤ' := by
    rintro ref₁ ref₂ σᵤ ε σₛ ⟨σₜ, R₁_σₛ_σₜ, R₂_σₜ_σᵤ⟩ sem_σᵤ
    obtain ⟨ε', ε'_le_ε, sem_σₜ⟩ := ref₂ σᵤ ε σₜ R₂_σₜ_σᵤ sem_σᵤ
    obtain ⟨ε'', ε''_le_ε', sem_σₛ⟩ := ref₁ σₜ ε' σₛ R₁_σₛ_σₜ sem_σₜ
    exists ε'', le_trans ε''_le_ε' ε'_le_ε

  protected theorem Aborting.Mono {R}
    {semᵣ' semₛ' : Set (α × τ)} {semₜ' semᵤ' : Set (β × τ)}
    (hyp : semₛ' ≤ semᵣ') (concl : semᵤ' ≤ semₜ') :
      StrongRefinement.Aborting R semₛ' semₜ' ≤ StrongRefinement.Aborting R semᵣ' semᵤ' := by
    intros ref σᵤ' ε σᵣ' R_σᵣ'_σᵤ' sem_σᵤ'
    obtain ⟨ε', ε'_le_ε, sem_σₛ'⟩ := ref _ _ _ R_σᵣ'_σᵤ' (Set.mem_of_subset_of_mem concl sem_σᵤ')
    use ε', ε'_le_ε, Set.mem_of_subset_of_mem hyp sem_σₛ'

  protected theorem Aborting.Empty {semₛ' : Set (α × τ)} : StrongRefinement.Aborting R semₛ' ∅ := by
    rintro _ _ _ _ (_|_)

  protected theorem Aborting.sup {A : Set (Set (α × τ))} {B}
    (sup : ∀ y ∈ B, ∃ x ∈ A, StrongRefinement.Aborting R x y) :
      StrongRefinement.Aborting R (⋃₀ A) (⋃₀ B) := by
    intros σₜ ε σₛ R_σₛ_σₜ sem_σₜ

    rw [Set.mem_sUnion] at sem_σₜ
    obtain ⟨abortₜ, abortₜ_in_B, abort_σₜ⟩ := sem_σₜ
    obtain ⟨abortₛ, abortₛ_in_A, ref⟩ := sup _ abortₜ_in_B
    obtain ⟨ε', ε'_le_ε, abort_σₛ⟩ := ref σₜ ε σₛ R_σₛ_σₜ abort_σₜ
    exists ε', ε'_le_ε
    exact Set.mem_sUnion_of_mem abort_σₛ abortₛ_in_A

  private theorem Aborting.lfp {f : Set (α × τ) →o _} {g : Set (β × τ) →o _}
    (IH : ∀ x y, StrongRefinement.Aborting R x y → StrongRefinement.Aborting R (f x) (g y)) :
      StrongRefinement.Aborting R (OrderHom.lfp f) (OrderHom.lfp g) := by
    apply OrderHom.lfp_induction₂ (p := λ x y ↦ StrongRefinement.Aborting R x y)
    · intros A B _ A_le_lfp_f B_le_lfp_g
      apply IH
      assumption
    · intros S hSup
      apply Aborting.sup
      intros y y_in
      obtain ⟨x, x_in⟩ := Set.exists_mem_of_mem_image_snd y_in
      use x, ?_, ?_
      2: exact hSup _ x_in
      1: grind only [= Set.mem_image]
end StrongRefinement

/--
  Strong behavior refinement.

  - `semₛ₁` is the reducing semantics for the source language.
  - `semₛ₂` is the aborting semantics for the source language.
  - `semₛ₃` is the diverging semantics for the source language.
  - `semₜ₁` is the reducing semantics for the target language.
  - `semₜ₂` is the aborting semantics for the source language.
  - `semₜ₂` is the diverging semantics for the target language.
 -/
structure StrongRefinement {τ : Type _} [Trace τ] {α β : Type _} (R : Rel α β)
    (semₛ₁ : Set (α × τ × α)) (semₛ₂ semₛ₃ : Set (α × τ))
    (semₜ₁ : Set (β × τ × β)) (semₜ₂ semₜ₃ : Set (β × τ)) where
  terminating : StrongRefinement.Terminating R semₛ₁ semₛ₂ semₜ₁
  aborting : StrongRefinement.Aborting R semₛ₂ semₜ₂
  diverging : StrongRefinement.Diverging R semₛ₃ semₛ₂ semₜ₃


namespace StrongRefinement
  variable {τ : Type _} [Trace τ] {α β : Type _} (R : Rel α β)

  /-- Vertical composition. -/
  protected theorem Comp {semₛ semᵤ : Set (α × τ × α)} {semₛ' semₛ'' semᵤ' semᵤ'' : Set (α × τ)} {semₜ semᵥ : Set (β × τ × β)} {semₜ' semₜ'' semᵥ' semᵥ'' : Set (β × τ)} :
      StrongRefinement R semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' →
      StrongRefinement R semᵤ semᵤ' semᵤ'' semᵥ semᵥ' semᵥ'' →
      StrongRefinement R (semₛ ∘ᵣ₂ semᵤ) (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₛ'' ∪ semₛ ∘ᵣ₁ semᵤ'') (semₜ ∘ᵣ₂ semᵥ) (semₜ' ∪ semₜ ∘ᵣ₁ semᵥ') (semₜ'' ∪ semₜ ∘ᵣ₁ semᵥ'') := by
    rintro ⟨_, _⟩ ⟨_, _⟩
    constructor
    · apply Terminating.Comp <;> assumption
    · apply Aborting.Comp <;> assumption
    · apply Diverging.Comp <;> assumption

  protected theorem ofNonDiverging {semₛ : Set (α × τ × α)} {semₛ' semₛ'' : Set (α × τ)} {semₜ : Set (β × τ × β)} {semₜ' : Set (β × τ)}
    (h₁ : StrongRefinement.Terminating R semₛ semₛ' semₜ) (h₂ : StrongRefinement.Aborting R semₛ' semₜ') :
      StrongRefinement R semₛ semₛ' semₛ'' semₜ semₜ' ∅ := by
    constructor
    · assumption
    · assumption
    · apply Diverging.Empty

  protected theorem ofTerminating {semₛ : Set (α × τ × α)} {semₛ' semₛ'' : Set (α × τ)} {semₜ : Set (β × τ × β)}
    (h : StrongRefinement.Terminating R semₛ semₛ' semₜ) :
      StrongRefinement R semₛ semₛ' semₛ'' semₜ ∅ ∅ := by
    constructor
    · assumption
    · apply Aborting.Empty
    · apply Diverging.Empty

  /-- Horizontal composition. -/
  protected theorem Trans {γ} {R₁ R₂}
    {semₛ : Set (α × τ × α)} {semₛ' semₛ'' : Set (α × τ)}
    {semₜ : Set (β × τ × β)} {semₜ' semₜ'' : Set (β × τ)}
    {semᵤ : Set (γ × τ × γ)} {semᵤ' semᵤ'' : Set (γ × τ)} :
      StrongRefinement R₁ semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' →
      StrongRefinement R₂ semₜ semₜ' semₜ'' semᵤ semᵤ' semᵤ'' →
      StrongRefinement (Relation.Comp R₁ R₂) semₛ semₛ' semₛ'' semᵤ semᵤ' semᵤ'' := by
    rintro ⟨ref₁_red, ref₁_abort, ref₁_div⟩ ⟨ref₂_red, ref₂_abort, ref₂_div⟩
    constructor
    · apply Terminating.Trans <;> assumption
    · apply Aborting.Trans <;> assumption
    · apply Diverging.Trans <;> assumption

  protected theorem Mono {R}
    {semᵣ semₛ : Set (α × τ × α)} {semᵣ' semᵣ'' semₛ' semₛ'' : Set (α × τ)} {semₜ semᵤ : Set (β × τ × β)} {semₜ' semₜ'' semᵤ' semᵤ'' : Set (β × τ)}
    (hyp₁ : semₛ ≤ semᵣ) (hyp₂ : semₛ' ≤ semᵣ') (hyp₃ : semₛ'' ≤ semᵣ'') (concl₁ : semᵤ ≤ semₜ) (concl₂ : semᵤ' ≤ semₜ') (concl₃ : semᵤ'' ≤ semₜ'') :
      StrongRefinement R semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' ≤ StrongRefinement R semᵣ semᵣ' semᵣ'' semᵤ semᵤ' semᵤ'' := by
    rintro ⟨ref₁, ref₂, ref₃⟩
    constructor
    · apply Terminating.Mono hyp₁ hyp₂ concl₁ ref₁
    · apply Aborting.Mono hyp₂ concl₂ ref₂
    · apply Diverging.Mono hyp₃ hyp₂ concl₃ ref₃

  protected theorem FixedPoint {f : Set (α × τ × α) →o _} {f' f'' : Set (α × τ) →o _} {g : Set (β × τ × β) →o _} {g' g''}
    (IH₁ : ∀ x x' y, StrongRefinement.Terminating R x x' y → StrongRefinement.Terminating R (f x) (f' x') (g y))
    (IH₂ : ∀ x' y', StrongRefinement.Aborting R x' y' → StrongRefinement.Aborting R (f' x') (g' y'))
    (IH₃ : ∀ x'' x' y'', StrongRefinement.Diverging R x'' x' y'' → StrongRefinement.Diverging R (f'' x'') (f' x') (g'' y'')) :
      StrongRefinement R (OrderHom.lfp f) (OrderHom.lfp f') (OrderHom.gfp f'') (OrderHom.lfp g) (OrderHom.lfp g') (OrderHom.gfp g'') := by
    constructor
    · exact Terminating.lfp _ IH₁
    · exact Aborting.lfp _ IH₂
    · exact Diverging.gfp _ IH₃
end StrongRefinement
