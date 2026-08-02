module

public import VerifiedCompiler.Trace
public import Mathlib.Data.Rel
public import Extra.Rel
public import Extra.Set
meta import CustomPrelude

public section

namespace StrongRefinement
  variable {εₛ εₜ : Type _} [Monoid εₛ] [Monoid εₜ] {α β : Type _} (R S : Rel α β) (Rτ : Rel εₛ εₜ)

  /--
    Behavior refinement in the terminating case.

    - `semₛ` is the reducing semantics for the source language.
    - `semₛ'` is the aborting semantics for the source language.
    - `semₜ` is the reducing semantics for the target language.

    The source's trace is existentially quantified and related to the target's by `Rτ`, rather than
    shared outright: a pass need not preserve a trace exactly, only up to `Rτ` (`0b`,
    `VerifiedCompiler/Trace.lean`). The aborting disjunct's `≼[Rτ]` is the same relaxation applied to
    *prefix*: not a syntactic prefix of the target's trace, but a sequentially consistent one.
  -/
  @[expose]
  protected def Terminating (semₛ : Set (α × εₛ × α)) (semₛ' : Set (α × εₛ)) (semₜ : Set (β × εₜ × β)) : Prop :=
    ∀ (σₜ σₜ' : β) (ε : εₜ) (σₛ : α), R σₛ σₜ → (σₜ, ε, σₜ') ∈ semₜ →
      (∃ (σₛ' : α) (ε' : εₛ), S σₛ' σₜ' ∧ Rτ ε' ε ∧ (σₛ, ε', σₛ') ∈ semₛ) ∨
      (∃ ε' : εₛ, ε' ≼[Rτ] ε ∧ (σₛ, ε') ∈ semₛ')

  /-- Vertical composition. `T₂` bundles the second factor's trace relation with its left-totality
  law — needed for the branch where the source aborts inside the *first* factor, so the target's
  full trace (which ran both) still has to be matchable. -/
  protected theorem Terminating.Comp {R S T : Rel α β} {Rτ₁ : Rel εₛ εₜ} [T₂ : Trace εₛ εₜ]
      {semₛ semᵤ : Set (α × εₛ × α)} {semₛ' semᵤ' : Set (α × εₛ)} {semₜ semᵥ : Set (β × εₜ × β)} :
      StrongRefinement.Terminating R S Rτ₁ semₛ semₛ' semₜ → StrongRefinement.Terminating S T T₂.Rτ semᵤ semᵤ' semᵥ →
      StrongRefinement.Terminating R T (Rτ₁ ⊗ᵣ T₂.Rτ) (semₛ ∘ᵣ₂ semᵤ) (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₜ ∘ᵣ₂ semᵥ) := by
    rintro ref_semₜ ref_semᵥ σₜ σᵥ'' ε σₛ σₛRσₜ ⟨σᵥ', ε₁, ε₂, red_σₜ_σᵥ', red_σᵥ'_σᵥ'', rfl⟩
    obtain ⟨σₛ', εₛ₁, σₛ'Rσᵥ', Rτ_εₛ₁_ε₁, sem_εₛ₁⟩|⟨εₛ₁, εₛ₁_scp_ε₁, semₛ'_εₛ₁⟩ :=
      ref_semₜ _ _ _ _ σₛRσₜ red_σₜ_σᵥ'
    · obtain ⟨σᵤ, εₛ₂, σᵤRσᵥ'', Rτ_εₛ₂_ε₂, sem_εₛ₂⟩|⟨εₛ₂, εₛ₂_scp_ε₂, semᵤ'_εₛ₂⟩ :=
        ref_semᵥ _ _ _ _ σₛ'Rσᵥ' red_σᵥ'_σᵥ''
      · left
        exists σᵤ, εₛ₁ * εₛ₂
        refine ⟨σᵤRσᵥ'', ⟨εₛ₁, εₛ₂, ε₁, ε₂, rfl, rfl, Rτ_εₛ₁_ε₁, Rτ_εₛ₂_ε₂⟩, ?_⟩
        exists σₛ', εₛ₁, εₛ₂
      · right
        exists εₛ₁ * εₛ₂
        refine ⟨Trace.scPrefix_rmul_right Rτ_εₛ₁_ε₁ εₛ₂_scp_ε₂, Or.inr ?_⟩
        exists σₛ', εₛ₁, εₛ₂
    · right
      exists εₛ₁
      exact ⟨Trace.scPrefix_rmul_left T₂.Rτ_total εₛ₁_scp_ε₁, Or.inl semₛ'_εₛ₁⟩

  omit [Monoid εₜ] in
  /-- Monotone in both the state sets and the trace relation: `Rτ` occurs only positively in
  `Terminating`'s conclusion, so widening it to a superset only weakens the statement, same as
  widening the semantics sets. Both axes are needed together where a vertical composition's
  natural relation (`Rτ₁ ⊗ᵣ Rτ₂` for `Terminating`) has to be widened to match the union
  `Aborting`/`Diverging`'s composition actually produces (`StrongRefinement.Comp`) — there the set
  hypotheses are trivial (`le_rfl`) and only the `Rτ` one does anything. -/
  protected theorem Terminating.Mono {R S : Rel α β} {Rτ Rτ' : Rel εₛ εₜ}
    {semᵣ semₛ : Set (α × εₛ × α)} {semᵣ' semₛ' : Set (α × εₛ)} {semₜ semᵤ : Set (β × εₜ × β)}
    (hyp₁ : semₛ ≤ semᵣ) (hyp₂ : semₛ' ≤ semᵣ') (hyp₃ : ∀ x y, Rτ x y → Rτ' x y) (concl : semᵤ ≤ semₜ) :
      StrongRefinement.Terminating R S Rτ semₛ semₛ' semₜ ≤ StrongRefinement.Terminating R S Rτ' semᵣ semᵣ' semᵤ := by
    intros ref σᵤ σᵤ' ε σᵣ' R_σᵣ'_σᵤ' sem_σᵤ'
    obtain ⟨σₛ', ε', R_σₛ'_σᵤ', Rτ_ε'_ε, sem_σₛ'⟩|⟨ε', ε'_scp_ε, sem_σₛ'⟩ :=
      ref _ _ ε _ R_σᵣ'_σᵤ' (Set.mem_of_subset_of_mem concl sem_σᵤ')
    · left
      exact ⟨σₛ', ε', R_σₛ'_σᵤ', hyp₃ _ _ Rτ_ε'_ε, Set.mem_of_subset_of_mem hyp₁ sem_σₛ'⟩
    · right
      exact ⟨ε', Trace.scPrefix_mono hyp₃ ε'_scp_ε, Set.mem_of_subset_of_mem hyp₂ sem_σₛ'⟩

  protected theorem Terminating.Id {X} :
      StrongRefinement.Terminating R R (Eq (α := εₛ)) {(x, ε, y) : α × εₛ × α | x = y ∧ ε = Trace.τ} X
        {(x, ε, y) | x = y ∧ ε = Trace.τ} := by
    rintro σₜ σₜ' ε σₛ σₛRσₜ ⟨rfl, rfl⟩
    left
    exact ⟨σₛ, Trace.τ, σₛRσₜ, rfl, rfl, rfl⟩

  omit [Monoid εₜ] in
  protected theorem Terminating.sup {R S : Rel α β} {Rτ : Rel εₛ εₜ} {A : Set (Set (α × εₛ × α))}
    {B : Set (Set (β × εₜ × β))} {C : Set (Set (α × εₛ))}
    (sup : ∀ y ∈ B, ∃ x ∈ A, ∃ z ∈ C, StrongRefinement.Terminating R S Rτ x z y) :
      StrongRefinement.Terminating R S Rτ (⋃₀ A) (⋃₀ C) (⋃₀ B) := by
    rintro σₜ σₜ' ε σₛ R_σₛ_σₜ sem_σₜ_σₜ'

    rw [Set.mem_sUnion] at sem_σₜ_σₜ'
    obtain ⟨semₜ, semₜ_in_B, sem_σₜ_σₜ'⟩ := sem_σₜ_σₜ'
    obtain ⟨semₛ, semₛ_in_A, abortₛ, abortₛ_in_C, ref⟩ := sup semₜ semₜ_in_B
    obtain ⟨σₛ', ε', R_σₛ'_σₜ', Rτ_ε'_ε, sem_σₛ_σₛ'⟩|⟨ε', ε'_scp_ε, abortₛ_σₛ⟩ := ref _ _ _ _ R_σₛ_σₜ sem_σₜ_σₜ'
    · left
      exists σₛ', ε', R_σₛ'_σₜ', Rτ_ε'_ε
      exact Set.mem_sUnion_of_mem sem_σₛ_σₛ' semₛ_in_A
    · right
      exists ε', ε'_scp_ε
      exact Set.mem_sUnion_of_mem abortₛ_σₛ abortₛ_in_C

  omit [Monoid εₜ] in
  protected theorem Terminating.lfp {f : Set (α × εₛ × α) →o _} {g : Set (β × εₜ × β) →o _} {h : Set (α × εₛ) →o _}
    (IH : ∀ x y z, StrongRefinement.Terminating R R Rτ x y z → StrongRefinement.Terminating R R Rτ (f x) (h y) (g z)) :
      StrongRefinement.Terminating R R Rτ (OrderHom.lfp f) (OrderHom.lfp h) (OrderHom.lfp g) := by
    apply OrderHom.lfp_induction₃ (p := λ x y z ↦ StrongRefinement.Terminating R R Rτ x y z)
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
  @[expose]
  protected def Diverging (semₛ semₛ' : Set (α × εₛ)) (semₜ : Set (β × εₜ)) : Prop :=
    ∀ (σₜ : β) (ε : εₜ) (σₛ : α), R σₛ σₜ → (σₜ, ε) ∈ semₜ →
      (∃ ε' : εₛ, Rτ ε' ε ∧ (σₛ, ε') ∈ semₛ) ∨ (∃ ε' : εₛ, ε' ≼[Rτ] ε ∧ (σₛ, ε') ∈ semₛ')

  /-- Vertical composition. Concludes about `Rτ₁ ⊔ (Rτ₁ ⊗ᵣ T₂.Rτ)`, not just `Rτ₁ ⊗ᵣ T₂.Rτ`: the
  first branch below is a divergence that never reaches the second factor at all, so its
  `Rτ₁`-relatedness has to survive as-is (via `Or.inl`) rather than being forced through a
  repackaging that would need `T₂.Rτ` to relate the empty trace to itself. Only the sequenced
  branch (`Or.inr`) needs `T₂`'s left-totality, same reason as `Terminating.Comp`. -/
  protected theorem Diverging.Comp {R} {Rτ₁ : Rel εₛ εₜ} [T₂ : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {semₛ' semₛ'' semᵤ' semᵤ'' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)} {semₜ'' semᵥ'' : Set (β × εₜ)} :
      StrongRefinement.Diverging R Rτ₁ semₛ'' semₛ' semₜ'' →
      StrongRefinement.Diverging R T₂.Rτ semᵤ'' semᵤ' semᵥ'' →
      StrongRefinement.Terminating R R Rτ₁ semₛ semₛ' semₜ →
      StrongRefinement.Diverging R (Rτ₁ ⊔ Rτ₁ ⊗ᵣ T₂.Rτ) (semₛ'' ∪ semₛ ∘ᵣ₁ semᵤ'') (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₜ'' ∪ semₜ ∘ᵣ₁ semᵥ'') := by
    rintro ref₁ ref₂ ref₃ σₜ ε σₛ R_σₛ_σₜ (semₜ''_σₜ|⟨σₜ', ε₁, ε₂, semₜ_σₜ_σₜ', semᵥ''_σₜ', rfl⟩)
    · obtain ⟨εₛ₁, Rτ_εₛ₁_ε, semₛ''_εₛ₁⟩|⟨εₛ₁, εₛ₁_scp_ε, semₛ'_εₛ₁⟩ := ref₁ _ _ _ R_σₛ_σₜ semₜ''_σₜ
      · left
        exact ⟨εₛ₁, Or.inl Rτ_εₛ₁_ε, Or.inl semₛ''_εₛ₁⟩
      · right
        exists εₛ₁
        exact ⟨Trace.scPrefix_mono (λ _ _ ↦ Or.inl) εₛ₁_scp_ε, Or.inl semₛ'_εₛ₁⟩
    · obtain ⟨σₛ', εₛ₁, R_σₛ'_σₜ', Rτ_εₛ₁_ε₁, sem_εₛ₁⟩|⟨εₛ₁, εₛ₁_scp_ε₁, semₛ'_εₛ₁⟩ :=
        ref₃ _ _ _ _ R_σₛ_σₜ semₜ_σₜ_σₜ'
      · obtain ⟨εₛ₂, Rτ_εₛ₂_ε₂, semᵤ''_εₛ₂⟩|⟨εₛ₂, εₛ₂_scp_ε₂, semᵤ'_εₛ₂⟩ := ref₂ _ _ _ R_σₛ'_σₜ' semᵥ''_σₜ'
        · left
          refine ⟨εₛ₁ * εₛ₂, Or.inr ⟨εₛ₁, εₛ₂, ε₁, ε₂, rfl, rfl, Rτ_εₛ₁_ε₁, Rτ_εₛ₂_ε₂⟩, Or.inr ?_⟩
          exists σₛ', εₛ₁, εₛ₂
        · right
          exists εₛ₁ * εₛ₂
          refine ⟨Trace.scPrefix_mono (λ _ _ ↦ Or.inr) (Trace.scPrefix_rmul_right Rτ_εₛ₁_ε₁ εₛ₂_scp_ε₂), Or.inr ?_⟩
          exists σₛ', εₛ₁, εₛ₂
      · right
        exists εₛ₁
        refine ⟨Trace.scPrefix_mono (λ _ _ ↦ Or.inr) (Trace.scPrefix_rmul_left T₂.Rτ_total εₛ₁_scp_ε₁), Or.inl semₛ'_εₛ₁⟩

  omit [Monoid εₜ] in
  protected theorem Diverging.Mono {R} {Rτ : Rel εₛ εₜ}
    {semᵣ'' semᵣ' semₛ'' semₛ' : Set (α × εₛ)} {semₜ'' semᵤ'' : Set (β × εₜ)}
    (hyp₁ : semₛ'' ≤ semᵣ'') (hyp₂ : semₛ' ≤ semᵣ') (concl : semᵤ'' ≤ semₜ'') :
      StrongRefinement.Diverging R Rτ semₛ'' semₛ' semₜ'' ≤ StrongRefinement.Diverging R Rτ semᵣ'' semᵣ' semᵤ'' := by
    intros ref σᵤ' ε σᵣ' R_σᵣ'_σᵤ' sem_σᵤ''
    obtain ⟨ε', Rτ_ε'_ε, sem_σₛ''⟩|⟨ε', ε'_scp_ε, sem_σₛ'⟩ :=
      ref _ ε _ R_σᵣ'_σᵤ' (Set.mem_of_subset_of_mem concl sem_σᵤ'')
    · left
      exact ⟨ε', Rτ_ε'_ε, Set.mem_of_subset_of_mem hyp₁ sem_σₛ''⟩
    · right
      exact ⟨ε', ε'_scp_ε, Set.mem_of_subset_of_mem hyp₂ sem_σₛ'⟩

  omit [Monoid εₜ] in
  protected theorem Diverging.Empty {Rτ : Rel εₛ εₜ} {semₛ'' semₛ' : Set (α × εₛ)} :
      StrongRefinement.Diverging R Rτ semₛ'' semₛ' ∅ := by
    rintro _ _ _ _ (_|_)


  omit [Monoid εₜ] in
  /-- Combines a family of `Diverging` facts via intersection on the state components. Unlike
  `Aborting.sup`'s union, intersection can't just pick one family member: proving "still diverging"
  needs a witness that works for *every* member at once, and each member only guarantees its own,
  independently-chosen one. Two extra hypotheses close that gap:

  - `Rτ_total`, for the degenerate `A = ∅` case (`⋂₀ ∅` is vacuous, but a witness must still exist)
    — already one of `Trace`'s two laws, not a new obligation.
  - `sat`, genuinely new: every set standing in the `Diverging` relation is closed under swapping
    between `Rτ`-equivalent witnesses for the same target trace. This is the confluence fact
    `PLAN.md`'s D8 needs anyway — independent steps of `Algebra.step` commute — surfaced here as an
    explicit obligation rather than proved inline, since discharging it is D8's job, not this
    lemma's.

  Neither hypothesis is needed when some family member aborts: that member's abort alone settles
  the conclusion via `⋃₀ C`, exactly as in `Aborting.sup`. They're needed only when every member is
  still diverging, to reconcile their independently-chosen witnesses into one. -/
  protected theorem Diverging.inf {R : Rel α β} {Rτ : Rel εₛ εₜ} (Rτ_total : Relation.LeftTotal Rτ)
    (sat : ∀ X Z Y, StrongRefinement.Diverging R Rτ X Z Y →
      ∀ σₛ ε ε₁ ε₂, Rτ ε₁ ε → Rτ ε₂ ε → (σₛ, ε₁) ∈ X → (σₛ, ε₂) ∈ X)
    {A : Set (Set (α × εₛ))} {B} {C}
    (sup : ∀ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, StrongRefinement.Diverging R Rτ x z y) :
      StrongRefinement.Diverging R Rτ (⋂₀ A) (⋃₀ C) (⋂₀ B) := by
    rintro σₜ ε σₛ R_σₛ_σₜ sem_σₜ_σₜ'
    rw [Set.mem_sInter] at sem_σₜ_σₜ'
    by_cases hQ : ∃ ε', ε' ≼[Rτ] ε ∧ (σₛ, ε') ∈ ⋃₀ C
    · right
      exact hQ
    · left
      by_cases hA : A.Nonempty
      · obtain ⟨t₀, t₀_in_A⟩ := hA
        obtain ⟨y₀, y₀_in_B, z₀, z₀_in_C, ref₀⟩ := sup t₀ t₀_in_A
        obtain ⟨ε'₀, Rτ_ε'₀_ε, mem₀⟩|⟨ε'₀, ε'₀_scp_ε, abort_mem⟩ :=
          ref₀ σₜ ε σₛ R_σₛ_σₜ (sem_σₜ_σₜ' _ y₀_in_B)
        · refine ⟨ε'₀, Rτ_ε'₀_ε, ?_⟩
          rw [Set.mem_sInter]
          intro t t_in_A
          obtain ⟨y, y_in_B, z, z_in_C, ref⟩ := sup t t_in_A
          obtain ⟨ε', Rτ_ε'_ε, mem'⟩|⟨ε', ε'_scp_ε, abort_mem⟩ :=
            ref σₜ ε σₛ R_σₛ_σₜ (sem_σₜ_σₜ' _ y_in_B)
          · exact sat t z y ref σₛ ε ε' ε'₀ Rτ_ε'_ε Rτ_ε'₀_ε mem'
          · exact absurd ⟨ε', ε'_scp_ε, Set.mem_sUnion_of_mem abort_mem z_in_C⟩ hQ
        · exact absurd ⟨ε'₀, ε'₀_scp_ε, Set.mem_sUnion_of_mem abort_mem z₀_in_C⟩ hQ
      · obtain ⟨ε'₀, Rτ_ε'₀_ε⟩ := Rτ_total ε
        refine ⟨ε'₀, Rτ_ε'₀_ε, ?_⟩
        rw [Set.mem_sInter]
        intro t t_in_A
        exact absurd ⟨t, t_in_A⟩ hA

  omit [Monoid εₜ] in
  protected theorem Diverging.gfp {Rτ : Rel εₛ εₜ} (Rτ_total : Relation.LeftTotal Rτ)
    (sat : ∀ X Z Y, StrongRefinement.Diverging R Rτ X Z Y →
      ∀ σₛ ε ε₁ ε₂, Rτ ε₁ ε → Rτ ε₂ ε → (σₛ, ε₁) ∈ X → (σₛ, ε₂) ∈ X)
    {f : Set (α × εₛ) →o _} {g : Set (β × εₜ) →o _} {h : Set (α × εₛ) →o _}
    (IH : ∀ x y z, StrongRefinement.Diverging R Rτ x y z → StrongRefinement.Diverging R Rτ (f x) (h y) (g z)) :
      StrongRefinement.Diverging R Rτ (OrderHom.gfp f) (OrderHom.lfp h) (OrderHom.gfp g) := by
    apply OrderHom.lfp_induction₃ f.dual h g.dual
    · intros A B C ref_A_B_C A_le_lfp B_le_lfp C_le_lfp
      apply IH
      assumption
    · intros S hSup
      apply Diverging.inf Rτ_total sat

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
    - `semₜ'` is the aborting semantics for the target language.
  -/
  @[expose]
  protected def Aborting (semₛ' : Set (α × εₛ)) (semₜ' : Set (β × εₜ)) : Prop :=
    ∀ (σₜ : β) (ε : εₜ) (σₛ : α), R σₛ σₜ → (σₜ, ε) ∈ semₜ' → ∃ ε' : εₛ, ε' ≼[Rτ] ε ∧ (σₛ, ε') ∈ semₛ'

  omit [Monoid εₜ] in
  /-- Horizontal composition, through an intermediate language with trace type `εₘ`. Needs `Rτ₁`
  (the first leg) both left-total and closed — bundled as `T₁ : Trace εₛ εₘ` — per
  `Trace.scPrefix_rcomp`. The second leg's `Rτ₂` needs nothing. -/
  protected theorem Terminating.Trans {γ} {εₘ : Type _} [Monoid εₘ] {R₁ S₁ : Rel α β} {R₂ S₂ : Rel β γ}
    [T₁ : Trace εₛ εₘ] {Rτ₂ : Rel εₘ εₜ}
    {semₛ : Set (α × εₛ × α)} {semₛ' : Set (α × εₛ)}
    {semₜ : Set (β × εₘ × β)} {semₜ' : Set (β × εₘ)}
    {semᵤ : Set (γ × εₜ × γ)} :
      StrongRefinement.Terminating R₁ S₁ T₁.Rτ semₛ semₛ' semₜ →
      StrongRefinement.Aborting R₁ T₁.Rτ semₛ' semₜ' →
      StrongRefinement.Terminating R₂ S₂ Rτ₂ semₜ semₜ' semᵤ →
      StrongRefinement.Terminating (Relation.Comp R₁ R₂) (Relation.Comp S₁ S₂) (T₁.Rτ ∘ᵣ Rτ₂) semₛ semₛ' semᵤ := by
    rintro ref₁ ref₃ ref₂ σᵤ σᵤ' ε σₛ ⟨σₜ, R₁_σₛ_σₜ, R₂_σₜ_σᵤ⟩ semᵤ_σᵤ_σᵤ'
    obtain ⟨σₜ', εₘ', S₂_σₜ'_σᵤ', Rτ₂_εₘ'_ε, semₜ_σₜ_σₜ'⟩|⟨εₘ', εₘ'_scp_ε, semₜ'_σₜ⟩ :=
      ref₂ _ _ _ _ R₂_σₜ_σᵤ semᵤ_σᵤ_σᵤ'
    · obtain ⟨σₛ', εₛ', S₁_σₛ'_σₜ', Rτ₁_εₛ'_εₘ', semₛ_σₛ_σₛ'⟩|⟨εₛ', εₛ'_scp_εₘ', semₛ'_σₛ⟩ :=
        ref₁ _ _ _ _ R₁_σₛ_σₜ semₜ_σₜ_σₜ'
      · left
        exact ⟨σₛ', εₛ', ⟨σₜ', S₁_σₛ'_σₜ', S₂_σₜ'_σᵤ'⟩, ⟨εₘ', Rτ₁_εₛ'_εₘ', Rτ₂_εₘ'_ε⟩, semₛ_σₛ_σₛ'⟩
      · right
        exact ⟨εₛ', Trace.scPrefix_rcomp T₁.Rτ_total T₁.Rτ_closed εₛ'_scp_εₘ' (Trace.scPrefix_of Rτ₂_εₘ'_ε), semₛ'_σₛ⟩
    · obtain ⟨εₛ', εₛ'_scp_εₘ', semₛ'_σₛ⟩ := ref₃ σₜ εₘ' σₛ R₁_σₛ_σₜ semₜ'_σₜ
      right
      exact ⟨εₛ', Trace.scPrefix_rcomp T₁.Rτ_total T₁.Rτ_closed εₛ'_scp_εₘ' εₘ'_scp_ε, semₛ'_σₛ⟩

  omit [Monoid εₜ] in
  /-- Horizontal composition. Same `scPrefix_rcomp` shape as `Terminating.Trans`: only the first
  leg's `Rτ₁` (bundled as `T₁`) needs laws. -/
  protected theorem Diverging.Trans {γ} {εₘ : Type _} [Monoid εₘ] {R₁ R₂} [T₁ : Trace εₛ εₘ] {Rτ₂ : Rel εₘ εₜ}
    {semₛ'' semₛ' : Set (α × εₛ)} {semₜ'' semₜ' : Set (β × εₘ)} {semᵤ'' : Set (γ × εₜ)} :
      StrongRefinement.Diverging R₁ T₁.Rτ semₛ'' semₛ' semₜ'' →
      StrongRefinement.Aborting R₁ T₁.Rτ semₛ' semₜ' →
      StrongRefinement.Diverging R₂ Rτ₂ semₜ'' semₜ' semᵤ'' →
      StrongRefinement.Diverging (Relation.Comp R₁ R₂) (T₁.Rτ ∘ᵣ Rτ₂) semₛ'' semₛ' semᵤ'' := by
    rintro ref₁ ref₃ ref₂ σᵤ ε σₛ ⟨σₜ, R₁_σₛ_σₜ, R₂_σₜ_σᵤ⟩ semᵤ''_σᵤ
    obtain ⟨εₘ', Rτ₂_εₘ'_ε, semₜ''_σₜ⟩|⟨εₘ', εₘ'_scp_ε, semₜ'_σₜ⟩ := ref₂ _ ε _ R₂_σₜ_σᵤ semᵤ''_σᵤ
    · obtain ⟨εₛ', Rτ₁_εₛ'_εₘ', semₛ''_σₛ⟩|⟨εₛ', εₛ'_scp_εₘ', semₛ'_σₛ⟩ := ref₁ _ εₘ' _ R₁_σₛ_σₜ semₜ''_σₜ
      · left
        exact ⟨εₛ', ⟨εₘ', Rτ₁_εₛ'_εₘ', Rτ₂_εₘ'_ε⟩, semₛ''_σₛ⟩
      · right
        exact ⟨εₛ', Trace.scPrefix_rcomp T₁.Rτ_total T₁.Rτ_closed εₛ'_scp_εₘ' (Trace.scPrefix_of Rτ₂_εₘ'_ε), semₛ'_σₛ⟩
    · obtain ⟨εₛ', εₛ'_scp_εₘ', semₛ'_σₛ⟩ := ref₃ _ εₘ' _ R₁_σₛ_σₜ semₜ'_σₜ
      right
      exact ⟨εₛ', Trace.scPrefix_rcomp T₁.Rτ_total T₁.Rτ_closed εₛ'_scp_εₘ' εₘ'_scp_ε, semₛ'_σₛ⟩

  /-- Vertical composition. Same union shape as `Diverging.Comp`, for the same reason: the first
  branch (abort directly in the first factor) never reaches the second, so `Rτ₁`'s relatedness
  survives as-is instead of being forced through `⊗ᵣ`. -/
  protected theorem Aborting.Comp {R} {Rτ₁ : Rel εₛ εₜ} [T₂ : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {semₛ' semᵤ' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)} {semₜ' semᵥ' : Set (β × εₜ)} :
      StrongRefinement.Aborting R Rτ₁ semₛ' semₜ' →
      StrongRefinement.Aborting R T₂.Rτ semᵤ' semᵥ' →
      StrongRefinement.Terminating R R Rτ₁ semₛ semₛ' semₜ →
      StrongRefinement.Aborting R (Rτ₁ ⊔ Rτ₁ ⊗ᵣ T₂.Rτ) (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₜ' ∪ semₜ ∘ᵣ₁ semᵥ') := by
    rintro ref₁ ref₂ ref₃ σₜ ε σₛ R_σₛ_σₜ (sem|⟨σₜ', ε₁, ε₂, sem₁, sem₂, rfl⟩)
    · obtain ⟨ε', ε'_scp_ε, sem'⟩ := ref₁ _ _ _ R_σₛ_σₜ sem
      exact ⟨ε', Trace.scPrefix_mono (λ _ _ ↦ Or.inl) ε'_scp_ε, Or.inl sem'⟩
    · obtain ⟨σₛ', εₛ₁, R_σₛ'_σₜ', Rτ_εₛ₁_ε₁, sem₃⟩|⟨εₛ₁, εₛ₁_scp_ε₁, semₛ'_εₛ₁⟩ :=
        ref₃ _ _ _ _ R_σₛ_σₜ sem₁
      · obtain ⟨εₛ₂, εₛ₂_scp_ε₂, sem_εₛ₂⟩ := ref₂ _ _ _ R_σₛ'_σₜ' sem₂
        refine ⟨εₛ₁ * εₛ₂, Trace.scPrefix_mono (λ _ _ ↦ Or.inr) (Trace.scPrefix_rmul_right Rτ_εₛ₁_ε₁ εₛ₂_scp_ε₂), Or.inr ?_⟩
        exists σₛ', εₛ₁, εₛ₂
      · exact ⟨εₛ₁, Trace.scPrefix_mono (λ _ _ ↦ Or.inr) (Trace.scPrefix_rmul_left T₂.Rτ_total εₛ₁_scp_ε₁), Or.inl semₛ'_εₛ₁⟩

  omit [Monoid εₜ] in
  /-- Horizontal composition. Same `scPrefix_rcomp` shape as `Terminating.Trans`. -/
  protected theorem Aborting.Trans {γ} {εₘ : Type _} [Monoid εₘ] {R₁ R₂} [T₁ : Trace εₛ εₘ] {Rτ₂ : Rel εₘ εₜ}
    {semₛ' : Set (α × εₛ)} {semₜ' : Set (β × εₘ)} {semᵤ' : Set (γ × εₜ)} :
      StrongRefinement.Aborting R₁ T₁.Rτ semₛ' semₜ' →
      StrongRefinement.Aborting R₂ Rτ₂ semₜ' semᵤ' →
      StrongRefinement.Aborting (Relation.Comp R₁ R₂) (T₁.Rτ ∘ᵣ Rτ₂) semₛ' semᵤ' := by
    rintro ref₁ ref₂ σᵤ ε σₛ ⟨σₜ, R₁_σₛ_σₜ, R₂_σₜ_σᵤ⟩ sem_σᵤ
    obtain ⟨εₘ', εₘ'_scp_ε, sem_σₜ⟩ := ref₂ σᵤ ε σₜ R₂_σₜ_σᵤ sem_σᵤ
    obtain ⟨εₛ', εₛ'_scp_εₘ', sem_σₛ⟩ := ref₁ σₜ εₘ' σₛ R₁_σₛ_σₜ sem_σₜ
    exact ⟨εₛ', Trace.scPrefix_rcomp T₁.Rτ_total T₁.Rτ_closed εₛ'_scp_εₘ' εₘ'_scp_ε, sem_σₛ⟩

  omit [Monoid εₜ] in
  protected theorem Aborting.Mono {R} {Rτ : Rel εₛ εₜ}
    {semᵣ' semₛ' : Set (α × εₛ)} {semₜ' semᵤ' : Set (β × εₜ)}
    (hyp : semₛ' ≤ semᵣ') (concl : semᵤ' ≤ semₜ') :
      StrongRefinement.Aborting R Rτ semₛ' semₜ' ≤ StrongRefinement.Aborting R Rτ semᵣ' semᵤ' := by
    intros ref σᵤ' ε σᵣ' R_σᵣ'_σᵤ' sem_σᵤ'
    obtain ⟨ε', ε'_scp_ε, sem_σₛ'⟩ := ref _ _ _ R_σᵣ'_σᵤ' (Set.mem_of_subset_of_mem concl sem_σᵤ')
    exact ⟨ε', ε'_scp_ε, Set.mem_of_subset_of_mem hyp sem_σₛ'⟩

  omit [Monoid εₜ] in
  protected theorem Aborting.Empty {Rτ : Rel εₛ εₜ} {semₛ' : Set (α × εₛ)} :
      StrongRefinement.Aborting R Rτ semₛ' ∅ := by
    rintro _ _ _ _ (_|_)

  omit [Monoid εₜ] in
  protected theorem Aborting.sup {Rτ : Rel εₛ εₜ} {A : Set (Set (α × εₛ))} {B}
    (sup : ∀ y ∈ B, ∃ x ∈ A, StrongRefinement.Aborting R Rτ x y) :
      StrongRefinement.Aborting R Rτ (⋃₀ A) (⋃₀ B) := by
    intros σₜ ε σₛ R_σₛ_σₜ sem_σₜ

    rw [Set.mem_sUnion] at sem_σₜ
    obtain ⟨abortₜ, abortₜ_in_B, abort_σₜ⟩ := sem_σₜ
    obtain ⟨abortₛ, abortₛ_in_A, ref⟩ := sup _ abortₜ_in_B
    obtain ⟨ε', ε'_scp_ε, abort_σₛ⟩ := ref σₜ ε σₛ R_σₛ_σₜ abort_σₜ
    exists ε', ε'_scp_ε
    exact Set.mem_sUnion_of_mem abort_σₛ abortₛ_in_A

  omit [Monoid εₜ] in
  private theorem Aborting.lfp {Rτ : Rel εₛ εₜ} {f : Set (α × εₛ) →o _} {g : Set (β × εₜ) →o _}
    (IH : ∀ x y, StrongRefinement.Aborting R Rτ x y → StrongRefinement.Aborting R Rτ (f x) (g y)) :
      StrongRefinement.Aborting R Rτ (OrderHom.lfp f) (OrderHom.lfp g) := by
    apply OrderHom.lfp_induction₂ (p := λ x y ↦ StrongRefinement.Aborting R Rτ x y)
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
  - `semₜ₂` is the aborting semantics for the target language.
  - `semₜ₃` is the diverging semantics for the target language.
 -/
structure StrongRefinement {εₛ εₜ : Type _} [Monoid εₛ] [Monoid εₜ] {α β : Type _} (R : Rel α β)
    (Rτ : Rel εₛ εₜ)
    (semₛ₁ : Set (α × εₛ × α)) (semₛ₂ semₛ₃ : Set (α × εₛ))
    (semₜ₁ : Set (β × εₜ × β)) (semₜ₂ semₜ₃ : Set (β × εₜ)) where
  terminating : StrongRefinement.Terminating R R Rτ semₛ₁ semₛ₂ semₜ₁
  aborting : StrongRefinement.Aborting R Rτ semₛ₂ semₜ₂
  diverging : StrongRefinement.Diverging R Rτ semₛ₃ semₛ₂ semₜ₃


namespace StrongRefinement
  variable {εₛ εₜ : Type _} [Monoid εₛ] [Monoid εₜ] {α β : Type _} (R S : Rel α β)

  /-- Vertical composition. `T₂` bundles the second operand's trace relation with its
  left-totality law. `Terminating`'s natural result `Rτ₁ ⊗ᵣ T₂.Rτ` gets widened via
  `Terminating.Rτ_mono` to match the union `Aborting`/`Diverging` produce — see their doc
  comments for why the union is unavoidable there. -/
  protected theorem Comp [T₂ : Trace εₛ εₜ] {Rτ₁ : Rel εₛ εₜ}
    {semₛ semᵤ : Set (α × εₛ × α)} {semₛ' semₛ'' semᵤ' semᵤ'' : Set (α × εₛ)} {semₜ semᵥ : Set (β × εₜ × β)} {semₜ' semₜ'' semᵥ' semᵥ'' : Set (β × εₜ)} :
      StrongRefinement R Rτ₁ semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' →
      StrongRefinement R T₂.Rτ semᵤ semᵤ' semᵤ'' semᵥ semᵥ' semᵥ'' →
      StrongRefinement R (Rτ₁ ⊔ Rτ₁ ⊗ᵣ T₂.Rτ) (semₛ ∘ᵣ₂ semᵤ) (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₛ'' ∪ semₛ ∘ᵣ₁ semᵤ'') (semₜ ∘ᵣ₂ semᵥ) (semₜ' ∪ semₜ ∘ᵣ₁ semᵥ') (semₜ'' ∪ semₜ ∘ᵣ₁ semᵥ'') := by
    rintro ⟨t₁, a₁, d₁⟩ ⟨t₂, a₂, d₂⟩
    exact ⟨Terminating.Mono le_rfl le_rfl (λ _ _ ↦ Or.inr) le_rfl (Terminating.Comp t₁ t₂), Aborting.Comp a₁ a₂ t₁,
      Diverging.Comp d₁ d₂ t₁⟩

  protected theorem ofNonDiverging {Rτ : Rel εₛ εₜ} {semₛ : Set (α × εₛ × α)} {semₛ' semₛ'' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)} {semₜ' : Set (β × εₜ)}
    (h₁ : StrongRefinement.Terminating R R Rτ semₛ semₛ' semₜ) (h₂ : StrongRefinement.Aborting R Rτ semₛ' semₜ') :
      StrongRefinement R Rτ semₛ semₛ' semₛ'' semₜ semₜ' ∅ := by
    constructor
    · assumption
    · assumption
    · apply Diverging.Empty

  protected theorem ofTerminating {Rτ : Rel εₛ εₜ} {semₛ : Set (α × εₛ × α)} {semₛ' semₛ'' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)}
    (h : StrongRefinement.Terminating R R Rτ semₛ semₛ' semₜ) :
      StrongRefinement R Rτ semₛ semₛ' semₛ'' semₜ ∅ ∅ := by
    constructor
    · assumption
    · apply Aborting.Empty
    · apply Diverging.Empty

  /-- Horizontal composition. `T₁` bundles the first operand's trace relation with both its laws,
  needed by `Terminating.Trans`/`Aborting.Trans`/`Diverging.Trans` alike. No union needed here,
  unlike `Comp`: every execution genuinely passes through the intermediate language. -/
  protected theorem Trans {γ} {εₘ : Type _} [Monoid εₘ] [T₁ : Trace εₛ εₘ] {R₁ R₂} {Rτ₂ : Rel εₘ εₜ}
    {semₛ : Set (α × εₛ × α)} {semₛ' semₛ'' : Set (α × εₛ)}
    {semₜ : Set (β × εₘ × β)} {semₜ' semₜ'' : Set (β × εₘ)}
    {semᵤ : Set (γ × εₜ × γ)} {semᵤ' semᵤ'' : Set (γ × εₜ)} :
      StrongRefinement R₁ T₁.Rτ semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' →
      StrongRefinement R₂ Rτ₂ semₜ semₜ' semₜ'' semᵤ semᵤ' semᵤ'' →
      StrongRefinement (Relation.Comp R₁ R₂) (T₁.Rτ ∘ᵣ Rτ₂) semₛ semₛ' semₛ'' semᵤ semᵤ' semᵤ'' := by
    rintro ⟨ref₁_red, ref₁_abort, ref₁_div⟩ ⟨ref₂_red, ref₂_abort, ref₂_div⟩
    exact ⟨Terminating.Trans ref₁_red ref₁_abort ref₂_red, Aborting.Trans ref₁_abort ref₂_abort,
      Diverging.Trans ref₁_div ref₁_abort ref₂_div⟩

  protected theorem Mono {R} {Rτ : Rel εₛ εₜ}
    {semᵣ semₛ : Set (α × εₛ × α)} {semᵣ' semᵣ'' semₛ' semₛ'' : Set (α × εₛ)} {semₜ semᵤ : Set (β × εₜ × β)} {semₜ' semₜ'' semᵤ' semᵤ'' : Set (β × εₜ)}
    (hyp₁ : semₛ ≤ semᵣ) (hyp₂ : semₛ' ≤ semᵣ') (hyp₃ : semₛ'' ≤ semᵣ'') (concl₁ : semᵤ ≤ semₜ) (concl₂ : semᵤ' ≤ semₜ') (concl₃ : semᵤ'' ≤ semₜ'') :
      StrongRefinement R Rτ semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' ≤ StrongRefinement R Rτ semᵣ semᵣ' semᵣ'' semᵤ semᵤ' semᵤ'' := by
    rintro ⟨ref₁, ref₂, ref₃⟩
    constructor
    · apply Terminating.Mono hyp₁ hyp₂ (λ _ _ ↦ id) concl₁ ref₁
    · apply Aborting.Mono hyp₂ concl₂ ref₂
    · apply Diverging.Mono hyp₃ hyp₂ concl₃ ref₃

  /-- `Rτ_total`/`sat` feed `Diverging.gfp`'s coinduction — see its doc comment for why `sat` in
  particular is unavoidable and what it defers to (D8's commutation argument). -/
  protected theorem FixedPoint {Rτ : Rel εₛ εₜ} (Rτ_total : Relation.LeftTotal Rτ)
    (sat : ∀ X Z Y, StrongRefinement.Diverging R Rτ X Z Y →
      ∀ σₛ ε ε₁ ε₂, Rτ ε₁ ε → Rτ ε₂ ε → (σₛ, ε₁) ∈ X → (σₛ, ε₂) ∈ X)
    {f : Set (α × εₛ × α) →o _} {f' f'' : Set (α × εₛ) →o _} {g : Set (β × εₜ × β) →o _} {g' g''}
    (IH₁ : ∀ x x' y, StrongRefinement.Terminating R R Rτ x x' y → StrongRefinement.Terminating R R Rτ (f x) (f' x') (g y))
    (IH₂ : ∀ x' y', StrongRefinement.Aborting R Rτ x' y' → StrongRefinement.Aborting R Rτ (f' x') (g' y'))
    (IH₃ : ∀ x'' x' y'', StrongRefinement.Diverging R Rτ x'' x' y'' → StrongRefinement.Diverging R Rτ (f'' x'') (f' x') (g'' y'')) :
      StrongRefinement R Rτ (OrderHom.lfp f) (OrderHom.lfp f') (OrderHom.gfp f'') (OrderHom.lfp g) (OrderHom.lfp g') (OrderHom.gfp g'') := by
    constructor
    · exact Terminating.lfp _ _ IH₁
    · exact Aborting.lfp _ IH₂
    · exact Diverging.gfp _ Rτ_total sat IH₃
end StrongRefinement

end
