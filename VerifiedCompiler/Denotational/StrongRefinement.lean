module

public import VerifiedCompiler.Trace
public import VerifiedCompiler.ClosedForm
public import Mathlib.Data.Rel
public import Extra.Rel
public import Extra.Set
public import Mathlib.Data.Nat.Find
meta import CustomPrelude

public section

namespace StrongRefinement
  variable {εₛ εₜ : Type _} [Monoid εₛ] [Monoid εₜ] {α β : Type _} (R S : Rel α β) (Rτ : Rel εₛ εₜ)

  /--
    Behavior refinement in the terminating case.

    - `semₛ` is the reducing semantics for the source language.
    - `semₛ'` is the aborting semantics for the source language.
    - `semₜ` is the reducing semantics for the target language.

    Given the top and right edges, the definition supplies the bottom and left edges below, or the
    aborting alternative underneath that. Diagram notation used throughout this file:
    `\mathit{sem}_s`/`\mathit{sem}_t` are `semₛ`/`semₜ`, `\varepsilon'`/`\varepsilon` are the
    source/target traces, and `\lightning` marks "aborts instead". `amscd` (the `CD` environment
    doc-gen4's MathJax renders) has no dashed-line primitive, so every edge below is drawn solid
    regardless of whether it's a hypothesis or a conclusion — here top and right are given, bottom
    and left are supplied.
    $$
    \begin{CD}
    \sigma_s @>R>> \sigma_t \\
    @V{\mathit{sem}_s}V{\varepsilon'}V @V{\mathit{sem}_t}V{\varepsilon}V \\
    \sigma_s' @>S>> \sigma_t'
    \end{CD}
    $$
    or
    $$
    \begin{CD}
    \sigma_s @>R>> \sigma_t \\
    @V{\mathit{sem}_s'}V{\varepsilon' \preceq \varepsilon}V @V{\mathit{sem}_t}V{\varepsilon}V \\
    \lightning @. \sigma_t'
    \end{CD}
    $$
    (`\preceq` above stands for `≼[Rτ]`; the first square's two vertical labels are related by `Rτ`
    directly instead, not pictured.)

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
    · intro _ _ _ _ _ sup
      exact Terminating.sup sup

  /--
    Behavior refinement in the diverging case.

    - `semₛ` is the diverging semantics for the source language.
    - `semₛ'` is the aborting semantics for the source language.
    - `semₜ` is the diverging semantics for the target language.

    Same diagram notation as `Terminating`; both columns run to `∞` when they diverge, or to
    `\lightning` on the source side when it aborts instead:
    $$
    \begin{CD}
    \sigma_s @>R>> \sigma_t \\
    @V{\mathit{sem}_s}V{\varepsilon'}V @V{\mathit{sem}_t}V{\varepsilon}V \\
    \infty @. \infty
    \end{CD}
    $$
    or
    $$
    \begin{CD}
    \sigma_s @>R>> \sigma_t \\
    @V{\mathit{sem}_s'}V{\varepsilon' \preceq \varepsilon}V @V{\mathit{sem}_t}V{\varepsilon}V \\
    \lightning @. \infty
    \end{CD}
    $$
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


  /-- Divergence refinement for `R^∞`, the replacement for `Diverging.gfp`'s coinduction.

  The target takes infinitely many steps; the source follows it one index at a time. Either it
  keeps up forever — and then its trace is the infinite product of the traces it emitted, related
  to the target's by `Rτ_omega` — or it aborts at some first index `n`, and the abort it reports is
  the one it reaches after `n` steps.

  Sequential, not König: the source run is built by choosing greedily at each index, never by
  reconstructing an infinite witness from a family of finite approximants. Nothing here asks
  whether the emitted traces are empty, so there is no productivity or fairness side condition —
  a source that follows a silently-diverging target forever emits `1`, which is correct.

  `abs` says the aborting set absorbs a step on the left, which is what makes "aborts after `n`
  steps" an element of `semₛ'` itself rather than of `semₛⁿ ∘ᵣ₁ semₛ'`. Any aborting semantics
  defined as a least fixed point of `X ↦ immediate ∪ sem ∘ᵣ₁ X` satisfies it by `map_le_lfp`. -/
  protected theorem Diverging.omega {R : Rel α β} [OmegaProd εₛ] [OmegaProd εₜ] [T : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {semₛ' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)}
      (Rτ_omega : ∀ (e' : ℕ → εₛ) (e : ℕ → εₜ), (∀ i, T.Rτ (e' i) (e i)) →
        T.Rτ (OmegaProd.ωProd e') (OmegaProd.ωProd e))
      (dvd : OmegaProd.HasPartialProdDvd εₜ)
      (abs : semₛ ∘ᵣ₁ semₛ' ≤ semₛ')
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ semₛ' semₜ) :
        StrongRefinement.Diverging R T.Rτ (Relation.omega semₛ) semₛ' (Relation.omega semₜ) := by classical
    rintro σₜ ε σₛ R_σₛ_σₜ ⟨σts, ets, hσts₀, hstep, rfl⟩
    subst hσts₀

    -- `T.Rτ ⊗ᵣ T.Rτ` collapses to `T.Rτ`; used to discharge every `≼` obligation below.
    have mulmono : ∀ x y, (T.Rτ ⊗ᵣ T.Rτ) x y → T.Rτ x y := by
      rintro _ _ ⟨a₁, a₂, b₁, b₂, rfl, rfl, h₁, h₂⟩
      exact T.Rτ_closed _ _ _ _ h₁ h₂

    -- One index of the target, matched against a source state sitting over it.
    set cont : ℕ → α → Prop :=
      λ i σ ↦ ∃ p : α × εₛ, R p.1 (σts (i + 1)) ∧ T.Rτ p.2 (ets i) ∧ (σ, p.2, p.1) ∈ semₛ with hcont

    -- The greedy source run: continue where possible, and park on `σₛ` once it cannot.
    set nextp : ℕ → α → α × εₛ := λ i σ ↦ if h : cont i σ then h.choose else (σₛ, 1) with hnextp
    set σs : ℕ → α := λ n ↦ Nat.rec σₛ (λ i s ↦ (nextp i s).1) n with hσs
    set es : ℕ → εₛ := λ i ↦ (nextp i (σs i)).2 with hes

    have hσs₀ : σs 0 = σₛ := rfl
    have hstep_of : ∀ i, cont i (σs i) →
        R (σs (i + 1)) (σts (i + 1)) ∧ T.Rτ (es i) (ets i) ∧ (σs i, es i, σs (i + 1)) ∈ semₛ := by
      intro i h
      have : σs (i + 1) = (nextp i (σs i)).1 := rfl
      rw [this, hes, hnextp]
      simp only [dif_pos h]
      exact h.choose_spec

    by_cases! hall : ∀ i, cont i (σs i)
    · -- The source keeps up forever.
      left
      have hR : ∀ i, R (σs i) (σts i) := by
        intro i
        induction i with
        | zero => exact R_σₛ_σₜ
        | succ i ih => exact (hstep_of i (hall i)).1
      exact ⟨OmegaProd.ωProd es, Rτ_omega es ets (λ i ↦ (hstep_of i (hall i)).2.1),
        σs, es, hσs₀, λ i ↦ (hstep_of i (hall i)).2.2, rfl⟩
    · -- The source gets stuck; take the first index where it does.
      right
      obtain ⟨n, hn⟩ := hall
      have hex : ∃ i, ¬cont i (σs i) := ⟨n, hn⟩
      -- The first index at which it gets stuck, as an opaque natural: `Nat.find` itself does not
      -- support the inductions below.
      obtain ⟨m, hm_spec, hm_min⟩ : ∃ m, ¬cont m (σs m) ∧ ∀ i, i < m → cont i (σs i) :=
        ⟨Nat.find hex, Nat.find_spec hex, λ i hi ↦ not_not.mp (Nat.find_min hex hi)⟩

      have hR : ∀ i, i ≤ m → R (σs i) (σts i) := by
        intro i
        induction i with
        | zero => exact λ _ ↦ R_σₛ_σₜ
        | succ i ih => exact λ hi ↦ (hstep_of i (hm_min i (by omega))).1

      -- At `m` the refinement cannot take its reducing branch, so it takes the aborting one.
      obtain ⟨σ', e', hR', hRτ', hsem'⟩|⟨ea, hea, hea_mem⟩ :=
        ref (σts m) (σts (m + 1)) (ets m) (σs m) (hR m le_rfl) (hstep m)
      · absurd (⟨(σ', e'), hR', hRτ', hsem'⟩ : cont m (σs m))
        exact hm_spec

      -- The abort is reached after `m` steps; `abs` walks it back one step at a time to `σₛ`.
      have habort : ∀ k i, i + k = m →
          (σs i, Monoid.partialProd (λ j ↦ es (i + j)) k * ea) ∈ semₛ' := by
        intro k
        induction k with
        | zero => intro i hi; simpa using (by rw [show i = m by omega]; exact hea_mem)
        | succ k ih =>
          intro i hi
          have hstep_i := (hstep_of i (hm_min i (by omega))).2.2
          have hrest := ih (i + 1) (by omega)
          have hfun : (λ j ↦ es (i + (j + 1))) = (λ j ↦ es (i + 1 + j)) := by
            funext j; congr 1; omega
          have hsplit : Monoid.partialProd (λ j ↦ es (i + j)) (k + 1) * ea
               = es i * (Monoid.partialProd (λ j ↦ es (i + 1 + j)) k * ea) := by
            rw [Monoid.partialProd_succ' (λ j ↦ es (i + j)) k, mul_assoc]
            simp only [Nat.add_zero, hfun]
          rw [hsplit]
          exact abs (Relation.lcomp₁.intro hstep_i hrest)

      -- And its trace is a sequentially consistent prefix of the target's.
      have hpp : ∀ n, n ≤ m → T.Rτ (Monoid.partialProd es n) (Monoid.partialProd ets n) := by
        intro n
        induction n with
        | zero => exact λ _ ↦ T.Rτ_one
        | succ n ih =>
          intro hn
          apply T.Rτ_closed _ _ _ _ (ih (by omega))
          exact (hstep_of n (hm_min n (by omega))).2.1
      obtain ⟨r, hr⟩ := dvd ets (m + 1)
      refine ⟨Monoid.partialProd es m * ea, ?_, ?_⟩
      · rw [hr, Monoid.partialProd_succ, mul_assoc]
        apply Trace.scPrefix_mono mulmono
        apply Trace.scPrefix_rmul_right (hpp m le_rfl)
        apply Trace.scPrefix_mono mulmono
        apply Trace.scPrefix_rmul_left T.Rτ_total hea
      · have h₀ := habort m 0 (by omega)
        simp only [Nat.zero_add] at h₀
        exact h₀

  /-- Divergence refinement for `R* ∘ᵣ₁ Y`: finitely many steps, then a divergence.

  The other half of the closed form. A diverging semantics given as `gfp (λ x, Y ∪ X ∘ᵣ₁ x)` denotes
  `(X* ∘ᵣ₁ Y) ∪ X^∞`, so a refinement framework that only covered `X^∞` would only cover instances
  with `Y = ∅`. This lemma and `Diverging.omega` between them cover the general shape.

  Simpler than `Diverging.omega`: the run is finite and handed over up front, so this is an
  induction on its length with no choice and no `dvd`/`Rτ_one` obligation. -/
  protected theorem Diverging.star {R : Rel α β} [T : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {semₛ' Yₛ : Set (α × εₛ)}
      {semₜ : Set (β × εₜ × β)} {Yₜ : Set (β × εₜ)}
      (abs : semₛ ∘ᵣ₁ semₛ' ≤ semₛ')
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ semₛ' semₜ)
      (refY : StrongRefinement.Diverging R T.Rτ Yₛ semₛ' Yₜ) :
        StrongRefinement.Diverging R T.Rτ (Relation.star semₛ ∘ᵣ₁ Yₛ) semₛ'
          (Relation.star semₜ ∘ᵣ₁ Yₜ) := by
    have mulmono : ∀ x y, (T.Rτ ⊗ᵣ T.Rτ) x y → T.Rτ x y := by
      rintro _ _ ⟨a₁, a₂, b₁, b₂, rfl, rfl, h₁, h₂⟩
      exact T.Rτ_closed _ _ _ _ h₁ h₂

    have main : ∀ (n : ℕ) (σts : ℕ → β) (ets : ℕ → εₜ) (σₛ : α) (σₜ' : β) (e₂ : εₜ),
        R σₛ (σts 0) → (∀ i, i < n → (σts i, ets i, σts (i + 1)) ∈ semₜ) → σts n = σₜ' →
        (σₜ', e₂) ∈ Yₜ →
        (∃ ε', T.Rτ ε' (Monoid.partialProd ets n * e₂) ∧ (σₛ, ε') ∈ Relation.star semₛ ∘ᵣ₁ Yₛ) ∨
        (∃ ε', ε' ≼[T.Rτ] (Monoid.partialProd ets n * e₂) ∧ (σₛ, ε') ∈ semₛ') := by
      intro n
      induction n with
      | zero =>
        intro σts ets σₛ σₜ' e₂ hR _ hlast hY
        subst hlast
        obtain ⟨ε', hRτ, hmem⟩|⟨ε', hscp, hmem⟩ := refY (σts 0) e₂ σₛ hR hY
        · left
          refine ⟨ε', ?_, ?_⟩
          · rwa [Monoid.partialProd_zero, one_mul]
          · rw [← one_mul ε']
            apply Relation.lcomp₁.intro (Relation.star.refl σₛ) hmem
        · right
          refine ⟨ε', ?_, hmem⟩
          rwa [Monoid.partialProd_zero, one_mul]
      | succ n ih =>
        intro σts ets σₛ σₜ' e₂ hR hsteps hlast hY
        obtain ⟨σₛ', e', hR', hRτ', hmem'⟩|⟨ea, hea, hea_mem⟩ :=
          ref (σts 0) (σts 1) (ets 0) σₛ hR (hsteps 0 (by omega))
        · obtain ⟨ε'', hRτ'', hmem''⟩|⟨ε'', hscp'', hmem''⟩ :=
            ih (λ i ↦ σts (i + 1)) (λ i ↦ ets (i + 1)) σₛ' σₜ' e₂ hR'
              (λ i hi ↦ hsteps (i + 1) (by omega)) hlast hY
          · left
            refine ⟨e' * ε'', ?_, ?_⟩
            · rw [Monoid.partialProd_succ' ets n, mul_assoc]
              apply T.Rτ_closed _ _ _ _ hRτ' hRτ''
            · obtain ⟨σᵣ, e₃, e₄, hs, hy, rfl⟩ := hmem''
              rw [← mul_assoc]
              apply Relation.lcomp₁.intro (Relation.star.head hmem' hs) hy
          · right
            refine ⟨e' * ε'', ?_, ?_⟩
            · rw [Monoid.partialProd_succ' ets n, mul_assoc]
              apply Trace.scPrefix_mono mulmono
              apply Trace.scPrefix_rmul_right hRτ' hscp''
            · apply abs
              apply Relation.lcomp₁.intro hmem' hmem''
        · right
          refine ⟨ea, ?_, hea_mem⟩
          rw [Monoid.partialProd_succ' ets n, mul_assoc]
          apply Trace.scPrefix_mono mulmono
          apply Trace.scPrefix_rmul_left T.Rτ_total hea

    rintro σₜ ε σₛ hR ⟨σₜ', e₁, e₂, ⟨n, σts, ets, h₀, hn, hsteps, rfl⟩, hY, rfl⟩
    dsimp only at h₀ hn
    subst h₀
    exact main n σts ets σₛ σₜ' e₂ hR hsteps hn hY

  omit [Monoid εₜ] in
  /-- Binary union on both sides. The aborting set is shared, so unlike `Terminating.sup` there is
  nothing to choose: each disjunct is discharged by its own refinement. -/
  protected theorem Diverging.union {R : Rel α β} {Rτ : Rel εₛ εₜ}
      {Aₛ Bₛ semₛ' : Set (α × εₛ)} {Aₜ Bₜ : Set (β × εₜ)}
      (h₁ : StrongRefinement.Diverging R Rτ Aₛ semₛ' Aₜ)
      (h₂ : StrongRefinement.Diverging R Rτ Bₛ semₛ' Bₜ) :
        StrongRefinement.Diverging R Rτ (Aₛ ∪ Bₛ) semₛ' (Aₜ ∪ Bₜ) := by
    rintro σₜ ε σₛ hR (hmem|hmem)
    · obtain ⟨ε', hRτ, h⟩|⟨ε', hscp, h⟩ := h₁ σₜ ε σₛ hR hmem
      · exact Or.inl ⟨ε', hRτ, Or.inl h⟩
      · exact Or.inr ⟨ε', hscp, h⟩
    · obtain ⟨ε', hRτ, h⟩|⟨ε', hscp, h⟩ := h₂ σₜ ε σₛ hR hmem
      · exact Or.inl ⟨ε', hRτ, Or.inr h⟩
      · exact Or.inr ⟨ε', hscp, h⟩

  /-- The closed form in one piece: `gfp (λ x, Y ∪ X ∘ᵣ₁ x)` denotes `(X* ∘ᵣ₁ Y) ∪ X^∞`, and this
  refines it as such. `Diverging.omega` is the `Y = ∅` special case, where the left summand is
  empty; stating both means the framework does not silently assume that instantiation. -/
  protected theorem Diverging.closedForm {R : Rel α β} [OmegaProd εₛ] [OmegaProd εₜ]
      [T : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {semₛ' Yₛ : Set (α × εₛ)}
      {semₜ : Set (β × εₜ × β)} {Yₜ : Set (β × εₜ)}
      (Rτ_omega : ∀ (e' : ℕ → εₛ) (e : ℕ → εₜ), (∀ i, T.Rτ (e' i) (e i)) →
        T.Rτ (OmegaProd.ωProd e') (OmegaProd.ωProd e))
      (dvd : OmegaProd.HasPartialProdDvd εₜ)
      (abs : semₛ ∘ᵣ₁ semₛ' ≤ semₛ')
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ semₛ' semₜ)
      (refY : StrongRefinement.Diverging R T.Rτ Yₛ semₛ' Yₜ) :
        StrongRefinement.Diverging R T.Rτ (Relation.star semₛ ∘ᵣ₁ Yₛ ∪ Relation.omega semₛ) semₛ'
          (Relation.star semₜ ∘ᵣ₁ Yₜ ∪ Relation.omega semₜ) := by
    apply Diverging.union
    · exact Diverging.star abs ref refY
    · exact Diverging.omega Rτ_omega dvd abs ref

  ------------------------------------

  /--
    Behavior refinement in the aborting case.

    - `semₛ'` is the aborting semantics for the source language.
    - `semₜ'` is the aborting semantics for the target language.

    Same diagram notation as `Terminating`; there is no bottom edge here — an aborting state has no
    "after", just the abort itself on each side:
    $$
    \begin{CD}
    \sigma_s @>R>> \sigma_t \\
    @V{\mathit{sem}_s'}V{\varepsilon' \preceq \varepsilon}V @V{\mathit{sem}_t'}V{\varepsilon}V \\
    \lightning @. \lightning
    \end{CD}
    $$
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
  theorem Aborting.lfp {Rτ : Rel εₛ εₜ} {f : Set (α × εₛ) →o _} {g : Set (β × εₜ) →o _}
    (IH : ∀ x y, StrongRefinement.Aborting R Rτ x y → StrongRefinement.Aborting R Rτ (f x) (g y)) :
      StrongRefinement.Aborting R Rτ (OrderHom.lfp f) (OrderHom.lfp g) := by
    apply OrderHom.lfp_induction₂ (p := λ x y ↦ StrongRefinement.Aborting R Rτ x y)
    · intros A B _ A_le_lfp_f B_le_lfp_g
      apply IH
      assumption
    · intro _ _ _ sup
      exact Aborting.sup _ sup
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

  /-- The three cases at once, for semantics defined by fixed points.

  The terminating and aborting components are least fixed points, as before. The diverging
  component is **not** a greatest fixed point: it is `R^∞`, the infinite iteration, given directly.

  That is a correction, not a presentational choice. The greatest fixed point of
  `x ↦ Y ∪ (X ∘ᵣ₁ x)` is the wrong set whenever `X` has a step emitting the empty trace, since the
  functional is then non-contractive and its gfp admits an arbitrary trace on top of any silently
  diverging state — see `Relation.omega`'s doc. `Algebra.step` has such steps, so the two really do
  differ on the semantics this framework is for.

  The diverging component is the full closed form `(X* ∘ᵣ₁ Y) ∪ X^∞`, not just `X^∞`: a semantics
  whose functional has a non-trivial `Y` is exactly as much an instance of this framework as one
  where `Y = ∅`. For the latter, `Y := ∅` collapses the left summand and `Diverging.omega` is
  available directly.

  `T` supplies the three trace laws (`Rτ_total`, `Rτ_closed`, `Rτ_one`). `Rτ_omega` and `dvd` stay
  explicit: the first mentions `OmegaProd.ωProd`, so folding it into `Trace` would put `OmegaProd`
  binders on every lemma that takes a `Trace` — including the composition lemmas, which have nothing
  to do with divergence; the second is a property of the target monoid's product rather than of the
  relation. `abs` is `Diverging.omega`'s; see there. -/
  protected theorem FixedPoint [OmegaProd εₛ] [OmegaProd εₜ] [T : Trace εₛ εₜ]
    (Rτ_omega : ∀ (e' : ℕ → εₛ) (e : ℕ → εₜ), (∀ i, T.Rτ (e' i) (e i)) →
      T.Rτ (OmegaProd.ωProd e') (OmegaProd.ωProd e))
    (dvd : OmegaProd.HasPartialProdDvd εₜ)
    {f : Set (α × εₛ × α) →o _} {f' : Set (α × εₛ) →o _} {g : Set (β × εₜ × β) →o _} {g'}
    {stepₛ : Set (α × εₛ × α)} {stepₜ : Set (β × εₜ × β)}
    {Yₛ : Set (α × εₛ)} {Yₜ : Set (β × εₜ)}
    (abs : stepₛ ∘ᵣ₁ OrderHom.lfp f' ≤ OrderHom.lfp f')
    (IH₁ : ∀ x x' y, StrongRefinement.Terminating R R T.Rτ x x' y → StrongRefinement.Terminating R R T.Rτ (f x) (f' x') (g y))
    (IH₂ : ∀ x' y', StrongRefinement.Aborting R T.Rτ x' y' → StrongRefinement.Aborting R T.Rτ (f' x') (g' y'))
    (IH₃ : StrongRefinement.Terminating R R T.Rτ stepₛ (OrderHom.lfp f') stepₜ)
    (IH₄ : StrongRefinement.Diverging R T.Rτ Yₛ (OrderHom.lfp f') Yₜ) :
      StrongRefinement R T.Rτ (OrderHom.lfp f) (OrderHom.lfp f')
        (Relation.star stepₛ ∘ᵣ₁ Yₛ ∪ Relation.omega stepₛ)
        (OrderHom.lfp g) (OrderHom.lfp g')
        (Relation.star stepₜ ∘ᵣ₁ Yₜ ∪ Relation.omega stepₜ) := by
    constructor
    · exact Terminating.lfp _ _ IH₁
    · exact Aborting.lfp _ IH₂
    · exact Diverging.closedForm Rτ_omega dvd abs IH₃ IH₄
end StrongRefinement

end
