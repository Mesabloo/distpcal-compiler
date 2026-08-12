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

  /-- Vertical composition. Concludes at `Rτ` itself: the proof naturally produces `Rτ ⊗ᵣ Rτ` — the
  two factors' traces concatenate — and `Trace.rmul_self` says that is `Rτ` again. Running both
  factors at the class rather than at two bare relations is what makes that collapse available;
  the class's left-totality is needed anyway, for the branch where the source aborts inside the
  *first* factor and the target's full trace still has to be matchable. -/
  protected theorem Terminating.Comp {R S T : Rel α β} [T₂ : Trace εₛ εₜ]
      {semₛ semᵤ : Set (α × εₛ × α)} {semₛ' semᵤ' : Set (α × εₛ)} {semₜ semᵥ : Set (β × εₜ × β)} :
      StrongRefinement.Terminating R S T₂.Rτ semₛ semₛ' semₜ →
      StrongRefinement.Terminating S T T₂.Rτ semᵤ semᵤ' semᵥ →
      StrongRefinement.Terminating R T T₂.Rτ (semₛ ∘ᵣ₂ semᵤ) (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ')
        (semₜ ∘ᵣ₂ semᵥ) := by
    intro ref_semₜ ref_semᵥ
    rw [← Trace.rmul_self (T := T₂)]
    revert ref_semₜ ref_semᵥ
    rintro ref_semₜ ref_semᵥ σₜ σᵥ'' ε σₛ σₛRσₜ ⟨σᵥ', ε₁, ε₂, red_σₜ_σᵥ', red_σᵥ'_σᵥ'', rfl⟩
    obtain ⟨σₛ', εₛ₁, σₛ'Rσᵥ', Rτ_εₛ₁_ε₁, sem_εₛ₁⟩|⟨εₛ₁, εₛ₁_scp_ε₁, semₛ'_εₛ₁⟩ :=
      ref_semₜ _ _ _ _ σₛRσₜ red_σₜ_σᵥ'
    · obtain ⟨σᵤ, εₛ₂, σᵤRσᵥ'', Rτ_εₛ₂_ε₂, sem_εₛ₂⟩|⟨εₛ₂, εₛ₂_scp_ε₂, semᵤ'_εₛ₂⟩ :=
        ref_semᵥ _ _ _ _ σₛ'Rσᵥ' red_σᵥ'_σᵥ''
      · left
        exists σᵤ, εₛ₁ * εₛ₂
        exists σᵤRσᵥ'', ⟨εₛ₁, εₛ₂, ε₁, ε₂, rfl, rfl, Rτ_εₛ₁_ε₁, Rτ_εₛ₂_ε₂⟩
        exists σₛ', εₛ₁, εₛ₂
      · right
        exists εₛ₁ * εₛ₂
        refine ⟨Trace.scPrefix_rmul_right Rτ_εₛ₁_ε₁ εₛ₂_scp_ε₂, Or.inr ?_⟩
        exists σₛ', εₛ₁, εₛ₂
    · right
      exists εₛ₁
      exact ⟨Trace.scPrefix_rmul_left T₂.Rτ_total εₛ₁_scp_ε₁, Or.inl semₛ'_εₛ₁⟩

  /-- Monotone in the state sets. There is no trace-relation axis: `Rτ` occurs only positively in
  the conclusion, so widening it would be sound, but after the composition lemmas moved onto `Trace`
  nothing needs it — every caller was already passing the identity. -/
  protected theorem Terminating.Mono {R S : Rel α β} [T : Trace εₛ εₜ]
    {semᵣ semₛ : Set (α × εₛ × α)} {semᵣ' semₛ' : Set (α × εₛ)} {semₜ semᵤ : Set (β × εₜ × β)}
    (hyp₁ : semₛ ≤ semᵣ) (hyp₂ : semₛ' ≤ semᵣ') (concl : semᵤ ≤ semₜ) :
      StrongRefinement.Terminating R S T.Rτ semₛ semₛ' semₜ ≤
        StrongRefinement.Terminating R S T.Rτ semᵣ semᵣ' semᵤ := by
    intros ref σᵤ σᵤ' ε σᵣ' R_σᵣ'_σᵤ' sem_σᵤ'
    obtain ⟨σₛ', ε', R_σₛ'_σᵤ', Rτ_ε'_ε, sem_σₛ'⟩|⟨ε', ε'_scp_ε, sem_σₛ'⟩ :=
      ref _ _ ε _ R_σᵣ'_σᵤ' (Set.mem_of_subset_of_mem concl sem_σᵤ')
    · exact Or.inl ⟨σₛ', ε', R_σₛ'_σᵤ', Rτ_ε'_ε, Set.mem_of_subset_of_mem hyp₁ sem_σₛ'⟩
    · exact Or.inr ⟨ε', ε'_scp_ε, Set.mem_of_subset_of_mem hyp₂ sem_σₛ'⟩

  /-- Doing nothing refines doing nothing. Runs at the canonical `Trace.Rτ` rather than at `Eq` or
  at a bare relation plus a side condition: the single law the identity transition needs is
  `Rτ_one`, which is one of the class's, and every use of this lemma is alongside the composition
  lemmas that take the class anyway. -/
  protected theorem Terminating.Id [T : Trace εₛ εₜ] {X} :
      StrongRefinement.Terminating R R T.Rτ Relation.Idle X Relation.Idle := by
    rintro σₜ σₜ' ε σₛ σₛRσₜ ⟨rfl, rfl⟩
    left
    exact ⟨σₛ, 1, σₛRσₜ, T.Rτ_one, rfl, rfl⟩

  protected theorem Terminating.sup {R S : Rel α β} [T : Trace εₛ εₜ] {A : Set (Set (α × εₛ × α))}
    {B : Set (Set (β × εₜ × β))} {C : Set (Set (α × εₛ))}
    (sup : ∀ y ∈ B, ∃ x ∈ A, ∃ z ∈ C, StrongRefinement.Terminating R S T.Rτ x z y) :
      StrongRefinement.Terminating R S T.Rτ (⋃₀ A) (⋃₀ C) (⋃₀ B) := by
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

  /-- Binary union on both sides, the `Diverging.union` shape at `Terminating`. The aborting set is
  shared and the summands are paired positionally, so there is nothing to choose: each disjunct is
  discharged by its own refinement. `Terminating.sup` is the `⋃₀` generalization, where every target
  summand picks its own source and aborting sets instead; this is its two-element special case, kept
  separate because the positional pairing is what a union-shaped semantics actually wants. -/
  protected theorem Terminating.union {R S : Rel α β} [T : Trace εₛ εₜ]
      {Aₛ Bₛ : Set (α × εₛ × α)} {semₛ' : Set (α × εₛ)} {Aₜ Bₜ : Set (β × εₜ × β)}
      (h₁ : StrongRefinement.Terminating R S T.Rτ Aₛ semₛ' Aₜ)
      (h₂ : StrongRefinement.Terminating R S T.Rτ Bₛ semₛ' Bₜ) :
        StrongRefinement.Terminating R S T.Rτ (Aₛ ∪ Bₛ) semₛ' (Aₜ ∪ Bₜ) := by
    rintro σₜ σₜ' ε σₛ hR (hmem|hmem)
    · obtain ⟨σₛ', ε', hS, hRτ, h⟩|⟨ε', hscp, h⟩ := h₁ σₜ σₜ' ε σₛ hR hmem
      · exact Or.inl ⟨σₛ', ε', hS, hRτ, Or.inl h⟩
      · exact Or.inr ⟨ε', hscp, h⟩
    · obtain ⟨σₛ', ε', hS, hRτ, h⟩|⟨ε', hscp, h⟩ := h₂ σₜ σₜ' ε σₛ hR hmem
      · exact Or.inl ⟨σₛ', ε', hS, hRτ, Or.inr h⟩
      · exact Or.inr ⟨ε', hscp, h⟩

  /-- Terminating refinement for `R*`: the run the target takes is matched step by step, and the
  source's traces concatenate. The operator-preservation law that replaces induction over
  `Algebra.reducing`'s least fixed point.

  Three of the `Trace` class's laws are used here and nowhere in the finite composition lemmas:
  `Rτ_one` for the empty run, `Rτ_closed` to concatenate two matched traces, and `Rτ_total` when the
  source aborts at the very first step. `abs` places an abort reached partway into `semₛ'` itself;
  at a closed-form aborting semantics it is `Relation.star.lcomp₁_absorb`.

  **The source side is `Relation.star semₛ`, matched against a single target step in the
  hypothesis.** A pass whose target takes steps with no source counterpart — Guarded→Network's `.rx`
  thread — cannot instantiate `semₛ := stepₛ`, since no source step matches an `.rx` step. It
  instantiates `semₛ := Relation.star stepₛ` instead, letting the source stutter, and
  `Terminating.starStutter` below is that instantiation with the resulting `R**` collapsed. -/
  protected theorem Terminating.star {R : Rel α β} [T : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {semₛ' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)}
      (abs : semₛ ∘ᵣ₁ semₛ' ≤ semₛ')
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ semₛ' semₜ) :
        StrongRefinement.Terminating R R T.Rτ (Relation.star semₛ) semₛ'
          (Relation.star semₜ) := by
    rintro σₜ σₜ' ε σₛ hR ⟨n, σts, ets, h₀, hn, hsteps, rfl⟩
    dsimp only at h₀ hn
    subst h₀
    induction n generalizing σts ets σₛ with
    | zero =>
      subst hn
      exact Or.inl ⟨σₛ, 1, hR, T.Rτ_one, Relation.star.refl σₛ⟩
    | succ n ih =>
      obtain ⟨σₛ', e', hR', hRτ', hmem'⟩|⟨ea, hea, hea_mem⟩ :=
        ref (σts 0) (σts 1) (ets 0) σₛ hR (hsteps 0 (by omega))
      · obtain ⟨σₛ'', ε'', hR'', hRτ'', hmem''⟩|⟨ε'', hscp'', hmem''⟩ :=
          ih σₛ' (λ i ↦ σts (i + 1)) (λ i ↦ ets (i + 1))
            (λ i hi ↦ hsteps (i + 1) (by omega)) hn hR'
        · refine Or.inl ⟨σₛ'', e' * ε'', hR'', ?_, Relation.star.head hmem' hmem''⟩
          rw [Monoid.partialProd_succ' ets n]
          apply T.Rτ_closed _ _ _ _ hRτ' hRτ''
        · refine Or.inr ⟨e' * ε'', ?_, ?_⟩
          · rw [Monoid.partialProd_succ' ets n]
            apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
            apply Trace.scPrefix_rmul_right hRτ' hscp''
          · apply abs
            apply Relation.lcomp₁.intro hmem' hmem''
      · refine Or.inr ⟨ea, ?_, hea_mem⟩
        rw [Monoid.partialProd_succ' ets n]
        apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
        apply Trace.scPrefix_rmul_left T.Rτ_total hea

  /-- **`Terminating.star` for a source that stutters.** The shape a pass whose target takes steps
  the source cannot match needs: the hypothesis answers one target step with a whole source *run*
  — possibly empty — and the conclusion is still stated at `Relation.star stepₛ`, not at `R**`.

  Nothing new is proved here. `Terminating.star` at `semₛ := Relation.star stepₛ` produces
  `Relation.star (Relation.star stepₛ)` on the source, and `Relation.star.star_eq` collapses it;
  the point of the lemma is that no caller has to notice.

  `abs` is the same absorption side condition, already at the starred shape. At a closed-form
  aborting semantics `Relation.star stepₛ ∘ᵣ₁ immₛ` it is `Relation.star.star_lcomp₁_absorb`. -/
  protected theorem Terminating.starStutter {R : Rel α β} [T : Trace εₛ εₜ]
      {stepₛ : Set (α × εₛ × α)} {semₛ' : Set (α × εₛ)} {stepₜ : Set (β × εₜ × β)}
      (abs : Relation.star stepₛ ∘ᵣ₁ semₛ' ≤ semₛ')
      (ref : StrongRefinement.Terminating R R T.Rτ (Relation.star stepₛ) semₛ' stepₜ) :
        StrongRefinement.Terminating R R T.Rτ (Relation.star stepₛ) semₛ'
          (Relation.star stepₜ) := by
    have h := Terminating.star abs ref
    rwa [Relation.star.star_eq] at h

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
  protected theorem Diverging.Comp {R} [T₂ : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {semₛ' semₛ'' semᵤ' semᵤ'' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)} {semₜ'' semᵥ'' : Set (β × εₜ)} :
      StrongRefinement.Diverging R T₂.Rτ semₛ'' semₛ' semₜ'' →
      StrongRefinement.Diverging R T₂.Rτ semᵤ'' semᵤ' semᵥ'' →
      StrongRefinement.Terminating R R T₂.Rτ semₛ semₛ' semₜ →
      StrongRefinement.Diverging R T₂.Rτ (semₛ'' ∪ semₛ ∘ᵣ₁ semᵤ'') (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₜ'' ∪ semₜ ∘ᵣ₁ semᵥ'') := by
    intro ref₁ ref₂ ref₃
    rw [← Trace.sup_rmul_self (T := T₂)]
    revert ref₁ ref₂ ref₃
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

  protected theorem Diverging.Mono {R} [T : Trace εₛ εₜ]
    {semᵣ'' semᵣ' semₛ'' semₛ' : Set (α × εₛ)} {semₜ'' semᵤ'' : Set (β × εₜ)}
    (hyp₁ : semₛ'' ≤ semᵣ'') (hyp₂ : semₛ' ≤ semᵣ') (concl : semᵤ'' ≤ semₜ'') :
      StrongRefinement.Diverging R T.Rτ semₛ'' semₛ' semₜ'' ≤
        StrongRefinement.Diverging R T.Rτ semᵣ'' semᵣ' semᵤ'' := by
    intros ref σᵤ' ε σᵣ' R_σᵣ'_σᵤ' sem_σᵤ''
    obtain ⟨ε', Rτ_ε'_ε, sem_σₛ''⟩|⟨ε', ε'_scp_ε, sem_σₛ'⟩ :=
      ref _ ε _ R_σᵣ'_σᵤ' (Set.mem_of_subset_of_mem concl sem_σᵤ'')
    · left
      exact ⟨ε', Rτ_ε'_ε, Set.mem_of_subset_of_mem hyp₁ sem_σₛ''⟩
    · right
      exact ⟨ε', ε'_scp_ε, Set.mem_of_subset_of_mem hyp₂ sem_σₛ'⟩

  protected theorem Diverging.Empty [T : Trace εₛ εₜ] {semₛ'' semₛ' : Set (α × εₛ)} :
      StrongRefinement.Diverging R T.Rτ semₛ'' semₛ' ∅ := by
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

    -- One index of the target, matched against a source state sitting over it.
    let cont (i : ℕ) (σ : α) : Prop :=
      ∃ p : α × εₛ, R p.1 (σts (i + 1)) ∧ T.Rτ p.2 (ets i) ∧ (σ, p.2, p.1) ∈ semₛ

    -- The greedy source run: continue where possible, and park on `σₛ` once it cannot.
    let nextp (i : ℕ) (σ : α) : α × εₛ := if h : cont i σ then h.choose else (σₛ, 1)
    let σs : ℕ → α := Nat.rec σₛ (λ i s ↦ (nextp i s).1)
    let es (i : ℕ) : εₛ := (nextp i (σs i)).2

    have hσs₀ : σs 0 = σₛ := rfl
    have hstep_of : ∀ i, cont i (σs i) →
        R (σs (i + 1)) (σts (i + 1)) ∧ T.Rτ (es i) (ets i) ∧ (σs i, es i, σs (i + 1)) ∈ semₛ := by
      intro i h
      change R (nextp i (σs i)).1 (σts (i + 1)) ∧ T.Rτ (nextp i (σs i)).2 (ets i)
             ∧ (σs i, (nextp i (σs i)).2, (nextp i (σs i)).1) ∈ semₛ
      unfold nextp
      repeat rw [dif_pos h]
      exact h.choose_spec

    by_cases! hall : ∀ i, cont i (σs i)
    · -- The source keeps up forever.
      left
      have hR : ∀ i, R (σs i) (σts i) := by
        rintro (_|i)
        · exact R_σₛ_σₜ
        · exact (hstep_of i (hall i)).1
      exact ⟨OmegaProd.ωProd es, Rτ_omega es ets (λ i ↦ (hstep_of i (hall i)).2.1),
        σs, es, hσs₀, λ i ↦ (hstep_of i (hall i)).2.2, rfl⟩
    · -- The source gets stuck; take the first index where it does.
      right
      -- The first index at which it gets stuck, as an opaque natural: `Nat.find` itself does not
      -- support the inductions below.
      set m := Nat.find hall
      have hm_spec : ¬cont m (σs m) := Nat.find_spec hall
      have hm_min i (hi : i < m) := not_not.mp (Nat.find_min hall hi)

      have hR : ∀ i, i ≤ m → R (σs i) (σts i) := by
        rintro (_|i) h
        · exact R_σₛ_σₜ
        · exact (hstep_of i (hm_min i h)).1

      -- At `m` the refinement cannot take its reducing branch, so it takes the aborting one.
      obtain ⟨σ', e', hR', hRτ', hsem'⟩|⟨ea, hea, hea_mem⟩ :=
        ref (σts m) (σts (m + 1)) (ets m) (σs m) (hR m le_rfl) (hstep m)
      · absurd (⟨(σ', e'), hR', hRτ', hsem'⟩ : cont m (σs m))
        exact hm_spec

      -- The abort is reached after `m` steps; `abs` walks it back one step at a time to `σₛ`.
      · have habort : ∀ k i, i + k = m →
            (σs i, Monoid.partialProd (λ j ↦ es (i + j)) k * ea) ∈ semₛ' := by
          intro k
          induction k with
          | zero =>
            intro i hi
            obtain rfl : i = m := hi
            simpa only [Monoid.partialProd_zero, one_mul]
          | succ k ih =>
            intro i hi
            have hfun : (λ j ↦ es (i + (j + 1))) = (λ j ↦ es (i + 1 + j)) := by
              simp +arith
            have hsplit : Monoid.partialProd (λ j ↦ es (i + j)) (k + 1) * ea
                 = es i * (Monoid.partialProd (λ j ↦ es (i + 1 + j)) k * ea) := by
              simp only [Monoid.partialProd_succ' (λ j ↦ es (i + j)) k, mul_assoc, Nat.add_zero,
                hfun]
            rw [hsplit]
            refine abs (Relation.lcomp₁.intro (b := σs (i + 1)) ?_ ?_)
            · refine (hstep_of i (hm_min i ?_)).2.2
              simp +arith [← hi]
            · apply ih (i + 1)
              simp +arith [← hi]

        -- And its trace is a sequentially consistent prefix of the target's.
        have hpp : ∀ n, n ≤ m → T.Rτ (Monoid.partialProd es n) (Monoid.partialProd ets n) := by
          intro n hn
          induction n with
          | zero => exact T.Rτ_one
          | succ n ih =>
            apply T.Rτ_closed _ _ _ _ (ih (Nat.le_of_succ_le hn))
            exact (hstep_of n (hm_min n hn)).2.1
        obtain ⟨r, hr⟩ := dvd ets (m + 1)
        refine ⟨Monoid.partialProd es m * ea, ?_, ?_⟩
        · rw [hr, Monoid.partialProd_succ, mul_assoc]
          apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
          apply Trace.scPrefix_rmul_right (hpp m le_rfl)
          apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
          apply Trace.scPrefix_rmul_left T.Rτ_total hea
        · -- NOTE: Lean style guidelines forbid this. Keep it.
          simpa only [Nat.zero_add] using! habort m 0 (Nat.zero_add m)

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
    rintro σₜ ε σₛ hR ⟨σₜ', e₁, e₂, ⟨n, σts, ets, h₀, hn, hsteps, rfl⟩, hY, rfl⟩
    dsimp only at h₀ hn
    subst h₀
    induction n generalizing σₛ σts ets with
    | zero =>
      subst hn
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
      obtain ⟨σₛ', e', hR', hRτ', hmem'⟩|⟨ea, hea, hea_mem⟩ :=
        ref (σts 0) (σts 1) (ets 0) σₛ hR (hsteps 0 (by omega))
      · obtain ⟨ε'', hRτ'', hmem''⟩|⟨ε'', hscp'', hmem''⟩ :=
          ih σₛ' (λ i ↦ σts (i + 1)) (λ i ↦ ets (i + 1))
            (λ i hi ↦ hsteps (i + 1) (by omega)) hn hR'
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
            apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
            apply Trace.scPrefix_rmul_right hRτ' hscp''
          · apply abs
            apply Relation.lcomp₁.intro hmem' hmem''
      · right
        refine ⟨ea, ?_, hea_mem⟩
        rw [Monoid.partialProd_succ' ets n, mul_assoc]
        apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
        apply Trace.scPrefix_rmul_left T.Rτ_total hea

  /-- Binary union on both sides. The aborting set is shared, so unlike `Terminating.sup` there is
  nothing to choose: each disjunct is discharged by its own refinement. -/
  protected theorem Diverging.union {R : Rel α β} [T : Trace εₛ εₜ]
      {Aₛ Bₛ semₛ' : Set (α × εₛ)} {Aₜ Bₜ : Set (β × εₜ)}
      (h₁ : StrongRefinement.Diverging R T.Rτ Aₛ semₛ' Aₜ)
      (h₂ : StrongRefinement.Diverging R T.Rτ Bₛ semₛ' Bₜ) :
        StrongRefinement.Diverging R T.Rτ (Aₛ ∪ Bₛ) semₛ' (Aₜ ∪ Bₜ) := by
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

  /-- An abort *is* a divergence that always takes the aborting branch. The reducing set is
  unconstrained because that branch never mentions it; `hle` places the witness in whichever
  aborting set the diverging statement carries, which is rarely the same one. -/
  protected theorem Aborting.toDiverging {R : Rel α β} [T : Trace εₛ εₜ]
      {semₛ semₛ' semₛ'' : Set (α × εₛ)} {semₜ' : Set (β × εₜ)}
      (h : StrongRefinement.Aborting R T.Rτ semₛ' semₜ') (hle : semₛ' ≤ semₛ'') :
        StrongRefinement.Diverging R T.Rτ semₛ semₛ'' semₜ' := by
    intro σₜ ε σₛ hR hmem
    obtain ⟨ε', hscp, h'⟩ := h σₜ ε σₛ hR hmem
    exact Or.inr ⟨ε', hscp, hle h'⟩

  /-- The converse, when the two source sets coincide: with nowhere else for the matched branch to
  land, `Rτ ε' ε` weakens to `ε' ≼[Rτ] ε` and the disjunction collapses. -/
  protected theorem Diverging.toAborting {R : Rel α β} [T : Trace εₛ εₜ] {semₛ' : Set (α × εₛ)}
      {semₜ' : Set (β × εₜ)} (h : StrongRefinement.Diverging R T.Rτ semₛ' semₛ' semₜ') :
        StrongRefinement.Aborting R T.Rτ semₛ' semₜ' := by
    intro σₜ ε σₛ hR hmem
    obtain ⟨ε', hRτ, h'⟩|⟨ε', hscp, h'⟩ := h σₜ ε σₛ hR hmem
    · exact ⟨ε', Trace.scPrefix_of hRτ, h'⟩
    · exact ⟨ε', hscp, h'⟩

  /-- Horizontal composition, through an intermediate language with trace type `εₘ`. Needs `Rτ₁`
  (the first leg) both left-total and closed — bundled as `T₁ : Trace εₛ εₘ` — per
  `Trace.scPrefix_rcomp`. The second leg's `Rτ₂` needs nothing. -/
  protected theorem Terminating.Trans {γ} {εₘ : Type _} [Monoid εₘ] {R₁ S₁ : Rel α β} {R₂ S₂ : Rel β γ}
    [T₁ : Trace εₛ εₘ] [T₂ : Trace εₘ εₜ]
    {semₛ : Set (α × εₛ × α)} {semₛ' : Set (α × εₛ)}
    {semₜ : Set (β × εₘ × β)} {semₜ' : Set (β × εₘ)}
    {semᵤ : Set (γ × εₜ × γ)} :
      StrongRefinement.Terminating R₁ S₁ T₁.Rτ semₛ semₛ' semₜ →
      StrongRefinement.Aborting R₁ T₁.Rτ semₛ' semₜ' →
      StrongRefinement.Terminating R₂ S₂ T₂.Rτ semₜ semₜ' semᵤ →
      StrongRefinement.Terminating (Relation.Comp R₁ R₂) (Relation.Comp S₁ S₂) (T₁.Rτ ∘ᵣ T₂.Rτ) semₛ semₛ' semᵤ := by
    rintro ref₁ ref₂ ref₃ σᵤ σᵤ' ε σₛ ⟨σₜ, R₁_σₛ_σₜ, R₂_σₜ_σᵤ⟩ semᵤ_σᵤ_σᵤ'
    obtain ⟨σₜ', εₘ', S₂_σₜ'_σᵤ', Rτ₂_εₘ'_ε, semₜ_σₜ_σₜ'⟩|⟨εₘ', εₘ'_scp_ε, semₜ'_σₜ⟩ :=
      ref₃ _ _ _ _ R₂_σₜ_σᵤ semᵤ_σᵤ_σᵤ'
    · obtain ⟨σₛ', εₛ', S₁_σₛ'_σₜ', Rτ₁_εₛ'_εₘ', semₛ_σₛ_σₛ'⟩|⟨εₛ', εₛ'_scp_εₘ', semₛ'_σₛ⟩ :=
        ref₁ _ _ _ _ R₁_σₛ_σₜ semₜ_σₜ_σₜ'
      · left
        exact ⟨σₛ', εₛ', ⟨σₜ', S₁_σₛ'_σₜ', S₂_σₜ'_σᵤ'⟩, ⟨εₘ', Rτ₁_εₛ'_εₘ', Rτ₂_εₘ'_ε⟩, semₛ_σₛ_σₛ'⟩
      · right
        exact ⟨εₛ', Trace.scPrefix_rcomp T₁.Rτ_total T₁.Rτ_closed εₛ'_scp_εₘ' (Trace.scPrefix_of Rτ₂_εₘ'_ε), semₛ'_σₛ⟩
    · obtain ⟨εₛ', εₛ'_scp_εₘ', semₛ'_σₛ⟩ := ref₂ σₜ εₘ' σₛ R₁_σₛ_σₜ semₜ'_σₜ
      right
      exact ⟨εₛ', Trace.scPrefix_rcomp T₁.Rτ_total T₁.Rτ_closed εₛ'_scp_εₘ' εₘ'_scp_ε, semₛ'_σₛ⟩

  /-- Horizontal composition. Same `scPrefix_rcomp` shape as `Terminating.Trans`: only the first
  leg's `Rτ₁` (bundled as `T₁`) needs laws. -/
  protected theorem Diverging.Trans {γ} {εₘ : Type _} [Monoid εₘ] {R₁ R₂} [T₁ : Trace εₛ εₘ] [T₂ : Trace εₘ εₜ]
    {semₛ'' semₛ' : Set (α × εₛ)} {semₜ'' semₜ' : Set (β × εₘ)} {semᵤ'' : Set (γ × εₜ)} :
      StrongRefinement.Diverging R₁ T₁.Rτ semₛ'' semₛ' semₜ'' →
      StrongRefinement.Aborting R₁ T₁.Rτ semₛ' semₜ' →
      StrongRefinement.Diverging R₂ T₂.Rτ semₜ'' semₜ' semᵤ'' →
      StrongRefinement.Diverging (Relation.Comp R₁ R₂) (T₁.Rτ ∘ᵣ T₂.Rτ) semₛ'' semₛ' semᵤ'' := by
    rintro ref₁ ref₂ ref₃ σᵤ ε σₛ ⟨σₜ, R₁_σₛ_σₜ, R₂_σₜ_σᵤ⟩ semᵤ''_σᵤ
    obtain ⟨εₘ', Rτ₂_εₘ'_ε, semₜ''_σₜ⟩|⟨εₘ', εₘ'_scp_ε, semₜ'_σₜ⟩ := ref₃ _ ε _ R₂_σₜ_σᵤ semᵤ''_σᵤ
    · obtain ⟨εₛ', Rτ₁_εₛ'_εₘ', semₛ''_σₛ⟩|⟨εₛ', εₛ'_scp_εₘ', semₛ'_σₛ⟩ := ref₁ _ εₘ' _ R₁_σₛ_σₜ semₜ''_σₜ
      · left
        exact ⟨εₛ', ⟨εₘ', Rτ₁_εₛ'_εₘ', Rτ₂_εₘ'_ε⟩, semₛ''_σₛ⟩
      · right
        exact ⟨εₛ', Trace.scPrefix_rcomp T₁.Rτ_total T₁.Rτ_closed εₛ'_scp_εₘ' (Trace.scPrefix_of Rτ₂_εₘ'_ε), semₛ'_σₛ⟩
    · obtain ⟨εₛ', εₛ'_scp_εₘ', semₛ'_σₛ⟩ := ref₂ _ εₘ' _ R₁_σₛ_σₜ semₜ'_σₜ
      right
      exact ⟨εₛ', Trace.scPrefix_rcomp T₁.Rτ_total T₁.Rτ_closed εₛ'_scp_εₘ' εₘ'_scp_ε, semₛ'_σₛ⟩

  /-- Vertical composition. The proof produces the union `Rτ ⊔ Rτ ⊗ᵣ Rτ` — the first branch is an
  abort inside the first factor, which never reaches the second, so its relatedness survives as-is
  rather than being forced through `⊗ᵣ` — and `Trace.sup_rmul_self` collapses that back to `Rτ`. -/
  protected theorem Aborting.Comp {R} [T₂ : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {semₛ' semᵤ' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)} {semₜ' semᵥ' : Set (β × εₜ)} :
      StrongRefinement.Aborting R T₂.Rτ semₛ' semₜ' →
      StrongRefinement.Aborting R T₂.Rτ semᵤ' semᵥ' →
      StrongRefinement.Terminating R R T₂.Rτ semₛ semₛ' semₜ →
      StrongRefinement.Aborting R T₂.Rτ (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₜ' ∪ semₜ ∘ᵣ₁ semᵥ') := by
    intro ref₁ ref₂ ref₃
    rw [← Trace.sup_rmul_self (T := T₂)]
    revert ref₁ ref₂ ref₃
    rintro ref₁ ref₂ ref₃ σₜ ε σₛ R_σₛ_σₜ (sem|⟨σₜ', ε₁, ε₂, sem₁, sem₂, rfl⟩)
    · obtain ⟨ε', ε'_scp_ε, sem'⟩ := ref₁ _ _ _ R_σₛ_σₜ sem
      exact ⟨ε', Trace.scPrefix_mono (λ _ _ ↦ Or.inl) ε'_scp_ε, Or.inl sem'⟩
    · obtain ⟨σₛ', εₛ₁, R_σₛ'_σₜ', Rτ_εₛ₁_ε₁, sem₃⟩|⟨εₛ₁, εₛ₁_scp_ε₁, semₛ'_εₛ₁⟩ :=
        ref₃ _ _ _ _ R_σₛ_σₜ sem₁
      · obtain ⟨εₛ₂, εₛ₂_scp_ε₂, sem_εₛ₂⟩ := ref₂ _ _ _ R_σₛ'_σₜ' sem₂
        refine ⟨εₛ₁ * εₛ₂, Trace.scPrefix_mono (λ _ _ ↦ Or.inr) (Trace.scPrefix_rmul_right Rτ_εₛ₁_ε₁ εₛ₂_scp_ε₂), Or.inr ?_⟩
        exists σₛ', εₛ₁, εₛ₂
      · exact ⟨εₛ₁, Trace.scPrefix_mono (λ _ _ ↦ Or.inr) (Trace.scPrefix_rmul_left T₂.Rτ_total εₛ₁_scp_ε₁), Or.inl semₛ'_εₛ₁⟩

  /-- Horizontal composition. Same `scPrefix_rcomp` shape as `Terminating.Trans`. -/
  protected theorem Aborting.Trans {γ} {εₘ : Type _} [Monoid εₘ] {R₁ R₂} [T₁ : Trace εₛ εₘ] [T₂ : Trace εₘ εₜ]
    {semₛ' : Set (α × εₛ)} {semₜ' : Set (β × εₘ)} {semᵤ' : Set (γ × εₜ)} :
      StrongRefinement.Aborting R₁ T₁.Rτ semₛ' semₜ' →
      StrongRefinement.Aborting R₂ T₂.Rτ semₜ' semᵤ' →
      StrongRefinement.Aborting (Relation.Comp R₁ R₂) (T₁.Rτ ∘ᵣ T₂.Rτ) semₛ' semᵤ' := by
    rintro ref₁ ref₂ σᵤ ε σₛ ⟨σₜ, R₁_σₛ_σₜ, R₂_σₜ_σᵤ⟩ sem_σᵤ
    obtain ⟨εₘ', εₘ'_scp_ε, sem_σₜ⟩ := ref₂ σᵤ ε σₜ R₂_σₜ_σᵤ sem_σᵤ
    obtain ⟨εₛ', εₛ'_scp_εₘ', sem_σₛ⟩ := ref₁ σₜ εₘ' σₛ R₁_σₛ_σₜ sem_σₜ
    exact ⟨εₛ', Trace.scPrefix_rcomp T₁.Rτ_total T₁.Rτ_closed εₛ'_scp_εₘ' εₘ'_scp_ε, sem_σₛ⟩

  protected theorem Aborting.Mono {R} [T : Trace εₛ εₜ]
    {semᵣ' semₛ' : Set (α × εₛ)} {semₜ' semᵤ' : Set (β × εₜ)}
    (hyp : semₛ' ≤ semᵣ') (concl : semᵤ' ≤ semₜ') :
      StrongRefinement.Aborting R T.Rτ semₛ' semₜ' ≤
        StrongRefinement.Aborting R T.Rτ semᵣ' semᵤ' := by
    intros ref σᵤ' ε σᵣ' R_σᵣ'_σᵤ' sem_σᵤ'
    obtain ⟨ε', ε'_scp_ε, sem_σₛ'⟩ := ref _ _ _ R_σᵣ'_σᵤ' (Set.mem_of_subset_of_mem concl sem_σᵤ')
    exact ⟨ε', ε'_scp_ε, Set.mem_of_subset_of_mem hyp sem_σₛ'⟩

  protected theorem Aborting.Empty [T : Trace εₛ εₜ] {semₛ' : Set (α × εₛ)} :
      StrongRefinement.Aborting R T.Rτ semₛ' ∅ := by
    rintro _ _ _ _ (_|_)

  protected theorem Aborting.sup [T : Trace εₛ εₜ] {A : Set (Set (α × εₛ))} {B}
    (sup : ∀ y ∈ B, ∃ x ∈ A, StrongRefinement.Aborting R T.Rτ x y) :
      StrongRefinement.Aborting R T.Rτ (⋃₀ A) (⋃₀ B) := by
    intros σₜ ε σₛ R_σₛ_σₜ sem_σₜ

    rw [Set.mem_sUnion] at sem_σₜ
    obtain ⟨abortₜ, abortₜ_in_B, abort_σₜ⟩ := sem_σₜ
    obtain ⟨abortₛ, abortₛ_in_A, ref⟩ := sup _ abortₜ_in_B
    obtain ⟨ε', ε'_scp_ε, abort_σₛ⟩ := ref σₜ ε σₛ R_σₛ_σₜ abort_σₜ
    exists ε', ε'_scp_ε
    exact Set.mem_sUnion_of_mem abort_σₛ abortₛ_in_A

  /-- Binary union on both sides, the `Diverging.union` shape at `Aborting`. Simplest of the three:
  `Aborting` carries no second source set, so there is nothing to share and nothing to choose —
  each disjunct is discharged by its own refinement, and the witness is injected back into the
  summand it came from. `Aborting.sup` is the `⋃₀` generalization, where every target summand picks
  its own source set instead; this is its two-element special case with positional pairing. -/
  protected theorem Aborting.union {R} [T : Trace εₛ εₜ]
      {Aₛ Bₛ : Set (α × εₛ)} {Aₜ Bₜ : Set (β × εₜ)}
      (h₁ : StrongRefinement.Aborting R T.Rτ Aₛ Aₜ)
      (h₂ : StrongRefinement.Aborting R T.Rτ Bₛ Bₜ) :
        StrongRefinement.Aborting R T.Rτ (Aₛ ∪ Bₛ) (Aₜ ∪ Bₜ) := by
    rintro σₜ ε σₛ hR (hmem|hmem)
    · obtain ⟨ε', hscp, h⟩ := h₁ σₜ ε σₛ hR hmem
      exact ⟨ε', hscp, Or.inl h⟩
    · obtain ⟨ε', hscp, h⟩ := h₂ σₜ ε σₛ hR hmem
      exact ⟨ε', hscp, Or.inr h⟩

  /-- Aborting refinement for `R* ∘ᵣ₁ Y`: finitely many steps, then an abort. The aborting
  semantics of an algorithm has exactly this shape — `Algebra.aborting` is `step* ∘ᵣ₁ immediate` —
  so this is the operator-preservation law that replaces induction over its least fixed point.

  `Diverging.star` at the diagonal, with its two conclusions collapsed into one: `Aborting` has no
  "matched exactly" disjunct, only the `≼` one, so the run's traces and the abort's are related the
  same way whether the source kept up or stopped early. That collapse is `Diverging.toAborting`,
  and reading the abort of `Yₛ` as an abort of the whole run is `Aborting.toDiverging` against
  `Relation.star.le_lcomp₁` — so the induction over the run's length is not repeated here.

  Note what is *not* a hypothesis. `Diverging.star` takes the source aborting set as a parameter
  with an `abs` law relating it to `semₛ`; here that set is the conclusion's own left-hand side, so
  absorption is `Relation.star.lcomp₁_absorb` rather than an assumption. The step-level refinement
  therefore mentions `Relation.star semₛ ∘ᵣ₁ Yₛ` — not circular, just the source's actual aborting
  semantics named where the framework needs it. -/
  protected theorem Aborting.star {R : Rel α β} [T : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {Yₛ : Set (α × εₛ)}
      {semₜ : Set (β × εₜ × β)} {Yₜ : Set (β × εₜ)}
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ (Relation.star semₛ ∘ᵣ₁ Yₛ) semₜ)
      (refY : StrongRefinement.Aborting R T.Rτ Yₛ Yₜ) :
        StrongRefinement.Aborting R T.Rτ (Relation.star semₛ ∘ᵣ₁ Yₛ)
          (Relation.star semₜ ∘ᵣ₁ Yₜ) :=
    StrongRefinement.Diverging.toAborting <|
      StrongRefinement.Diverging.star Relation.star.lcomp₁_absorb ref
        (refY.toDiverging Relation.star.le_lcomp₁)

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

  /-- Vertical composition, at the trace relation both operands already run at. Each component's
  own `Comp` absorbs the `⊗ᵣ`/`⊔` its proof produces (`Trace.rmul_self`, `Trace.sup_rmul_self`), so
  nothing is left for a caller to repair — composing a chain of refinements stays at `Rτ` however
  long the chain is. -/
  protected theorem Comp [T₂ : Trace εₛ εₜ]
    {semₛ semᵤ : Set (α × εₛ × α)} {semₛ' semₛ'' semᵤ' semᵤ'' : Set (α × εₛ)} {semₜ semᵥ : Set (β × εₜ × β)} {semₜ' semₜ'' semᵥ' semᵥ'' : Set (β × εₜ)} :
      StrongRefinement R T₂.Rτ semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' →
      StrongRefinement R T₂.Rτ semᵤ semᵤ' semᵤ'' semᵥ semᵥ' semᵥ'' →
      StrongRefinement R T₂.Rτ (semₛ ∘ᵣ₂ semᵤ) (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₛ'' ∪ semₛ ∘ᵣ₁ semᵤ'') (semₜ ∘ᵣ₂ semᵥ) (semₜ' ∪ semₜ ∘ᵣ₁ semᵥ') (semₜ'' ∪ semₜ ∘ᵣ₁ semᵥ'') := by
    rintro ⟨t₁, a₁, d₁⟩ ⟨t₂, a₂, d₂⟩
    exact ⟨Terminating.Comp t₁ t₂, Aborting.Comp a₁ a₂ t₁, Diverging.Comp d₁ d₂ t₁⟩

  protected theorem ofNonDiverging [T : Trace εₛ εₜ] {semₛ : Set (α × εₛ × α)} {semₛ' semₛ'' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)} {semₜ' : Set (β × εₜ)}
    (h₁ : StrongRefinement.Terminating R R T.Rτ semₛ semₛ' semₜ)
    (h₂ : StrongRefinement.Aborting R T.Rτ semₛ' semₜ') :
      StrongRefinement R T.Rτ semₛ semₛ' semₛ'' semₜ semₜ' ∅ := by
    constructor
    · assumption
    · assumption
    · apply Diverging.Empty

  protected theorem ofTerminating [T : Trace εₛ εₜ] {semₛ : Set (α × εₛ × α)} {semₛ' semₛ'' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)}
    (h : StrongRefinement.Terminating R R T.Rτ semₛ semₛ' semₜ) :
      StrongRefinement R T.Rτ semₛ semₛ' semₛ'' semₜ ∅ ∅ := by
    constructor
    · assumption
    · apply Aborting.Empty
    · apply Diverging.Empty

  /-- Horizontal composition. `T₁` bundles the first operand's trace relation with both its laws,
  needed by `Terminating.Trans`/`Aborting.Trans`/`Diverging.Trans` alike. No union needed here,
  unlike `Comp`: every execution genuinely passes through the intermediate language. -/
  protected theorem Trans {γ} {εₘ : Type _} [Monoid εₘ] [T₁ : Trace εₛ εₘ] {R₁ R₂} [T₂ : Trace εₘ εₜ]
    {semₛ : Set (α × εₛ × α)} {semₛ' semₛ'' : Set (α × εₛ)}
    {semₜ : Set (β × εₘ × β)} {semₜ' semₜ'' : Set (β × εₘ)}
    {semᵤ : Set (γ × εₜ × γ)} {semᵤ' semᵤ'' : Set (γ × εₜ)} :
      StrongRefinement R₁ T₁.Rτ semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' →
      StrongRefinement R₂ T₂.Rτ semₜ semₜ' semₜ'' semᵤ semᵤ' semᵤ'' →
      StrongRefinement (Relation.Comp R₁ R₂) (T₁.Rτ ∘ᵣ T₂.Rτ) semₛ semₛ' semₛ'' semᵤ semᵤ' semᵤ'' := by
    rintro ⟨ref₁_red, ref₁_abort, ref₁_div⟩ ⟨ref₂_red, ref₂_abort, ref₂_div⟩
    constructor
    · exact Terminating.Trans ref₁_red ref₁_abort ref₂_red
    · exact Aborting.Trans ref₁_abort ref₂_abort
    · exact Diverging.Trans ref₁_div ref₁_abort ref₂_div

  protected theorem Mono {R} [T : Trace εₛ εₜ]
    {semᵣ semₛ : Set (α × εₛ × α)} {semᵣ' semᵣ'' semₛ' semₛ'' : Set (α × εₛ)} {semₜ semᵤ : Set (β × εₜ × β)} {semₜ' semₜ'' semᵤ' semᵤ'' : Set (β × εₜ)}
    (hyp₁ : semₛ ≤ semᵣ) (hyp₂ : semₛ' ≤ semᵣ') (hyp₃ : semₛ'' ≤ semᵣ'') (concl₁ : semᵤ ≤ semₜ) (concl₂ : semᵤ' ≤ semₜ') (concl₃ : semᵤ'' ≤ semₜ'') :
      StrongRefinement R T.Rτ semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' ≤
        StrongRefinement R T.Rτ semᵣ semᵣ' semᵣ'' semᵤ semᵤ' semᵤ'' := by
    rintro ⟨ref₁, ref₂, ref₃⟩
    constructor
    · apply Terminating.Mono hyp₁ hyp₂ concl₁ ref₁
    · apply Aborting.Mono hyp₂ concl₂ ref₂
    · apply Diverging.Mono hyp₃ hyp₂ concl₃ ref₃

  /-- All three cases at once, at the shapes a step-and-iterate semantics takes: `step*`,
  `step* ∘ᵣ₁ immediate`, `(step* ∘ᵣ₁ Y) ∪ step^∞`.

  Three hypotheses, all about one step: a `Terminating` for the step itself, an `Aborting` for the
  sets a step can abort into, and a `Diverging` for the sets it can diverge into. Everything else is
  derived rather than assumed — the absorption law each preservation lemma wants is
  `Relation.star.lcomp₁_absorb` at these shapes, not a side condition on the caller.

  This is where the paper's per-operator laws (arXiv 2404.17297 §7, Def. 7.22–7.26) are assembled
  into one refinement, and it replaces induction over three fixed points. `Rτ_omega` and `dvd` stay
  explicit for the reasons given on `Diverging.omega`.

  `Yₛ`/`Yₜ` are the immediate-divergence sets, kept general even though the algorithm layer has
  none: whether a single step can diverge is a property of the semantics being refined, not of this
  framework. `sequentialOmega` is the `Y = ∅` case, which is what `Algebra` instantiates. -/
  protected theorem sequential [OmegaProd εₛ] [OmegaProd εₜ] [T : Trace εₛ εₜ] {R : Rel α β}
      (Rτ_omega : ∀ (e' : ℕ → εₛ) (e : ℕ → εₜ), (∀ i, T.Rτ (e' i) (e i)) →
        T.Rτ (OmegaProd.ωProd e') (OmegaProd.ωProd e))
      (dvd : OmegaProd.HasPartialProdDvd εₜ)
      {stepₛ : Set (α × εₛ × α)} {immₛ Yₛ : Set (α × εₛ)}
      {stepₜ : Set (β × εₜ × β)} {immₜ Yₜ : Set (β × εₜ)}
      (ref : StrongRefinement.Terminating R R T.Rτ stepₛ (Relation.star stepₛ ∘ᵣ₁ immₛ) stepₜ)
      (refImm : StrongRefinement.Aborting R T.Rτ immₛ immₜ)
      (refY : StrongRefinement.Diverging R T.Rτ Yₛ (Relation.star stepₛ ∘ᵣ₁ immₛ) Yₜ) :
        StrongRefinement R T.Rτ
          (Relation.star stepₛ) (Relation.star stepₛ ∘ᵣ₁ immₛ)
          (Relation.star stepₛ ∘ᵣ₁ Yₛ ∪ Relation.omega stepₛ)
          (Relation.star stepₜ) (Relation.star stepₜ ∘ᵣ₁ immₜ)
          (Relation.star stepₜ ∘ᵣ₁ Yₜ ∪ Relation.omega stepₜ) where
    terminating := Terminating.star Relation.star.lcomp₁_absorb ref
    aborting := Aborting.star ref refImm
    diverging := Diverging.closedForm Rτ_omega dvd Relation.star.lcomp₁_absorb ref refY

  /-- `sequential` where no single step diverges, so the diverging component collapses to `step^∞`.

  This is the algorithm layer's case — `CodeTable.procDiverging` is `∅`, an atomic block having no
  non-terminating semantics — and the conclusion is then *definitionally* `Algebra.reducing`,
  `.aborting`, `.diverging`, so a caller applies it without rewriting anything. The collapse is done
  here, once, rather than at each use site. -/
  protected theorem sequentialOmega [OmegaProd εₛ] [OmegaProd εₜ] [T : Trace εₛ εₜ] {R : Rel α β}
      (Rτ_omega : ∀ (e' : ℕ → εₛ) (e : ℕ → εₜ), (∀ i, T.Rτ (e' i) (e i)) →
        T.Rτ (OmegaProd.ωProd e') (OmegaProd.ωProd e))
      (dvd : OmegaProd.HasPartialProdDvd εₜ)
      {stepₛ : Set (α × εₛ × α)} {immₛ : Set (α × εₛ)}
      {stepₜ : Set (β × εₜ × β)} {immₜ : Set (β × εₜ)}
      (ref : StrongRefinement.Terminating R R T.Rτ stepₛ (Relation.star stepₛ ∘ᵣ₁ immₛ) stepₜ)
      (refImm : StrongRefinement.Aborting R T.Rτ immₛ immₜ) :
        StrongRefinement R T.Rτ
          (Relation.star stepₛ) (Relation.star stepₛ ∘ᵣ₁ immₛ) (Relation.omega stepₛ)
          (Relation.star stepₜ) (Relation.star stepₜ ∘ᵣ₁ immₜ) (Relation.omega stepₜ) := by
    have h := StrongRefinement.sequential (Yₛ := ∅) (Yₜ := ∅) Rτ_omega dvd ref refImm
      (Diverging.Empty R)
    rwa [Relation.lcomp₁.right_empty_eq_empty, Set.empty_union,
      Relation.lcomp₁.right_empty_eq_empty, Set.empty_union] at h

end StrongRefinement

end
