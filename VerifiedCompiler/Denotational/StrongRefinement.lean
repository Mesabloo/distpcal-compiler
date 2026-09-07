module

public import VerifiedCompiler.Trace
public import VerifiedCompiler.ClosedForm
public import Mathlib.Data.Rel
public import Extra.Rel
public import Extra.Set
public import Mathlib.Data.Nat.Find
meta import CustomPrelude

public section

/-!
# Strong behavior refinement

`Terminating`, `Diverging`, `Aborting` and `Blocking` are the four shapes a behavior refinement
takes, one per way a target run can end. `StrongRefinement` bundles all four for a single pass;
the `Comp`, `Trans`, `Mono`, `star` and `sequential` lemmas are their algebra.

Each definition is a commuting square, drawn in its doc comment:

* top edge — the pre-relation `R` between a source configuration `σₛ` and a target `σₜ`;
* verticals — one step of each semantics, right-labelled by the trace it emits (`ε'` source,
  `ε` target); the left label names the source semantics taken, `sem_s` the one being matched
  (reducing, diverging or blocking) and `sem_s'` the aborting one;
* bottom row — where each side lands: `σₛ'`/`σₜ'` a configuration, `↯` an abort, `∞` a
  divergence, `∅` a stuck configuration. `@.` is no edge.

The source trace is existentially quantified and only ever related to the target's — by `Rτ` on a
matched step, by `≼[Rτ]` (a sequentially consistent prefix, not a syntactic one; `\preceq` in the
squares) on an abort — never shared. In each square the top and right edges are the hypothesis and
the bottom and left are what the definition supplies; `amscd` draws every edge solid, so that
split is not visible.
-/

namespace StrongRefinement
  variable {εₛ εₜ : Type _} [Monoid εₛ] [Monoid εₜ] {α β : Type _} (R S : Rel α β) (Rτ : Rel εₛ εₜ)

  /--
    Behavior refinement for a target run that terminates.

    From `R σₛ σₜ` and a `semₜ` step `(σₜ, ε, σₜ')`, the source either takes a matching `semₛ` step
    to some `σₛ'` with `S σₛ' σₜ'` and `Rτ ε' ε`, or aborts via `semₛ'` on a trace with
    `ε' ≼[Rτ] ε`. `S` is the post-relation, usually `R` again.

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
    \unicode{x21AF} @. \sigma_t'
    \end{CD}
    $$
  -/
  @[expose]
  protected def Terminating (semₛ : Set (α × εₛ × α)) (semₛ' : Set (α × εₛ)) (semₜ : Set (β × εₜ × β)) : Prop :=
    ∀ (σₜ σₜ' : β) (ε : εₜ) (σₛ : α), R σₛ σₜ → (σₜ, ε, σₜ') ∈ semₜ →
      (∃ (σₛ' : α) (ε' : εₛ), S σₛ' σₜ' ∧ Rτ ε' ε ∧ (σₛ, ε', σₛ') ∈ semₛ) ∨
      (∃ ε' : εₛ, ε' ≼[Rτ] ε ∧ (σₛ, ε') ∈ semₛ')

  /-- Vertical composition: a `Terminating` refinement of `semₛ ∘ᵣ₂ semᵤ` against `semₜ ∘ᵣ₂ semᵥ`,
  from one refinement of each factor sharing the middle relation `S`. Trace relation stays `Rτ`;
  the composite aborting set is `semₛ' ∪ semₛ ∘ᵣ₁ semᵤ'`. -/
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

  /-- Monotone in the state sets: widen either source set, shrink the target set. -/
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

  /-- Both reducing sets cut to the runs whose final state satisfies a predicate. `hback` carries
  the target predicate back across `R`; without it, restricting the source set would not be
  monotone. Turns a reachability relation into a terminating semantics on both sides at once. -/
  protected theorem Terminating.restrictEnd {R : Rel α β} [T : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {semₛ' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)}
      {Qₛ : α → Prop} {Qₜ : β → Prop}
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ semₛ' semₜ)
      (hback : ∀ σₛ σₜ, R σₛ σₜ → Qₜ σₜ → Qₛ σₛ) :
      StrongRefinement.Terminating R R T.Rτ {x ∈ semₛ | Qₛ x.2.2} semₛ' {x ∈ semₜ | Qₜ x.2.2} := by
    rintro σₜ σₜ' ε σₛ hR ⟨hmem, hQ⟩
    obtain ⟨σₛ', ε', hR', hRτ, hsem⟩ | ⟨ε', hscp, habt⟩ := ref σₜ σₜ' ε σₛ hR hmem
    · exact Or.inl ⟨σₛ', ε', hR', hRτ, hsem, hback σₛ' σₜ' hR' hQ⟩
    · exact Or.inr ⟨ε', hscp, habt⟩

  /-- A target with no reducing behavior is refined by anything: the empty target set vacates the
  premise, so the pre- and post-relations and both source sets are unconstrained. -/
  protected theorem Terminating.Empty [T : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {semₛ' : Set (α × εₛ)} :
      StrongRefinement.Terminating R S T.Rτ semₛ semₛ' ∅ := by
    rintro _ _ _ _ _ (_|_)

  /-- Doing nothing refines doing nothing: `Relation.Idle` on the source refines `Relation.Idle`
  on the target, at any aborting set. -/
  protected theorem Terminating.Id [T : Trace εₛ εₜ] {X} :
      StrongRefinement.Terminating R R T.Rτ Relation.Idle X Relation.Idle := by
    rintro σₜ σₜ' ε σₛ σₛRσₜ ⟨rfl, rfl⟩
    left
    exact ⟨σₛ, 1, σₛRσₜ, T.Rτ_one, rfl, rfl⟩

  /-- `⋃₀` on all three sets: every target reducing set in `B` is refined by some source reducing
  set in `A` and some source aborting set in `C`. -/
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

  /-- Binary union on the reducing sets, aborting set shared and summands paired positionally.
  The two-element case of `Terminating.sup`. -/
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

  /-- Terminating refinement for `Relation.star`: from a step-level refinement that answers one
  target step with a source `Relation.star semₛ` run, a refinement of `Relation.star semₜ` with
  aborting set `Relation.star semₛ ∘ᵣ₁ Yₛ`. The operator-preservation law standing in for induction
  over `Algebra.reducing`'s least fixed point.

  The hypothesis answers a target step with a source *run*, not a source step, so a pass whose
  target has steps with no source counterpart still fits it by instantiating `semₛ` at a `star`;
  `Terminating.starStutter` packages that instantiation. -/
  protected theorem Terminating.star {R : Rel α β} [T : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {Yₛ : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)}
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ (Relation.star semₛ ∘ᵣ₁ Yₛ) semₜ) :
        StrongRefinement.Terminating R R T.Rτ (Relation.star semₛ) (Relation.star semₛ ∘ᵣ₁ Yₛ)
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
          · exact Relation.star.lcomp₁_absorb (Relation.lcomp₁.intro hmem' hmem'')
      · refine Or.inr ⟨ea, ?_, hea_mem⟩
        rw [Monoid.partialProd_succ' ets n]
        apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
        apply Trace.scPrefix_rmul_left T.Rτ_total hea

  /-- `Terminating.star` with the source instantiated at `Relation.star stepₛ` and the resulting
  doubled star collapsed, so a target step is answered by a source run — possibly empty — and the
  conclusion still reads at `Relation.star stepₛ`. -/
  protected theorem Terminating.starStutter {R : Rel α β} [T : Trace εₛ εₜ]
      {stepₛ : Set (α × εₛ × α)} {Yₛ : Set (α × εₛ)} {stepₜ : Set (β × εₜ × β)}
      (ref : StrongRefinement.Terminating R R T.Rτ (Relation.star stepₛ)
        (Relation.star stepₛ ∘ᵣ₁ Yₛ) stepₜ) :
        StrongRefinement.Terminating R R T.Rτ (Relation.star stepₛ) (Relation.star stepₛ ∘ᵣ₁ Yₛ)
          (Relation.star stepₜ) := by
    have ref' : StrongRefinement.Terminating R R T.Rτ (Relation.star stepₛ)
        (Relation.star (Relation.star stepₛ) ∘ᵣ₁ Yₛ) stepₜ := by rwa [Relation.star.star_eq]
    have h := Terminating.star ref'
    rwa [Relation.star.star_eq] at h

  /--
    Behavior refinement for a target run that diverges.

    From `R σₛ σₜ` and a diverging `semₜ` run `(σₜ, ε)`, the source either diverges too via `semₛ`
    with `Rτ ε' ε`, or aborts via `semₛ'` with `ε' ≼[Rτ] ε`.

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
    \unicode{x21AF} @. \infty
    \end{CD}
    $$
  -/
  @[expose]
  protected def Diverging (semₛ semₛ' : Set (α × εₛ)) (semₜ : Set (β × εₜ)) : Prop :=
    ∀ (σₜ : β) (ε : εₜ) (σₛ : α), R σₛ σₜ → (σₜ, ε) ∈ semₜ →
      (∃ ε' : εₛ, Rτ ε' ε ∧ (σₛ, ε') ∈ semₛ) ∨ (∃ ε' : εₛ, ε' ≼[Rτ] ε ∧ (σₛ, ε') ∈ semₛ')

  /-- Vertical composition: a divergence of the first factor, or a terminating run of the first
  then a divergence of the second, is a divergence of `semₛ'' ∪ semₛ ∘ᵣ₁ semᵤ''` against
  `semₜ'' ∪ semₜ ∘ᵣ₁ semᵥ''`. Aborting set `semₛ' ∪ semₛ ∘ᵣ₁ semᵤ'`. -/
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

  /-- Monotone: widen either source set, shrink the target diverging set. -/
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

  /-- An empty target diverging set is refined by anything. -/
  protected theorem Diverging.Empty [T : Trace εₛ εₜ] {semₛ'' semₛ' : Set (α × εₛ)} :
      StrongRefinement.Diverging R T.Rτ semₛ'' semₛ' ∅ := by
    rintro _ _ _ _ (_|_)

  /-- Divergence refinement for `Relation.omega`, standing in for coinduction. From a step-level
  `Terminating` refinement, a refinement of `Relation.omega semₜ`: the source either keeps pace
  with the target forever, its trace the infinite product related by `Rτ_omega`, or aborts at the
  first index it cannot. The aborting set is fixed to the closed form `Relation.star semₛ ∘ᵣ₁ Yₛ`,
  so its absorption law holds by `Relation.star.lcomp₁_absorb` rather than as a hypothesis. -/
  protected theorem Diverging.omega {R : Rel α β} [ωMonoid εₛ] [ωMonoid εₜ] [T : ωTrace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {Yₛ : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)}
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ (Relation.star semₛ ∘ᵣ₁ Yₛ) semₜ) :
        StrongRefinement.Diverging R T.Rτ (Relation.omega semₛ) (Relation.star semₛ ∘ᵣ₁ Yₛ)
          (Relation.omega semₜ) := by classical
    let semₛ' := Relation.star semₛ ∘ᵣ₁ Yₛ
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
      exact ⟨ωMonoid.ωProd es, T.Rτ_omega es ets (λ i ↦ (hstep_of i (hall i)).2.1),
        σs, es, hσs₀, λ i ↦ (hstep_of i (hall i)).2.2, rfl⟩
    · -- The source gets stuck; take the first index where it does.
      right
      -- The first index at which it gets stuck, as an opaque natural: `Nat.find` itself does not
      -- support the inductions below.
      let m := Nat.find hall
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
            refine Relation.star.lcomp₁_absorb
              (Relation.lcomp₁.intro (b := σs (i + 1)) ?_ ?_)
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
        obtain ⟨r, hr⟩ := ωMonoid.partialProd_dvd ets (m + 1)
        exists Monoid.partialProd es m * ea
        refine ⟨?_, ?_⟩
        · rw [hr, Monoid.partialProd_succ, mul_assoc]
          apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
          apply Trace.scPrefix_rmul_right (hpp m le_rfl)
          apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
          apply Trace.scPrefix_rmul_left T.Rτ_total hea
        · -- `using!`, not `using`: closing needs a local definition unfolded, which the reducible
          -- transparency `using` matches at does not see through.
          simpa only [Nat.zero_add] using! habort m 0 (Nat.zero_add m)

  /-- Divergence refinement for a stuttering source, where instantiating `semₛ` at a `star` is not
  available (`Relation.omega (Relation.star stepₛ) ≤ Relation.omega stepₛ` is false). The
  hypothesis is a stuttering simulation: per target step the source takes one step, or none while
  a well-founded measure `μ` on target configurations strictly drops, or aborts. The idle branch
  requires the target trace to be `1` there — a step the source does not answer must be
  unobservable. -/
  protected theorem Diverging.omegaStutter {R : Rel α β} [ωMonoid εₛ] [ωMonoid εₜ]
      [T : ωTrace εₛ εₜ] {stepₛ : Set (α × εₛ × α)} {Yₛ : Set (α × εₛ)}
      {stepₜ : Set (β × εₜ × β)} {μ : β → ℕ}
      (ref : ∀ (σₜ σₜ' : β) (ε : εₜ) (σₛ : α), R σₛ σₜ → (σₜ, ε, σₜ') ∈ stepₜ →
        (∃ (σₛ' : α) (ε' : εₛ), R σₛ' σₜ' ∧ T.Rτ ε' ε ∧ (σₛ, ε', σₛ') ∈ stepₛ) ∨
        (R σₛ σₜ' ∧ ε = 1 ∧ μ σₜ' < μ σₜ) ∨
        (∃ ε' : εₛ, ε' ≼[T.Rτ] ε ∧ (σₛ, ε') ∈ Relation.star stepₛ ∘ᵣ₁ Yₛ)) :
        StrongRefinement.Diverging R T.Rτ (Relation.omega stepₛ) (Relation.star stepₛ ∘ᵣ₁ Yₛ)
          (Relation.omega stepₜ) := by classical
    let semₛ' := Relation.star stepₛ ∘ᵣ₁ Yₛ
    rintro σₜ ε σₛ R_σₛ_σₜ ⟨σts, ets, hσts₀, hstep, rfl⟩
    subst hσts₀

    -- A real source step over this target index, when one is available at all.
    let moved (i : ℕ) (σ : α) : Prop :=
      ∃ p : α × εₛ, R p.1 (σts (i + 1)) ∧ T.Rτ p.2 (ets i) ∧ (σ, p.2, p.1) ∈ stepₛ
    -- Stepping is preferred; standing still is the fallback, and only ever legitimate because the
    -- measure drops when it happens.
    let cont (i : ℕ) (σ : α) : Prop :=
      moved i σ ∨ (R σ (σts (i + 1)) ∧ ets i = 1 ∧ μ (σts (i + 1)) < μ (σts i))
    let nextp (i : ℕ) (σ : α) : α × εₛ := if h : moved i σ then h.choose else (σ, 1)
    let σs : ℕ → α := Nat.rec σₛ (λ i s ↦ (nextp i s).1)
    let es (i : ℕ) : εₛ := (nextp i (σs i)).2

    have hσs₀ : σs 0 = σₛ := rfl
    have hstep_of : ∀ i, cont i (σs i) →
        R (σs (i + 1)) (σts (i + 1)) ∧ T.Rτ (es i) (ets i) ∧
          ((σs i, es i, σs (i + 1)) ∈ stepₛ ∨ (σs (i + 1) = σs i ∧ es i = 1)) := by
      intro i h
      by_cases hm : moved i (σs i)
      · have hnext : nextp i (σs i) = hm.choose := dif_pos hm
        change R (nextp i (σs i)).1 (σts (i + 1)) ∧ T.Rτ (nextp i (σs i)).2 (ets i) ∧
          ((σs i, (nextp i (σs i)).2, (nextp i (σs i)).1) ∈ stepₛ ∨
            ((nextp i (σs i)).1 = σs i ∧ (nextp i (σs i)).2 = 1))
        rw [hnext]
        exact ⟨hm.choose_spec.1, hm.choose_spec.2.1, .inl hm.choose_spec.2.2⟩
      · have hnext : nextp i (σs i) = (σs i, 1) := dif_neg hm
        change R (nextp i (σs i)).1 (σts (i + 1)) ∧ T.Rτ (nextp i (σs i)).2 (ets i) ∧
          ((σs i, (nextp i (σs i)).2, (nextp i (σs i)).1) ∈ stepₛ ∨
            ((nextp i (σs i)).1 = σs i ∧ (nextp i (σs i)).2 = 1))
        rw [hnext]
        obtain hm' | ⟨hR, hone, -⟩ := h
        · absurd hm
          exact hm'
        · rw [hone]
          exact ⟨hR, T.Rτ_one, .inr ⟨rfl, rfl⟩⟩

    by_cases! hall : ∀ i, cont i (σs i)
    · -- The source keeps up forever, stepping or standing still.
      left
      -- and it cannot stand still forever: each idle index drops `μ`, and `ℕ` is well-founded
      have hinf : ∀ N, ∃ i, N ≤ i ∧ (σs i, es i, σs (i + 1)) ∈ stepₛ := by
        by_contra! hno
        obtain ⟨N, hN⟩ := hno
        have hdrop : ∀ i, N ≤ i → μ (σts (i + 1)) < μ (σts i) := by
          intro i hi
          obtain hm | ⟨-, -, hμ⟩ := hall i
          · absurd hN i hi
            have hnext : nextp i (σs i) = hm.choose := dif_pos hm
            change (σs i, (nextp i (σs i)).2, (nextp i (σs i)).1) ∈ stepₛ
            rw [hnext]
            exact hm.choose_spec.2.2
          · exact hμ
        have hbound : ∀ k, μ (σts (N + k)) + k ≤ μ (σts N) := by
          intro k
          induction k with
          | zero => exact Nat.le_refl _
          | succ k ih =>
            have hd := hdrop (N + k) (Nat.le_add_right N k)
            have heq : N + (k + 1) = N + k + 1 := by omega
            rw [heq]
            omega
        have := hbound (μ (σts N) + 1)
        omega
      exact ⟨ωMonoid.ωProd es, T.Rτ_omega es ets (λ i ↦ (hstep_of i (hall i)).2.1),
        hσs₀ ▸ Relation.omega.of_idle (λ i ↦ (hstep_of i (hall i)).2.2) hinf⟩
    · -- The source gets stuck; take the first index where it does.
      right
      let m := Nat.find hall
      have hm_spec : ¬cont m (σs m) := Nat.find_spec hall
      have hm_min i (hi : i < m) := not_not.mp (Nat.find_min hall hi)

      have hR : ∀ i, i ≤ m → R (σs i) (σts i) := by
        rintro (_ | i) h
        · exact R_σₛ_σₜ
        · exact (hstep_of i (hm_min i h)).1

      -- At `m` neither of `cont`'s disjuncts can be taken, so `ref` reports an abort.
      obtain ⟨σ', e', hR', hRτ', hsem'⟩ | ⟨hR', hone, hμ⟩ | ⟨ea, hea, hea_mem⟩ :=
        ref (σts m) (σts (m + 1)) (ets m) (σs m) (hR m le_rfl) (hstep m)
      · absurd hm_spec
        exact .inl ⟨(σ', e'), hR', hRτ', hsem'⟩
      · absurd hm_spec
        exact .inr ⟨hR', hone, hμ⟩

      -- The abort is reached after `m` indices; `abs` walks it back, and an idle index costs
      -- nothing to walk back since neither the state nor the trace moved there.
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
            have hi' : i < m := by omega
            have hfun : (λ j ↦ es (i + (j + 1))) = (λ j ↦ es (i + 1 + j)) := by
              simp +arith
            have hsplit : Monoid.partialProd (λ j ↦ es (i + j)) (k + 1) * ea
                 = es i * (Monoid.partialProd (λ j ↦ es (i + 1 + j)) k * ea) := by
              simp only [Monoid.partialProd_succ' (λ j ↦ es (i + j)) k, mul_assoc, Nat.add_zero,
                hfun]
            have htail : (σs (i + 1), Monoid.partialProd (λ j ↦ es (i + 1 + j)) k * ea) ∈ semₛ' := by
              apply ih (i + 1)
              omega
            rw [hsplit]
            obtain hs | ⟨hfix, hone⟩ := (hstep_of i (hm_min i hi')).2.2
            · exact Relation.star.lcomp₁_absorb (Relation.lcomp₁.intro (b := σs (i + 1)) hs htail)
            · rwa [hone, one_mul, ← hfix]

        -- And its trace is a sequentially consistent prefix of the target's.
        have hpp : ∀ n, n ≤ m → T.Rτ (Monoid.partialProd es n) (Monoid.partialProd ets n) := by
          intro n hn
          induction n with
          | zero => exact T.Rτ_one
          | succ n ih =>
            apply T.Rτ_closed _ _ _ _ (ih (Nat.le_of_succ_le hn))
            exact (hstep_of n (hm_min n hn)).2.1
        obtain ⟨r, hr⟩ := ωMonoid.partialProd_dvd ets (m + 1)
        exists Monoid.partialProd es m * ea
        refine ⟨?_, ?_⟩
        · rw [hr, Monoid.partialProd_succ, mul_assoc]
          apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
          apply Trace.scPrefix_rmul_right (hpp m le_rfl)
          apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
          apply Trace.scPrefix_rmul_left T.Rτ_total hea
        · -- `using!`, not `using`: closing needs a local definition unfolded, which the reducible
          -- transparency `using` matches at does not see through.
          simpa only [Nat.zero_add] using! habort m 0 (Nat.zero_add m)

  /-- Divergence refinement for `Relation.star semₛ ∘ᵣ₁ Yₛ`: finitely many steps, then a
  divergence. With `Diverging.omega` it covers the general closed form — `gfp (λ x, Y ∪ X ∘ᵣ₁ x)`
  denotes `(X* ∘ᵣ₁ Y) ∪ X^∞`, and `omega` alone would force `Y = ∅`. -/
  protected theorem Diverging.star {R : Rel α β} [T : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {immₛ Yₛ : Set (α × εₛ)}
      {semₜ : Set (β × εₜ × β)} {Yₜ : Set (β × εₜ)}
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ (Relation.star semₛ ∘ᵣ₁ immₛ) semₜ)
      (refY : StrongRefinement.Diverging R T.Rτ Yₛ (Relation.star semₛ ∘ᵣ₁ immₛ) Yₜ) :
        StrongRefinement.Diverging R T.Rτ (Relation.star semₛ ∘ᵣ₁ Yₛ) (Relation.star semₛ ∘ᵣ₁ immₛ)
          (Relation.star semₜ ∘ᵣ₁ Yₜ) := by
    rintro σₜ ε σₛ hR ⟨σₜ', e₁, e₂, ⟨n, σts, ets, h₀, hn, hsteps, rfl⟩, hY, rfl⟩
    dsimp only at h₀ hn
    subst h₀
    induction n generalizing σₛ σts ets with
    | zero =>
      subst hn
      obtain ⟨ε', hRτ, hmem⟩|⟨ε', hscp, hmem⟩ := refY (σts 0) e₂ σₛ hR hY
      · left
        exists ε', by rwa [Monoid.partialProd_zero, one_mul]
        rw [← one_mul ε']
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
          exists e' * ε''
          refine ⟨?_, ?_⟩
          · rw [Monoid.partialProd_succ' ets n, mul_assoc]
            apply T.Rτ_closed _ _ _ _ hRτ' hRτ''
          · obtain ⟨σᵣ, e₃, e₄, hs, hy, rfl⟩ := hmem''
            rw [← mul_assoc]
            apply Relation.lcomp₁.intro (Relation.star.head hmem' hs) hy
        · right
          exists e' * ε''
          refine ⟨?_, ?_⟩
          · rw [Monoid.partialProd_succ' ets n, mul_assoc]
            apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
            apply Trace.scPrefix_rmul_right hRτ' hscp''
          · exact Relation.star.lcomp₁_absorb (Relation.lcomp₁.intro hmem' hmem'')
      · right
        refine ⟨ea, ?_, hea_mem⟩
        rw [Monoid.partialProd_succ' ets n, mul_assoc]
        apply Trace.scPrefix_mono T.Rτ_closed.rmul_le
        apply Trace.scPrefix_rmul_left T.Rτ_total hea

  /-- Binary union on the diverging sets, aborting set shared. -/
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
  refines it as such. `Diverging.omega` is the `Y = ∅` special case. -/
  protected theorem Diverging.closedForm {R : Rel α β} [ωMonoid εₛ] [ωMonoid εₜ]
      [T : ωTrace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {immₛ Yₛ : Set (α × εₛ)}
      {semₜ : Set (β × εₜ × β)} {Yₜ : Set (β × εₜ)}
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ (Relation.star semₛ ∘ᵣ₁ immₛ) semₜ)
      (refY : StrongRefinement.Diverging R T.Rτ Yₛ (Relation.star semₛ ∘ᵣ₁ immₛ) Yₜ) :
        StrongRefinement.Diverging R T.Rτ (Relation.star semₛ ∘ᵣ₁ Yₛ ∪ Relation.omega semₛ)
          (Relation.star semₛ ∘ᵣ₁ immₛ)
          (Relation.star semₜ ∘ᵣ₁ Yₜ ∪ Relation.omega semₜ) := by
    apply Diverging.union
    · exact Diverging.star ref refY
    · exact Diverging.omega ref

  /--
    Behavior refinement for a target run that aborts.

    From `R σₛ σₜ` and an aborting `semₜ'` run `(σₜ, ε)`, the source aborts too via `semₛ'` with
    `ε' ≼[Rτ] ε`. No bottom edge — an abort has no "after".

    $$
    \begin{CD}
    \sigma_s @>R>> \sigma_t \\
    @V{\mathit{sem}_s'}V{\varepsilon' \preceq \varepsilon}V @V{\mathit{sem}_t'}V{\varepsilon}V \\
    \unicode{x21AF} @. \unicode{x21AF}
    \end{CD}
    $$
  -/
  @[expose]
  protected def Aborting (semₛ' : Set (α × εₛ)) (semₜ' : Set (β × εₜ)) : Prop :=
    ∀ (σₜ : β) (ε : εₜ) (σₛ : α), R σₛ σₜ → (σₜ, ε) ∈ semₜ' → ∃ ε' : εₛ, ε' ≼[Rτ] ε ∧ (σₛ, ε') ∈ semₛ'

  /-- An abort is a divergence that always takes the aborting branch; the reducing set is
  unconstrained. `hle` places the witness in whichever aborting set the diverging statement carries. -/
  protected theorem Aborting.toDiverging {R : Rel α β} [T : Trace εₛ εₜ]
      {semₛ semₛ' semₛ'' : Set (α × εₛ)} {semₜ' : Set (β × εₜ)}
      (h : StrongRefinement.Aborting R T.Rτ semₛ' semₜ') (hle : semₛ' ≤ semₛ'') :
        StrongRefinement.Diverging R T.Rτ semₛ semₛ'' semₜ' := by
    intro σₜ ε σₛ hR hmem
    obtain ⟨ε', hscp, h'⟩ := h σₜ ε σₛ hR hmem
    exact Or.inr ⟨ε', hscp, hle h'⟩

  /-- The converse of `Aborting.toDiverging` when the two source sets coincide: the matched branch
  weakens into the aborting one, so the disjunction collapses. -/
  protected theorem Diverging.toAborting {R : Rel α β} [T : Trace εₛ εₜ] {semₛ' : Set (α × εₛ)}
      {semₜ' : Set (β × εₜ)} (h : StrongRefinement.Diverging R T.Rτ semₛ' semₛ' semₜ') :
        StrongRefinement.Aborting R T.Rτ semₛ' semₜ' := by
    intro σₜ ε σₛ hR hmem
    obtain ⟨ε', hRτ, h'⟩|⟨ε', hscp, h'⟩ := h σₜ ε σₛ hR hmem
    · exact ⟨ε', Trace.scPrefix_of hRτ, h'⟩
    · exact ⟨ε', hscp, h'⟩

  /-- Horizontal composition through an intermediate language with trace type `εₘ`. The first leg's
  trace relation must be left-total and closed (bundled as `T₁`); the second leg's needs nothing. -/
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

  /-- Horizontal composition through an intermediate language, `Terminating.Trans` for divergence:
  only the first leg's trace relation needs laws (bundled as `T₁`). -/
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

  /-- Vertical composition: an abort of the first factor, or a terminating run of the first then an
  abort of the second, is an abort of `semₛ' ∪ semₛ ∘ᵣ₁ semᵤ'` against `semₜ' ∪ semₜ ∘ᵣ₁ semᵥ'`. -/
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

  /-- Horizontal composition through an intermediate language, `Terminating.Trans` for aborts. -/
  protected theorem Aborting.Trans {γ} {εₘ : Type _} [Monoid εₘ] {R₁ R₂} [T₁ : Trace εₛ εₘ] [T₂ : Trace εₘ εₜ]
    {semₛ' : Set (α × εₛ)} {semₜ' : Set (β × εₘ)} {semᵤ' : Set (γ × εₜ)} :
      StrongRefinement.Aborting R₁ T₁.Rτ semₛ' semₜ' →
      StrongRefinement.Aborting R₂ T₂.Rτ semₜ' semᵤ' →
      StrongRefinement.Aborting (Relation.Comp R₁ R₂) (T₁.Rτ ∘ᵣ T₂.Rτ) semₛ' semᵤ' := by
    rintro ref₁ ref₂ σᵤ ε σₛ ⟨σₜ, R₁_σₛ_σₜ, R₂_σₜ_σᵤ⟩ sem_σᵤ
    obtain ⟨εₘ', εₘ'_scp_ε, sem_σₜ⟩ := ref₂ σᵤ ε σₜ R₂_σₜ_σᵤ sem_σᵤ
    obtain ⟨εₛ', εₛ'_scp_εₘ', sem_σₛ⟩ := ref₁ σₜ εₘ' σₛ R₁_σₛ_σₜ sem_σₜ
    exact ⟨εₛ', Trace.scPrefix_rcomp T₁.Rτ_total T₁.Rτ_closed εₛ'_scp_εₘ' εₘ'_scp_ε, sem_σₛ⟩

  /-- Monotone: widen the source aborting set, shrink the target aborting set. -/
  protected theorem Aborting.Mono {R} [T : Trace εₛ εₜ]
    {semᵣ' semₛ' : Set (α × εₛ)} {semₜ' semᵤ' : Set (β × εₜ)}
    (hyp : semₛ' ≤ semᵣ') (concl : semᵤ' ≤ semₜ') :
      StrongRefinement.Aborting R T.Rτ semₛ' semₜ' ≤
        StrongRefinement.Aborting R T.Rτ semᵣ' semᵤ' := by
    intros ref σᵤ' ε σᵣ' R_σᵣ'_σᵤ' sem_σᵤ'
    obtain ⟨ε', ε'_scp_ε, sem_σₛ'⟩ := ref _ _ _ R_σᵣ'_σᵤ' (Set.mem_of_subset_of_mem concl sem_σᵤ')
    exact ⟨ε', ε'_scp_ε, Set.mem_of_subset_of_mem hyp sem_σₛ'⟩

  /-- An empty target aborting set is refined by anything. -/
  protected theorem Aborting.Empty [T : Trace εₛ εₜ] {semₛ' : Set (α × εₛ)} :
      StrongRefinement.Aborting R T.Rτ semₛ' ∅ := by
    rintro _ _ _ _ (_|_)

  /-- `⋃₀` on both sets: every target aborting set in `B` is refined by some source aborting set
  in `A`. -/
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

  /-- Binary union on both aborting sets, summands paired positionally. The two-element case of
  `Aborting.sup`. -/
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

  /-- Aborting refinement for `Relation.star semₛ ∘ᵣ₁ Yₛ`: finitely many steps, then an abort —
  the shape of `Algebra.aborting` (`step* ∘ᵣ₁ immediate`). The operator-preservation law standing
  in for induction over its least fixed point.

  The step-level hypothesis names `Relation.star semₛ ∘ᵣ₁ Yₛ` as its aborting set — the
  conclusion's own left-hand side. Not circular: its absorption law holds by
  `Relation.star.lcomp₁_absorb`, so it is not an added assumption. -/
  protected theorem Aborting.star {R : Rel α β} [T : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {Yₛ : Set (α × εₛ)}
      {semₜ : Set (β × εₜ × β)} {Yₜ : Set (β × εₜ)}
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ (Relation.star semₛ ∘ᵣ₁ Yₛ) semₜ)
      (refY : StrongRefinement.Aborting R T.Rτ Yₛ Yₜ) :
        StrongRefinement.Aborting R T.Rτ (Relation.star semₛ ∘ᵣ₁ Yₛ)
          (Relation.star semₜ ∘ᵣ₁ Yₜ) :=
    StrongRefinement.Diverging.toAborting <|
      StrongRefinement.Diverging.star ref (refY.toDiverging Relation.star.le_lcomp₁)

  /-- `Aborting.star` with the source instantiated at `Relation.star stepₛ` and the doubled star
  collapsed, so a target step is answered by a source run and the conclusion still reads at
  `Relation.star stepₛ ∘ᵣ₁ Yₛ`. -/
  protected theorem Aborting.starStutter {R : Rel α β} [T : Trace εₛ εₜ]
      {stepₛ : Set (α × εₛ × α)} {Yₛ : Set (α × εₛ)}
      {stepₜ : Set (β × εₜ × β)} {Yₜ : Set (β × εₜ)}
      (ref : StrongRefinement.Terminating R R T.Rτ (Relation.star stepₛ)
        (Relation.star stepₛ ∘ᵣ₁ Yₛ) stepₜ)
      (refY : StrongRefinement.Aborting R T.Rτ Yₛ Yₜ) :
        StrongRefinement.Aborting R T.Rτ (Relation.star stepₛ ∘ᵣ₁ Yₛ)
          (Relation.star stepₜ ∘ᵣ₁ Yₜ) := by
    have ref' : StrongRefinement.Terminating R R T.Rτ (Relation.star stepₛ)
        (Relation.star (Relation.star stepₛ) ∘ᵣ₁ Yₛ) stepₜ := by
      rwa [Relation.star.star_eq]
    have h := Aborting.star ref' refY
    rwa [Relation.star.star_eq] at h

  /--
    Behavior refinement for a target run that blocks: a finite run ending in a configuration that
    is stuck — nothing steps, nothing aborts — and is not terminal.

    From `R σₛ σₜ` and a blocking `semₜ_blk` run `(σₜ, ε)`, the source either blocks too via
    `semₛ_blk` with `Rτ ε' ε`, or aborts via `semₛ_abt` with `ε' ≼[Rτ] ε`. `∅` marks the stuck
    configuration; no bottom edge.

    $$
    \begin{CD}
    \sigma_s @>R>> \sigma_t \\
    @V{\mathit{sem}_s}V{\varepsilon'}V @V{\mathit{sem}_t}V{\varepsilon}V \\
    \emptyset @. \emptyset
    \end{CD}
    $$
    or
    $$
    \begin{CD}
    \sigma_s @>R>> \sigma_t \\
    @V{\mathit{sem}_s'}V{\varepsilon' \preceq \varepsilon}V @V{\mathit{sem}_t}V{\varepsilon}V \\
    \unicode{x21AF} @. \emptyset
    \end{CD}
    $$
  -/
  @[expose]
  protected def Blocking (semₛ_blk semₛ_abt : Set (α × εₛ)) (semₜ_blk : Set (β × εₜ)) : Prop :=
    ∀ (σₜ : β) (ε : εₜ) (σₛ : α), R σₛ σₜ → (σₜ, ε) ∈ semₜ_blk →
      (∃ ε' : εₛ, Rτ ε' ε ∧ (σₛ, ε') ∈ semₛ_blk) ∨ (∃ ε' : εₛ, ε' ≼[Rτ] ε ∧ (σₛ, ε') ∈ semₛ_abt)

  /-- Vertical composition: a blocking run of the second factor after a terminating run of the
  first is a blocking run of the sequence, with the aborting sets as shared fallback. Same
  conclusion shape as `Diverging.Comp`. -/
  protected theorem Blocking.Comp {R} [T₂ : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {semₛ_blk semₛ_abt semᵤ_blk semᵤ_abt : Set (α × εₛ)}
      {semₜ : Set (β × εₜ × β)} {semₜ_blk semᵥ_blk : Set (β × εₜ)} :
      StrongRefinement.Blocking R T₂.Rτ semₛ_blk semₛ_abt semₜ_blk →
      StrongRefinement.Blocking R T₂.Rτ semᵤ_blk semᵤ_abt semᵥ_blk →
      StrongRefinement.Terminating R R T₂.Rτ semₛ semₛ_abt semₜ →
      StrongRefinement.Blocking R T₂.Rτ (semₛ_blk ∪ semₛ ∘ᵣ₁ semᵤ_blk) (semₛ_abt ∪ semₛ ∘ᵣ₁ semᵤ_abt)
        (semₜ_blk ∪ semₜ ∘ᵣ₁ semᵥ_blk) :=
    StrongRefinement.Diverging.Comp

  /-- Horizontal composition through an intermediate language: a blocking run of the composite pass
  is matched by a blocking run of the first leg, with an abort of the middle language as fallback. -/
  protected theorem Blocking.Trans {γ} {εₘ : Type _} [Monoid εₘ] {R₁ R₂} [T₁ : Trace εₛ εₘ] [T₂ : Trace εₘ εₜ]
      {semₛ_blk semₛ_abt : Set (α × εₛ)} {semₜ_blk semₜ_abt : Set (β × εₘ)} {semᵤ_blk : Set (γ × εₜ)} :
      StrongRefinement.Blocking R₁ T₁.Rτ semₛ_blk semₛ_abt semₜ_blk →
      StrongRefinement.Aborting R₁ T₁.Rτ semₛ_abt semₜ_abt →
      StrongRefinement.Blocking R₂ T₂.Rτ semₜ_blk semₜ_abt semᵤ_blk →
      StrongRefinement.Blocking (Relation.Comp R₁ R₂) (T₁.Rτ ∘ᵣ T₂.Rτ) semₛ_blk semₛ_abt semᵤ_blk :=
    StrongRefinement.Diverging.Trans

  /-- Monotone: widen either source set or shrink the target blocking set. -/
  protected theorem Blocking.Mono {R} [T : Trace εₛ εₜ]
      {semᵣ_blk semᵣ_abt semₛ_blk semₛ_abt : Set (α × εₛ)} {semₜ_blk semᵤ_blk : Set (β × εₜ)}
      (hyp₁ : semₛ_blk ≤ semᵣ_blk) (hyp₂ : semₛ_abt ≤ semᵣ_abt) (concl : semᵤ_blk ≤ semₜ_blk) :
        StrongRefinement.Blocking R T.Rτ semₛ_blk semₛ_abt semₜ_blk ≤
          StrongRefinement.Blocking R T.Rτ semᵣ_blk semᵣ_abt semᵤ_blk :=
    StrongRefinement.Diverging.Mono hyp₁ hyp₂ concl

  /-- An empty target blocking set is refined by anything. -/
  protected theorem Blocking.Empty [T : Trace εₛ εₜ] {semₛ_blk semₛ_abt : Set (α × εₛ)} :
      StrongRefinement.Blocking R T.Rτ semₛ_blk semₛ_abt ∅ :=
    StrongRefinement.Diverging.Empty R

  /-- Binary union on the blocking sets, aborting set shared. -/
  protected theorem Blocking.union {R : Rel α β} [T : Trace εₛ εₜ]
      {Aₛ Bₛ semₛ_abt : Set (α × εₛ)} {Aₜ Bₜ : Set (β × εₜ)}
      (h₁ : StrongRefinement.Blocking R T.Rτ Aₛ semₛ_abt Aₜ)
      (h₂ : StrongRefinement.Blocking R T.Rτ Bₛ semₛ_abt Bₜ) :
        StrongRefinement.Blocking R T.Rτ (Aₛ ∪ Bₛ) semₛ_abt (Aₜ ∪ Bₜ) :=
    StrongRefinement.Diverging.union h₁ h₂

  /-- Blocking refinement distributes over an arbitrary union of target blocking sets: each target
  summand is matched by a source blocking set and a source aborting set of its own. -/
  protected theorem Blocking.sup [T : Trace εₛ εₜ]
      {A : Set (Set (α × εₛ))} {B : Set (Set (β × εₜ))} {C : Set (Set (α × εₛ))}
      (sup : ∀ y ∈ B, ∃ x ∈ A, ∃ z ∈ C, StrongRefinement.Blocking R T.Rτ x z y) :
        StrongRefinement.Blocking R T.Rτ (⋃₀ A) (⋃₀ C) (⋃₀ B) := by
    intro σₜ ε σₛ R_σₛ_σₜ block_σₜ
    rw [Set.mem_sUnion] at block_σₜ
    obtain ⟨blockₜ, blockₜ_in_B, block_σₜ⟩ := block_σₜ
    obtain ⟨blockₛ, blockₛ_in_A, abortₛ, abortₛ_in_C, ref⟩ := sup _ blockₜ_in_B
    obtain ⟨ε', Rτ_ε'_ε, block_σₛ⟩|⟨ε', ε'_scp_ε, abort_σₛ⟩ := ref σₜ ε σₛ R_σₛ_σₜ block_σₜ
    · left
      exists ε', Rτ_ε'_ε
      exact Set.mem_sUnion_of_mem block_σₛ blockₛ_in_A
    · right
      exists ε', ε'_scp_ε
      exact Set.mem_sUnion_of_mem abort_σₛ abortₛ_in_C

  /-- Blocking refinement for `Relation.star semₛ ∘ᵣ₁ Yₛ`: finitely many steps, then a block — the
  shape of an algorithm's blocking semantics (`step* ∘ᵣ₁ immediateBlock`). Operator-preservation
  standing in for induction over its least fixed point; same conclusion shape as `Diverging.star`. -/
  protected theorem Blocking.star {R : Rel α β} [T : Trace εₛ εₜ]
      {semₛ : Set (α × εₛ × α)} {immₛ Yₛ : Set (α × εₛ)}
      {semₜ : Set (β × εₜ × β)} {Yₜ : Set (β × εₜ)}
      (ref : StrongRefinement.Terminating R R T.Rτ semₛ (Relation.star semₛ ∘ᵣ₁ immₛ) semₜ)
      (refY : StrongRefinement.Blocking R T.Rτ Yₛ (Relation.star semₛ ∘ᵣ₁ immₛ) Yₜ) :
        StrongRefinement.Blocking R T.Rτ (Relation.star semₛ ∘ᵣ₁ Yₛ) (Relation.star semₛ ∘ᵣ₁ immₛ)
          (Relation.star semₜ ∘ᵣ₁ Yₜ) :=
    StrongRefinement.Diverging.star ref refY

  /-- `Blocking.star` with the source instantiated at `Relation.star stepₛ` and the doubled star
  collapsed, so a target step is answered by a source run and the conclusion still reads at
  `Relation.star stepₛ ∘ᵣ₁ Yₛ`. -/
  protected theorem Blocking.starStutter {R : Rel α β} [T : Trace εₛ εₜ]
      {stepₛ : Set (α × εₛ × α)} {immₛ Yₛ : Set (α × εₛ)}
      {stepₜ : Set (β × εₜ × β)} {Yₜ : Set (β × εₜ)}
      (ref : StrongRefinement.Terminating R R T.Rτ (Relation.star stepₛ)
        (Relation.star stepₛ ∘ᵣ₁ immₛ) stepₜ)
      (refY : StrongRefinement.Blocking R T.Rτ Yₛ (Relation.star stepₛ ∘ᵣ₁ immₛ) Yₜ) :
        StrongRefinement.Blocking R T.Rτ (Relation.star stepₛ ∘ᵣ₁ Yₛ)
          (Relation.star stepₛ ∘ᵣ₁ immₛ) (Relation.star stepₜ ∘ᵣ₁ Yₜ) := by
    have ref' : StrongRefinement.Terminating R R T.Rτ (Relation.star stepₛ)
        (Relation.star (Relation.star stepₛ) ∘ᵣ₁ immₛ) stepₜ := by
      rwa [Relation.star.star_eq]
    have refY' : StrongRefinement.Blocking R T.Rτ Yₛ
        (Relation.star (Relation.star stepₛ) ∘ᵣ₁ immₛ) Yₜ := by
      rwa [Relation.star.star_eq]
    have h := Blocking.star ref' refY'
    rwa [Relation.star.star_eq] at h

end StrongRefinement

/--
  All four behavior refinements for one pass, sharing the pre-relation `R` and trace relation `Rτ`.
  The aborting sets `semₛ₂`/`semₜ₂` are the fallback for the `terminating`, `diverging` and
  `blocking` components alike; `semₛ₁`/`semₜ₁` reduce, `semₛ₃`/`semₜ₃` diverge, `semₛ₄`/`semₜ₄`
  block.
-/
structure StrongRefinement {εₛ εₜ : Type _} [Monoid εₛ] [Monoid εₜ] {α β : Type _} (R : Rel α β)
    (Rτ : Rel εₛ εₜ)
    (semₛ₁ : Set (α × εₛ × α)) (semₛ₂ semₛ₃ : Set (α × εₛ))
    (semₜ₁ : Set (β × εₜ × β)) (semₜ₂ semₜ₃ : Set (β × εₜ))
    (semₛ₄ : Set (α × εₛ)) (semₜ₄ : Set (β × εₜ)) where
  terminating : StrongRefinement.Terminating R R Rτ semₛ₁ semₛ₂ semₜ₁
  aborting : StrongRefinement.Aborting R Rτ semₛ₂ semₜ₂
  diverging : StrongRefinement.Diverging R Rτ semₛ₃ semₛ₂ semₜ₃
  blocking : StrongRefinement.Blocking R Rτ semₛ₄ semₛ₂ semₜ₄

namespace StrongRefinement
  variable {εₛ εₜ : Type _} [Monoid εₛ] [Monoid εₜ] {α β : Type _} (R S : Rel α β)

  /-- Vertical composition of two full refinements, staying at the trace relation `Rτ`. Composing a
  chain stays at `Rτ` however long the chain. -/
  protected theorem Comp [T₂ : Trace εₛ εₜ]
    {semₛ semᵤ : Set (α × εₛ × α)} {semₛ' semₛ'' semₛb semᵤ' semᵤ'' semᵤb : Set (α × εₛ)} {semₜ semᵥ : Set (β × εₜ × β)} {semₜ' semₜ'' semₜb semᵥ' semᵥ'' semᵥb : Set (β × εₜ)} :
      StrongRefinement R T₂.Rτ semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' semₛb semₜb →
      StrongRefinement R T₂.Rτ semᵤ semᵤ' semᵤ'' semᵥ semᵥ' semᵥ'' semᵤb semᵥb →
      StrongRefinement R T₂.Rτ (semₛ ∘ᵣ₂ semᵤ) (semₛ' ∪ semₛ ∘ᵣ₁ semᵤ') (semₛ'' ∪ semₛ ∘ᵣ₁ semᵤ'') (semₜ ∘ᵣ₂ semᵥ) (semₜ' ∪ semₜ ∘ᵣ₁ semᵥ') (semₜ'' ∪ semₜ ∘ᵣ₁ semᵥ'') (semₛb ∪ semₛ ∘ᵣ₁ semᵤb) (semₜb ∪ semₜ ∘ᵣ₁ semᵥb) := by
    rintro ⟨t₁, a₁, d₁, b₁⟩ ⟨t₂, a₂, d₂, b₂⟩
    exact ⟨Terminating.Comp t₁ t₂, Aborting.Comp a₁ a₂ t₁, Diverging.Comp d₁ d₂ t₁, Blocking.Comp b₁ b₂ t₁⟩

  /-- A full refinement from just the terminating and aborting components, with the target
  diverging and blocking sets empty. -/
  protected theorem ofNonDiverging [T : Trace εₛ εₜ] {semₛ : Set (α × εₛ × α)} {semₛ' semₛ'' semₛ''' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)} {semₜ' : Set (β × εₜ)}
    (h₁ : StrongRefinement.Terminating R R T.Rτ semₛ semₛ' semₜ)
    (h₂ : StrongRefinement.Aborting R T.Rτ semₛ' semₜ') :
      StrongRefinement R T.Rτ semₛ semₛ' semₛ'' semₜ semₜ' ∅ semₛ''' ∅ := by
    constructor
    · assumption
    · assumption
    · apply Diverging.Empty
    · apply Blocking.Empty

  /-- A full refinement from just the terminating component, with every other target set empty. -/
  protected theorem ofTerminating [T : Trace εₛ εₜ] {semₛ : Set (α × εₛ × α)} {semₛ' semₛ'' semₛ''' : Set (α × εₛ)} {semₜ : Set (β × εₜ × β)}
    (h : StrongRefinement.Terminating R R T.Rτ semₛ semₛ' semₜ) :
      StrongRefinement R T.Rτ semₛ semₛ' semₛ'' semₜ ∅ ∅ semₛ''' ∅ := by
    constructor
    · assumption
    · apply Aborting.Empty
    · apply Diverging.Empty
    · apply Blocking.Empty

  /-- Horizontal composition of two full refinements through an intermediate language. `T₁` bundles
  the first leg's trace relation and its laws. No union in the conclusion, unlike `Comp`: every run
  passes through the middle language. -/
  protected theorem Trans {γ} {εₘ : Type _} [Monoid εₘ] [T₁ : Trace εₛ εₘ] {R₁ R₂} [T₂ : Trace εₘ εₜ]
    {semₛ : Set (α × εₛ × α)} {semₛ' semₛ'' semₛb : Set (α × εₛ)}
    {semₜ : Set (β × εₘ × β)} {semₜ' semₜ'' semₜb : Set (β × εₘ)}
    {semᵤ : Set (γ × εₜ × γ)} {semᵤ' semᵤ'' semᵤb : Set (γ × εₜ)} :
      StrongRefinement R₁ T₁.Rτ semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' semₛb semₜb →
      StrongRefinement R₂ T₂.Rτ semₜ semₜ' semₜ'' semᵤ semᵤ' semᵤ'' semₜb semᵤb →
      StrongRefinement (Relation.Comp R₁ R₂) (T₁.Rτ ∘ᵣ T₂.Rτ) semₛ semₛ' semₛ'' semᵤ semᵤ' semᵤ'' semₛb semᵤb := by
    rintro ⟨ref₁_red, ref₁_abort, ref₁_div, ref₁_blk⟩ ⟨ref₂_red, ref₂_abort, ref₂_div, ref₂_blk⟩
    constructor
    · exact Terminating.Trans ref₁_red ref₁_abort ref₂_red
    · exact Aborting.Trans ref₁_abort ref₂_abort
    · exact Diverging.Trans ref₁_div ref₁_abort ref₂_div
    · exact Blocking.Trans ref₁_blk ref₁_abort ref₂_blk

  /-- Monotone in all eight state sets: widen the four source sets, shrink the four target sets. -/
  protected theorem Mono {R} [T : Trace εₛ εₜ]
    {semᵣ semₛ : Set (α × εₛ × α)} {semᵣ' semᵣ'' semᵣb semₛ' semₛ'' semₛb : Set (α × εₛ)} {semₜ semᵤ : Set (β × εₜ × β)} {semₜ' semₜ'' semₜb semᵤ' semᵤ'' semᵤb : Set (β × εₜ)}
    (hyp₁ : semₛ ≤ semᵣ) (hyp₂ : semₛ' ≤ semᵣ') (hyp₃ : semₛ'' ≤ semᵣ'') (hyp₄ : semₛb ≤ semᵣb) (concl₁ : semᵤ ≤ semₜ) (concl₂ : semᵤ' ≤ semₜ') (concl₃ : semᵤ'' ≤ semₜ'') (concl₄ : semᵤb ≤ semₜb) :
      StrongRefinement R T.Rτ semₛ semₛ' semₛ'' semₜ semₜ' semₜ'' semₛb semₜb ≤
        StrongRefinement R T.Rτ semᵣ semᵣ' semᵣ'' semᵤ semᵤ' semᵤ'' semᵣb semᵤb := by
    rintro ⟨ref₁, ref₂, ref₃, ref₄⟩
    constructor
    · apply Terminating.Mono hyp₁ hyp₂ concl₁ ref₁
    · apply Aborting.Mono hyp₂ concl₂ ref₂
    · apply Diverging.Mono hyp₃ hyp₂ concl₃ ref₃
    · apply Blocking.Mono hyp₄ hyp₂ concl₄ ref₄

  /-- Assembles per-step refinements into a full `StrongRefinement` at the shapes a step-and-iterate
  semantics takes: `step*`, `step* ∘ᵣ₁ immediate`, `(step* ∘ᵣ₁ Y) ∪ step^∞`,
  `step* ∘ᵣ₁ blocking`. Standing in for induction over `Algebra`'s fixed points.

  Four hypotheses, each about one step: a `Terminating` for the step, and `Aborting`/`Diverging`/
  `Blocking` for the sets a step can abort, diverge or block into. `Yₛ`/`Yₜ` are the
  immediate-divergence sets — general because whether a step can diverge is a property of the
  semantics, not this framework. `sequentialOmega` is the `Y = ∅` case that `Algebra` uses. -/
  protected theorem sequential [ωMonoid εₛ] [ωMonoid εₜ] [T : ωTrace εₛ εₜ] {R : Rel α β}
      {stepₛ : Set (α × εₛ × α)} {immₛ Yₛ blkₛ : Set (α × εₛ)}
      {stepₜ : Set (β × εₜ × β)} {immₜ Yₜ blkₜ : Set (β × εₜ)}
      (ref : StrongRefinement.Terminating R R T.Rτ stepₛ (Relation.star stepₛ ∘ᵣ₁ immₛ) stepₜ)
      (refImm : StrongRefinement.Aborting R T.Rτ immₛ immₜ)
      (refY : StrongRefinement.Diverging R T.Rτ Yₛ (Relation.star stepₛ ∘ᵣ₁ immₛ) Yₜ)
      (refBlk : StrongRefinement.Blocking R T.Rτ blkₛ (Relation.star stepₛ ∘ᵣ₁ immₛ) blkₜ) :
        StrongRefinement R T.Rτ
          (Relation.star stepₛ) (Relation.star stepₛ ∘ᵣ₁ immₛ)
          (Relation.star stepₛ ∘ᵣ₁ Yₛ ∪ Relation.omega stepₛ)
          (Relation.star stepₜ) (Relation.star stepₜ ∘ᵣ₁ immₜ)
          (Relation.star stepₜ ∘ᵣ₁ Yₜ ∪ Relation.omega stepₜ)
          (Relation.star stepₛ ∘ᵣ₁ blkₛ) (Relation.star stepₜ ∘ᵣ₁ blkₜ) where
    terminating := Terminating.star ref
    aborting := Aborting.star ref refImm
    diverging := Diverging.closedForm ref refY
    blocking := Blocking.star ref refBlk

  /-- `sequential` at `Y = ∅`, so the diverging component is just `step^∞`. The algorithm layer's
  case — an atomic block has no diverging semantics — where the conclusion is then definitionally
  `Algebra.reducing`/`.aborting`/`.diverging`, applied without rewriting. -/
  protected theorem sequentialOmega [ωMonoid εₛ] [ωMonoid εₜ] [T : ωTrace εₛ εₜ] {R : Rel α β}
      {stepₛ : Set (α × εₛ × α)} {immₛ blkₛ : Set (α × εₛ)}
      {stepₜ : Set (β × εₜ × β)} {immₜ blkₜ : Set (β × εₜ)}
      (ref : StrongRefinement.Terminating R R T.Rτ stepₛ (Relation.star stepₛ ∘ᵣ₁ immₛ) stepₜ)
      (refImm : StrongRefinement.Aborting R T.Rτ immₛ immₜ)
      (refBlk : StrongRefinement.Blocking R T.Rτ blkₛ (Relation.star stepₛ ∘ᵣ₁ immₛ) blkₜ) :
        StrongRefinement R T.Rτ
          (Relation.star stepₛ) (Relation.star stepₛ ∘ᵣ₁ immₛ) (Relation.omega stepₛ)
          (Relation.star stepₜ) (Relation.star stepₜ ∘ᵣ₁ immₜ) (Relation.omega stepₜ)
          (Relation.star stepₛ ∘ᵣ₁ blkₛ) (Relation.star stepₜ ∘ᵣ₁ blkₜ) := by
    have h := StrongRefinement.sequential (Yₛ := ∅) (Yₜ := ∅) ref refImm
      (Diverging.Empty R) refBlk
    rwa [Relation.lcomp₁.right_empty_eq_empty, Set.empty_union,
      Relation.lcomp₁.right_empty_eq_empty, Set.empty_union] at h

end StrongRefinement

end
