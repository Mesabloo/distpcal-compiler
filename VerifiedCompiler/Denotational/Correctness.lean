module

public import VerifiedCompiler.Denotational.StrongRefinement
public import VerifiedCompiler.Denotational.Notations

@[expose] public section

open Std.Do

/-!
  What it means for a compilation pass to be correct: the target's initial states are covered by
  related source ones, and the target's behaviour refines the source's.

  **Both halves live inside one Hoare triple**, over the pass's own monad. They have to: the
  simulation relation and the target's `init` predicate are generally functions of the *compiled*
  program, which exists only under `C x`. `Guarded2Network` is the concrete case — its relation is
  indexed by the mailbox and receiving labels read off the compiled algorithm, and the `inbox` name
  they mention is one the pass invents, so no relation written before the pass runs can name it.
-/

namespace Compiler

/-- **A pass is correct at a named simulation relation.** `R` is indexed by both programs because
that is what a pass generally determines it from — the compiled program above all. `isInit`/`isInit'`
are indexed for the same reason: an algorithm's initial states are a function of the algorithm.

The `init` conjunct is the non-vacuity half. `StrongRefinement` over a relation that never holds is
trivially true, so what gives the second conjunct content is that every initial state of the compiled
program has a related initial state of the source. Stated in that direction — target to source —
because that is the direction a whole-pipeline statement composes along. -/
structure Correctness {α β} {m : Type _ → Type _} {ps} {pₛ pₜ} {εₛ εₜ} [Monad m] [WPMonad m ps]
  [Monoid εₛ] [Monoid εₜ] [inst : Trace εₛ εₜ]
  [Reduce pₛ (Set (α × εₛ × α))] [Abort pₛ (Set (α × εₛ))] [Diverge pₛ (Set (α × εₛ))]
  [Reduce pₜ (Set (β × εₜ × β))] [Abort pₜ (Set (β × εₜ))] [Diverge pₜ (Set (β × εₜ))]
    (R : pₛ → pₜ → Rel α β) (C : pₛ → m pₜ) (isInit : pₛ → α → Prop) (isInit' : pₜ → β → Prop) :
    Prop where
  correct : ∀ x : pₛ, ⦃⌜True⌝⦄ C x ⦃⇓? y =>
    ⌜(∀ s' : β, isInit' y s' → ∃ s : α, isInit x s ∧ R x y s s') ∧
      StrongRefinement (R x y) inst.Rτ ⟦x⟧* ⟦x⟧⊥ ⟦x⟧∞ ⟦y⟧* ⟦y⟧⊥ ⟦y⟧∞⌝⦄

/-- **The same statement with the relation forgotten** — the form that composes.

Two passes chained have no simulation relation that can be *named* in advance: the composite's is
`R₁ x y ∘ᵣ R₂ y z` at the intermediate program `y`, and `y` exists only inside the triple for `C₁ x`.
Nor can it be recovered by quantifying `y` inside the relation: `StrongRefinement` takes its relation
as both the pre- and the post-relation (`Terminating R R …`), so it is monotone in neither direction
and an existential over `y` does not follow from the instance at the true one. Existentially
quantifying the *relation*, inside the triple where both programs are in scope, is what lets the
composition go through, and it loses nothing a caller of a whole-pipeline theorem can use. -/
def Correct {α β} {m : Type _ → Type _} {ps} {pₛ pₜ} {εₛ εₜ} [Monad m] [WPMonad m ps]
  [Monoid εₛ] [Monoid εₜ] [inst : Trace εₛ εₜ]
  [Reduce pₛ (Set (α × εₛ × α))] [Abort pₛ (Set (α × εₛ))] [Diverge pₛ (Set (α × εₛ))]
  [Reduce pₜ (Set (β × εₜ × β))] [Abort pₜ (Set (β × εₜ))] [Diverge pₜ (Set (β × εₜ))]
    (C : pₛ → m pₜ) (isInit : pₛ → α → Prop) (isInit' : pₜ → β → Prop) : Prop :=
  ∀ x : pₛ, ⦃⌜True⌝⦄ C x ⦃⇓? y => ⌜∃ R : Rel α β,
    (∀ s' : β, isInit' y s' → ∃ s : α, isInit x s ∧ R s s') ∧
      StrongRefinement R inst.Rτ ⟦x⟧* ⟦x⟧⊥ ⟦x⟧∞ ⟦y⟧* ⟦y⟧⊥ ⟦y⟧∞⌝⦄

/-- A pass proved correct at a named relation is correct. The only direction there is: coming back
would have to pick the relation out of a postcondition. -/
theorem Correctness.toCorrect {α β} {m : Type _ → Type _} {ps} {pₛ pₜ} {εₛ εₜ} [Monad m]
  [WPMonad m ps] [Monoid εₛ] [Monoid εₜ] [inst : Trace εₛ εₜ]
  [Reduce pₛ (Set (α × εₛ × α))] [Abort pₛ (Set (α × εₛ))] [Diverge pₛ (Set (α × εₛ))]
  [Reduce pₜ (Set (β × εₜ × β))] [Abort pₜ (Set (β × εₜ))] [Diverge pₜ (Set (β × εₜ))]
  {R : pₛ → pₜ → Rel α β} {C : pₛ → m pₜ} {isInit : pₛ → α → Prop} {isInit' : pₜ → β → Prop}
  (h : Correctness R C isInit isInit') : Correct C isInit isInit' := by
  intro x
  mintro -
  mspec h.correct x
  rename pₜ => y
  mframe
  mpure_intro
  exact ⟨R x y, ‹_›⟩

set_option synthInstance.checkSynthOrder false in
set_option allowUnsafeReducibility true in
attribute [local instance, local instance_reducible] Trace.comp in
/-- **Two correct passes compose.** The intermediate program is bound by the first triple, so the
composite's relation — `R₁ ∘ᵣ R₂` at that program — is available exactly where `Correct`'s
existential is discharged, and nowhere earlier. `Trace.comp` carries the trace relation across the
same seam. -/
theorem Correct.comp {α β γ} {m : Type _ → Type _} {ps} {pₛ pₜ pᵤ} {εₛ εₜ εᵤ} [Monad m]
  [WPMonad m ps] [Monoid εₛ] [Monoid εₜ] [Monoid εᵤ] [inst₁ : Trace εₛ εₜ] [inst₂ : Trace εₜ εᵤ]
  [Reduce pₛ (Set (α × εₛ × α))] [Abort pₛ (Set (α × εₛ))] [Diverge pₛ (Set (α × εₛ))]
  [Reduce pₜ (Set (β × εₜ × β))] [Abort pₜ (Set (β × εₜ))] [Diverge pₜ (Set (β × εₜ))]
  [Reduce pᵤ (Set (γ × εᵤ × γ))] [Abort pᵤ (Set (γ × εᵤ))] [Diverge pᵤ (Set (γ × εᵤ))]
  {C₁ : pₛ → m pₜ} {C₂ : pₜ → m pᵤ} {isInit : pₛ → α → Prop} {isInit' : pₜ → β → Prop}
  {isInit'' : pᵤ → γ → Prop} (h₁ : Correct C₁ isInit isInit') (h₂ : Correct C₂ isInit' isInit'') :
    Correct (inst := Trace.comp (εₜ := εₜ)) (C₁ >=> C₂) isInit isInit'' := by
  intro x
  unfold Bind.kleisliRight

  mintro -
  mspec h₁ x
  rename pₜ => y
  mspec h₂ _
  rename pᵤ => z
  mframe
  mpure_intro

  obtain ⟨R₁, init₁, ref₁⟩ := ‹∃ _ : Rel α β, _›
  obtain ⟨R₂, init₂, ref₂⟩ := ‹∃ _ : Rel β γ, _›
  refine ⟨R₁ ∘ᵣ R₂, ?_, StrongRefinement.Trans (T₁ := inst₁) (T₂ := inst₂) ref₁ ref₂⟩
  intro u init_u
  obtain ⟨t, init_t, tR₂u⟩ := init₂ u init_u
  obtain ⟨s, init_s, sR₁t⟩ := init₁ t init_t
  exact ⟨s, init_s, t, sR₁t, tR₂u⟩

end Compiler

end
