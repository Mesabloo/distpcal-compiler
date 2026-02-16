import VerifiedCompiler.Trace
import Mathlib.Logic.Relation
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Set.Basic

inductive Relation.TraceReflGen {α ε} [Trace ε] (R : α → ε → α → Prop) : α → ε → α → Prop
  | refl : ∀ {x}, Relation.TraceReflGen R x Trace.τ x
  | single : ∀ {x y} {a}, R x a y → Relation.TraceReflGen R x a y

inductive Relation.TraceTransGen {α ε} [Trace ε] (R : α → ε → α → Prop) : α → ε → α → Prop
  | single : ∀ {x y} {a}, R x a y → Relation.TraceTransGen R x a y
  | head : ∀ {x y z} {a a'}, R x a y → Relation.TraceTransGen R y a' z → Relation.TraceTransGen R x (a * a') z

theorem Relation.TraceTransGen.no_rel {α ε} [Trace ε] {R : α → ε → α → Prop} {x y a} (h : ∀ y a, ¬ R x a y) : ¬ Relation.TraceTransGen R x a y := by
  intro h₂
  induction h₂ with
  | single xRy => exact h _ _ xRy
  | @head _ y _ a => specialize h y a; contradiction

theorem Relation.TraceTransGen.trans {α ε} [Trace ε] {R : α → ε → α → Prop} {x y z} {a a'} :
  Relation.TraceTransGen R x a y → Relation.TraceTransGen R y a' z → Relation.TraceTransGen R x (a * a') z := by
    intros xRpy yRpz
    induction xRpy with
    | @single x y a xRy => exact head xRy yRpz
    | @head x y z a a'' xRy _ IH => exact (mul_assoc a a'' a').symm ▸ head xRy (IH yRpz)

inductive Relation.TraceReflTransGen {α ε} [Trace ε] (R : α → ε → α → Prop) : α → ε → α → Prop
  | refl : ∀ {x}, Relation.TraceReflTransGen R x Trace.τ x
  | head : ∀ {x} y {z} {a a'}, R x a y → Relation.TraceReflTransGen R y a' z → Relation.TraceReflTransGen R x (a * a') z

protected theorem Relation.TraceReflTransGen.single {α ε} [Trace ε] (R : α → ε → α → Prop) : ∀ {x a} y, R x a y → Relation.TraceReflTransGen R x a y := by
  intros x a y xRy
  rw [← Trace.toCancelMonoid.mul_one a]
  apply Relation.TraceReflTransGen.head
  · exact xRy
  · apply Relation.TraceReflTransGen.refl

theorem Relation.TraceReflTransGen.no_rel_to_eq {α ε} [Trace ε] {R : α → ε → α → Prop} {x y a} (h₁ : ∀ y a, ¬ R x a y) (h₂ : Relation.TraceReflTransGen R x a y) : x = y := by
  induction h₂ with
  | refl => rfl
  | @head x y _ a _ xRy =>
    specialize h₁ y a
    contradiction

theorem Relation.TraceReflTransGen.to_trans_gen {α ε} [Trace ε] {R : α → ε → α → Prop} {x y z} {a a'} :
  R x a y → Relation.TraceReflTransGen R y a' z → Relation.TraceTransGen R x (a * a') z := by
    rintro xRy yRsz
    induction yRsz generalizing x a with
    | refl => exact .single ((append_τ_eq a).symm ▸ xRy)
    | @head x _ z a a' xRy' _ IH => exact .head xRy (IH xRy')

theorem Relation.TraceReflTransGen.trans {α ε} [Trace ε] {R : α → ε → α → Prop} {x y z} {a a'} :
  Relation.TraceReflTransGen R x a y → Relation.TraceReflTransGen R y a' z → Relation.TraceReflTransGen R x (a * a') z := by
    intros xRsy yRsz
    induction xRsy with
    | refl => exact ((τ_append_eq a').symm ▸ yRsz)
    | @head x y z' a a' xRy _ IH =>
      let xRsz := head _ xRy (IH yRsz)
      rwa [← mul_assoc] at xRsz

theorem Relation.TraceTransGen.to_refl_trans_gen {α ε} [Trace ε] {R : α → ε → α → Prop} {x y} {a} :
  Relation.TraceTransGen R x a y → Relation.TraceReflTransGen R x a y := by
    intro xRy
    induction xRy with
    | @single x y a xRy => exact append_τ_eq a ▸ .head _ xRy .refl
    | @head x y z a a' xRy _ IH => exact .head _ xRy IH

theorem Relation.TraceReflTransGen.tail {α ε} [Trace ε] {R : α → ε → α → Prop} {x y z} {a a'} :
  Relation.TraceReflTransGen R x a y → R y a' z → Relation.TraceReflTransGen R x (a * a') z := by
    intros xRsy yRz
    induction xRsy with
    | refl =>
      rw [τ_append_eq, ← append_τ_eq a']
      exact head _ yRz refl
    | head y xRy _ IH =>
      rw [mul_assoc]
      exact head _ xRy (IH yRz)

theorem Relation.TraceReflTransGen.tail_induction_on {α ε} [Trace ε] {R : α → ε → α → Prop} {x : α} {motive : ∀ (z : α) (e : ε), Relation.TraceReflTransGen R x e z → Prop} {z : α} {e : ε}
  (h : Relation.TraceReflTransGen R x e z) (refl : motive x Trace.τ Relation.TraceReflTransGen.refl) (tail : ∀ {y z : α} {e₁ e₂ : ε} (h : Relation.TraceReflTransGen R x e₁ y) (h' : R y e₂ z), motive y e₁ h → motive z (e₁ * e₂) (Relation.TraceReflTransGen.tail h h')) :
  motive z e h := by
    induction h with
    | refl => exact refl
    | @head _ _ _ e₁ _ xRy _ IH =>
      apply IH
      · have : e₁ * Trace.τ = Trace.τ * e₁ := by rw [append_τ_eq, τ_append_eq]
        simp [this]
        exact tail _ xRy refl
      · intros _ _ e₂ e₃ _ h' ih
        have : e₁ * (e₂ * e₃) = e₁ * e₂ * e₃ := mul_assoc _ _ _ |>.symm
        simp [this]
        exact tail _ h' ih

def Relation.iComp {α β δ ι ι'} (R : ι → α → β → Prop) (R' : ι' → β → δ → Prop) : ι × ι' → α → δ → Prop :=
  λ (i, i') => Relation.Comp (R i) (R' i')

theorem Relation.flip_icomp {α β δ ι ι'} {R : ι → α → β → Prop} {R' : ι' → β → δ → Prop}
  : (flip ∘ Relation.iComp R R') = (Relation.iComp (flip ∘ R') (flip ∘ R) ∘ Prod.swap) := by
  funext ⟨i, i'⟩ z x
  dsimp [Relation.iComp]
  rw [Relation.flip_comp]

------

/--
  `Eventually R x P` is the proposition stating that:
  * All possible `R`-chains from `x` are safe (do not get stuck).
  * All possible `R`-chains from `x` eventually reach a value satisfying `P`.
-/
inductive Relation.Eventually {α} (R : α → Set α → Prop) : α → Set α → Prop
  | here {x : α} {P : Set α} : x ∈ P → Relation.Eventually R x P
  | step {x : α} {P : Set α} (P' : Set α) : R x P' → (∀ x' ∈ P', Relation.Eventually R x' P) → Relation.Eventually R x P

theorem Relation.Eventually.wellformed {α} (R : α → Set α → Prop) (R_wf : ∀ x P, R x P → P ≠ ∅) : ∀ x P, Relation.Eventually R x P → P ≠ ∅ := by
  intros x P xReP
  induction xReP with
  | here x_in_P =>
    apply Set.nonempty_iff_ne_empty.mp
    exact Set.nonempty_of_mem x_in_P
  | step P' xRP' _ IH =>
    have P'_non_empty := R_wf _ _ xRP'
    obtain ⟨x', x'_in_P'⟩ := Set.nonempty_iff_ne_empty.mpr P'_non_empty
    exact IH x' x'_in_P'

theorem Relation.Eventually.step_chained {α} {x : α} {R : α → Set α → Prop} {P : Set _} (h : R x {y | Relation.Eventually R y P}) : Relation.Eventually R x P := by
  apply Relation.Eventually.step _ h <;> simp

theorem Relation.Eventually.cut {α} {x : α} {P : Set α} (P' : Set α) {R : α → Set α → Prop} (h : Relation.Eventually R x P') (h' : ∀ y ∈ P', Relation.Eventually R y P) : Relation.Eventually R x P := by
  induction h with
  | @here x P' x_in_P' => exact h' x x_in_P'
  | @step x P'' P' RxP'' _ IH =>
    apply Relation.Eventually.step _ RxP''
    · intro x' x'_in_P''
      exact IH _ x'_in_P'' h'

theorem Relation.Eventually.cut_chained  {α} {x : α} {R : α → Set α → Prop} {P : Set _} (h : Relation.Eventually R x {y | Relation.Eventually R y P}) : Relation.Eventually R x P := by
  apply Relation.Eventually.cut _ h <;> simp

--------

/--
  `Eventually? R x P` is the proposition stating that:
  * All possible `R`-chains from `x` that are `R`-safe eventually reach a value satisfying `P`.
-/
inductive Relation.Eventually? {α} (R : α → Set α → Prop) : α → Set α → Prop
  | here {x : α} {P : Set α} : x ∈ P → Relation.Eventually? R x P
  | step? {x : α} {P : Set α} (P' : Set α) (x' : α) :
    R x P' → x' ∈ P' → Relation.Eventually? R x' P → Relation.Eventually? R x P

theorem Relation.Eventually?.wellformed {α} (R : α → Set α → Prop) : ∀ x P, Relation.Eventually? R x P → P ≠ ∅ := by
  intros x P xRe?P
  induction xRe?P with
  | here x_in_P =>
    apply Set.nonempty_iff_ne_empty.mp
    exact Set.nonempty_of_mem x_in_P
  | step? _ _ _ _ _ IH =>
    exact IH

/--
  Sanity check: if all `R`-chains from `x` are safe and eventually reach values satisfying `P`, then all `R`-chains
  from `x` that are safe eventually reach values satisfying `P`.
-/
private theorem Relation.Eventually_implies_Eventually? {α} (R : α → Set α → Prop) (R_wf : ∀ x P, R x P → P ≠ ∅) (x : α) (P : Set α) :
  Relation.Eventually R x P → Relation.Eventually? R x P := by
    intro rede_x_P
    induction rede_x_P with
    | here x_in_P => exact Relation.Eventually?.here x_in_P
    | step P' RxP' _ IH =>
      obtain ⟨_, x'_in_P'⟩ := Set.nonempty_iff_ne_empty.mpr (R_wf _ _ RxP')
      apply Relation.Eventually?.step? P' _ RxP'
      · exact x'_in_P'
      · exact IH _ x'_in_P'
