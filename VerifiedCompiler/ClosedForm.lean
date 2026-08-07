module

public import Extra.Rel
public import Extra.Seq
public import Mathlib.Order.FixedPoints
import Mathlib.Data.Nat.Find

public section

/-!
# The closed form of a diverging fixed point

Divergence is denoted directly, by the infinite iteration `Relation.omega` (`Extra/Rel.lean`), which
is what the semantics in `Core/*/Semantics/Process.lean` use. This module is about the *other*
denotation — the greatest fixed point the paper (arXiv 2404.17297, 5:36) starts from — and about
when the two agree:

```
gfp (λ x, Y ∪ X ∘ᵣ₁ x)  =  (X* ∘ᵣ₁ Y) ∪ X^∞
```

Nothing in the compiler or its refinement proofs may depend on that identity, and nothing does. It
is stated here because the paper computes with it, and because writing down the exact hypothesis it
needs is what justifies not taking the greatest fixed point as the definition in the first place.

Split from `Extra/Rel.lean` on the same principle as the rest of this library: `Extra/` carries what
the *semantics* need — `∘ᵣ₁`, `Monoid.partialProd`, `OmegaProd`, `Relation.omega` — and everything
whose only consumer is a refinement proof lives here.
-/

/-! ## Laws of the infinite product

`OmegaProd` (`Extra/Rel.lean`) carries the product and no laws, so that registering an instance
costs nothing. The laws refinement proofs actually consume are these three predicates, each passed
explicitly to the lemma that needs it.
-/

/-- Every finite prefix of an infinite product divides it. What the aborting branch of a divergence
refinement consumes: the trace emitted before the abort is a factor of the whole product, so a `≼`
obligation against the product can be discharged against that factor. -/
@[expose]
def OmegaProd.HasPartialProdDvd (ε : Type _) [Monoid ε] [OmegaProd ε] : Prop :=
  ∀ (e : ℕ → ε) (n : ℕ), ∃ r, OmegaProd.ωProd e = Monoid.partialProd e n * r

/-- The first factor of an infinite product comes out in front. -/
@[expose]
def OmegaProd.HasUnfold (ε : Type _) [Monoid ε] [OmegaProd ε] : Prop :=
  ∀ e : ℕ → ε, OmegaProd.ωProd e = e 0 * OmegaProd.ωProd (λ i ↦ e (i + 1))

/-- An element having every partial product of a sequence as a left factor *is* that sequence's
infinite product, provided the sequence keeps contributing.

The proviso is essential and is where productivity enters: without it the partial products stabilize
at some finite `p`, every element of the form `p * r` has them all as left factors, and the infinite
product is not pinned down. -/
@[expose]
def OmegaProd.HasProductLimit (ε : Type _) [Monoid ε] [OmegaProd ε] : Prop :=
  ∀ (e r : ℕ → ε) (x : ε), (∀ n, x = Monoid.partialProd e n * r n) →
    (∀ n, ∃ m, n ≤ m ∧ e m ≠ 1) → x = OmegaProd.ωProd e

/-! ## Unfolding the infinite iteration

`R^∞ = R ∘ᵣ₁ R^∞` is the one recursion equation `Relation.omega` might be expected to satisfy for
free, and it does not: neither inclusion holds without `OmegaProd.HasUnfold`. The states and steps
line up on both sides regardless — the whole content is the trace, and `OmegaProd` says nothing
about how the infinite product relates to its own tail. Taking `ωProd _ := 1` on `Multiplicative ℕ`
and `R = {((), ofAdd 1, ())}` makes the two sides `{((), 1)}` and `{((), ofAdd 1)}`, disjoint.
-/

/-- The infinite iteration unfolds by one step. Both inclusions need the unfold law; see the section
comment for the counterexample without it. -/
theorem Relation.omega_unfold {α ε : Type _} [Monoid ε] [OmegaProd ε]
    (hunfold : OmegaProd.HasUnfold ε) (R : Set (α × ε × α)) :
    Relation.omega R = R ∘ᵣ₁ Relation.omega R := by
  ext ⟨a, e⟩
  constructor
  · rintro ⟨σs, es, rfl, hstep, rfl⟩
    rw [hunfold es]
    apply Relation.lcomp₁.intro (hstep 0)
    exact ⟨λ i ↦ σs (i + 1), λ i ↦ es (i + 1), rfl, λ i ↦ hstep (i + 1), rfl⟩
  · rintro ⟨b, e₁, e₂, hR, ⟨σs, es, rfl, hstep, rfl⟩, rfl⟩
    refine ⟨λ i ↦ Nat.rec a (λ j _ ↦ σs j) i, λ i ↦ Nat.rec e₁ (λ j _ ↦ es j) i, rfl, ?_, ?_⟩
    · intro i
      cases i with
      | zero => exact hR
      | succ i => exact hstep i
    · exact (hunfold (λ i ↦ Nat.rec e₁ (λ j _ ↦ es j) i)).symm

/-! ## The identity, and the hypothesis it needs

Only one inclusion is unconditional. The functional is not contractive when `X` can step emitting
nothing, so its greatest fixed point overshoots: at `X = {(σ, 1, σ)}` and `Y = ∅` the functional is
the identity and its greatest fixed point is `⊤`, pairing `σ` with every trace whatsoever, while the
right-hand side gives `{(σ, 1)}` — the trace that execution actually emits. The leak is entirely on
the gfp side.

`Relation.Productive` is the exact boundary, not merely a convenient sufficient condition: it is what
fails in that counterexample. It is deliberately *not* satisfied by the semantics this development
compiles — `while TRUE { x := x + 1 }` diverges silently — which is why `Algebra.diverging` is
`Relation.omega` and never a greatest fixed point.
-/

/-- No infinite run of `R` emits nothing forever.

Stated as a negated existential rather than as "infinitely many steps emit something", because the
run whose productivity is at stake is produced by dependent choice: its states are not known in
advance, so there is nothing to quantify over positively. -/
@[expose]
def Relation.Productive {α ε : Type _} [Monoid ε] (R : Set (α × ε × α)) : Prop :=
  ¬∃ σ : ℕ → α, ∀ i, (σ i, (1 : ε), σ (i + 1)) ∈ R

/-- The functional whose greatest fixed point the paper takes as the denotation of divergence: one
`X`-step in front of the rest, or stop in `Y`. -/
@[expose]
def Relation.divFun {α ε : Type _} [Monoid ε] (X : Set (α × ε × α)) (Y : Set (α × ε)) :
    Set (α × ε) →o Set (α × ε) where
  toFun x := Y ∪ X ∘ᵣ₁ x
  monotone' _ _ h := Set.union_subset_union le_rfl (Relation.lcomp₁.mono le_rfl h)

@[simp] theorem Relation.divFun_apply {α ε : Type _} [Monoid ε] {X : Set (α × ε × α)}
    {Y x : Set (α × ε)} : Relation.divFun X Y x = Y ∪ X ∘ᵣ₁ x := rfl

/-- The closed form is below the greatest fixed point, unconditionally: it is a post-fixed point.
This is the half of the paper's identity that always holds. -/
theorem Relation.closedForm_le_gfp {α ε : Type _} [Monoid ε] [OmegaProd ε]
    (hunfold : OmegaProd.HasUnfold ε) {X : Set (α × ε × α)} {Y : Set (α × ε)} :
    (Relation.star X ∘ᵣ₁ Y) ∪ Relation.omega X ≤ OrderHom.gfp (Relation.divFun X Y) := by
  apply OrderHom.le_gfp
  rintro ⟨σ, e⟩ (⟨σ', e₁, e₂, hstar, hY, rfl⟩ | ⟨σs, es, h₀, hstep, rfl⟩)
  · rcases Relation.star.dest hstar with ⟨rfl, rfl⟩ | ⟨b, f₁, f₂, hR, hstar', rfl⟩
    · apply Or.inl
      rwa [one_mul]
    · refine Or.inr ⟨b, f₁, f₂ * e₂, hR, Or.inl ⟨σ', f₂, e₂, hstar', hY, rfl⟩, ?_⟩
      rw [mul_assoc]
  · dsimp only at h₀ ⊢
    subst h₀
    refine Or.inr ⟨σs 1, es 0, OmegaProd.ωProd (λ i ↦ es (i + 1)), hstep 0, Or.inr ?_, hunfold es⟩
    exact ⟨λ i ↦ σs (i + 1), λ i ↦ es (i + 1), rfl, λ i ↦ hstep (i + 1), rfl⟩

/-- The converse inclusion, under productivity. Unfolding the fixed point greedily either reaches
`Y` — a finite run, hence `X* ∘ᵣ₁ Y` — or never does, and dependent choice then produces an infinite
run whose partial products are all left factors of the trace. Productivity turns that into an
equality with the infinite product; without it the trace is never pinned down, which is exactly the
counterexample. -/
theorem Relation.gfp_le_closedForm {α ε : Type _} [Monoid ε] [OmegaProd ε]
    (lim : OmegaProd.HasProductLimit ε) {X : Set (α × ε × α)} {Y : Set (α × ε)}
    (prod : Relation.Productive X) :
    OrderHom.gfp (Relation.divFun X Y) ≤ (Relation.star X ∘ᵣ₁ Y) ∪ Relation.omega X := by classical
  rintro ⟨σ, e⟩ hmem
  haveI : Nonempty α := ⟨σ⟩
  have unf : ∀ p : α × ε, p ∈ OrderHom.gfp (Relation.divFun X Y) → p ∉ Y →
      ∃ q : ε × α × ε, (p.1, q.1, q.2.1) ∈ X ∧
        q.2 ∈ OrderHom.gfp (Relation.divFun X Y) ∧ p.2 = q.1 * q.2.2 := by
    rintro ⟨a, x⟩ hp hpY
    rw [← OrderHom.map_gfp] at hp
    rcases hp with h | ⟨b, e₁, e₂, hX, hb, he⟩
    · absurd h
      exact hpY
    · exact ⟨(e₁, b, e₂), hX, hb, he⟩
  choose! g hgX hgmem hgtrace using unf
  set P : ℕ → α × ε := λ n ↦ Nat.rec (σ, e) (λ _ p ↦ (g p).2) n
  set es : ℕ → ε := λ n ↦ (g (P n)).1
  have inv : ∀ n, (∀ i, i < n → P i ∉ Y) →
      P n ∈ OrderHom.gfp (Relation.divFun X Y) ∧ e = Monoid.partialProd es n * (P n).2 ∧
        ∀ i, i < n → ((P i).1, es i, (P (i + 1)).1) ∈ X := by
    intro n
    induction n with
    | zero => exact λ _ ↦ ⟨hmem, (one_mul e).symm, by omega⟩
    | succ n ih =>
      intro hY
      obtain ⟨hg, htr, hst⟩ := ih (λ i hi ↦ hY i (by omega))
      have hnY : P n ∉ Y := hY n (by omega)
      refine ⟨hgmem _ hg hnY, ?_, ?_⟩
      · rw [Monoid.partialProd_succ, mul_assoc, ← hgtrace _ hg hnY]
        exact htr
      · intro i hi
        rcases Nat.lt_or_ge i n with h | h
        · exact hst i h
        · rw [show i = n by omega]
          exact hgX _ hg hnY
  by_cases hstop : ∃ n, P n ∈ Y
  · obtain ⟨-, htr, hst⟩ := inv (Nat.find hstop) (λ j hj ↦ Nat.find_min hstop hj)
    exact Or.inl ⟨(P (Nat.find hstop)).1, Monoid.partialProd es (Nat.find hstop),
      (P (Nat.find hstop)).2, ⟨Nat.find hstop, λ i ↦ (P i).1, es, rfl, rfl, hst, rfl⟩,
      Nat.find_spec hstop, htr⟩
  · have hall : ∀ n, P n ∈ OrderHom.gfp (Relation.divFun X Y) ∧
        e = Monoid.partialProd es n * (P n).2 ∧
        ∀ i, i < n → ((P i).1, es i, (P (i + 1)).1) ∈ X :=
      λ n ↦ inv n (λ i _ h ↦ hstop ⟨i, h⟩)
    have hne : ∀ n, ∃ m, n ≤ m ∧ es m ≠ 1 := by
      intro n
      by_contra! hc
      apply prod
      refine ⟨λ i ↦ (P (n + i)).1, λ i ↦ ?_⟩
      have hs := (hall (n + i + 1)).2.2 (n + i) (by omega)
      rwa [hc (n + i) (by omega)] at hs
    refine Or.inr ⟨λ i ↦ (P i).1, es, rfl, λ i ↦ (hall (i + 1)).2.2 i (by omega), ?_⟩
    exact lim es (λ n ↦ (P n).2) e (λ n ↦ (hall n).2.1) hne

/-- The paper's identity, with the hypothesis it needs. -/
theorem Relation.gfp_eq_closedForm {α ε : Type _} [Monoid ε] [OmegaProd ε]
    (hunfold : OmegaProd.HasUnfold ε) (lim : OmegaProd.HasProductLimit ε)
    {X : Set (α × ε × α)} {Y : Set (α × ε)} (prod : Relation.Productive X) :
    OrderHom.gfp (Relation.divFun X Y) = (Relation.star X ∘ᵣ₁ Y) ∪ Relation.omega X :=
  le_antisymm (Relation.gfp_le_closedForm lim prod) (Relation.closedForm_le_gfp hunfold)

/-! ## Checks against the least fixed points

The semantics are the closed forms; these two identities say the closed forms denote what the least
fixed points used to. They are checks, not machinery — nothing depends on them, and if either failed
the redefinitions in `Core/*/Semantics/Process.lean` would be wrong.

There is no third identity. The greatest fixed point of the diverging functional is *not*
`Relation.omega`, which is the whole point of `Relation.gfp_eq_closedForm` above and of that
functional no longer being the definition.
-/

/-- A run followed by one more step is a run. The `∘ᵣ₂` orientation: `Relation.star.head` extends a
run on the left, and the reducing functional extends it on the right. -/
theorem Relation.star.snoc {α ε : Type _} [Monoid ε] {R : Set (α × ε × α)} {a b c : α} {e e' : ε}
    (h : (a, e, b) ∈ Relation.star R) (h' : (b, e', c) ∈ R) :
    (a, e * e', c) ∈ Relation.star R := by
  have main : ∀ (n : ℕ) (σs : ℕ → α) (es : ℕ → ε) (d : α) (f : ε),
      (∀ i, i < n → (σs i, es i, σs (i + 1)) ∈ R) → (σs n, f, d) ∈ R →
      (σs 0, Monoid.partialProd es n * f, d) ∈ Relation.star R := by
    intro n
    induction n with
    | zero =>
      intro σs es d f _ hstep
      rw [Monoid.partialProd_zero, one_mul, ← mul_one f]
      apply Relation.star.head hstep (Relation.star.refl d)
    | succ n ih =>
      intro σs es d f hsteps hstep
      rw [Monoid.partialProd_succ' es n, mul_assoc]
      apply Relation.star.head (hsteps 0 (by omega))
      apply ih (λ i ↦ σs (i + 1)) (λ i ↦ es (i + 1)) d f (λ i hi ↦ hsteps (i + 1) (by omega)) hstep
  obtain ⟨n, σs, es, h₀, hn, hsteps, rfl⟩ := h
  dsimp only at h₀ hn ⊢
  subst h₀
  subst hn
  exact main n σs es c e' hsteps h'

/-- The functional whose least fixed point used to define the reducing semantics: the empty
execution, or a run followed by one more step. -/
@[expose]
def Relation.starFun {α ε : Type _} [Monoid ε] (X : Set (α × ε × α)) :
    Set (α × ε × α) →o Set (α × ε × α) where
  toFun Z := {⟨x, e, y⟩ | x = y ∧ e = 1} ∪ Z ∘ᵣ₂ X
  monotone' _ _ h := Set.union_subset_union le_rfl (Relation.lcomp₂.mono h le_rfl)

/-- `step*` is what `μZ. Id ∪ Z ∘ᵣ₂ step` denoted. -/
theorem Relation.lfp_starFun {α ε : Type _} [Monoid ε] (X : Set (α × ε × α)) :
    OrderHom.lfp (Relation.starFun X) = Relation.star X := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    rintro ⟨a, e, b⟩ (⟨rfl, rfl⟩ | ⟨c, e₁, e₂, hrun, hstep, rfl⟩)
    · exact Relation.star.refl a
    · exact Relation.star.snoc hrun hstep
  · have main : ∀ (n : ℕ) (σs : ℕ → α) (es : ℕ → ε),
        (∀ i, i < n → (σs i, es i, σs (i + 1)) ∈ X) →
        (σs 0, Monoid.partialProd es n, σs n) ∈ OrderHom.lfp (Relation.starFun X) := by
      intro n
      induction n with
      | zero =>
        intro σs es _
        rw [← OrderHom.map_lfp]
        exact Or.inl ⟨rfl, rfl⟩
      | succ n ih =>
        intro σs es hsteps
        rw [← OrderHom.map_lfp, Monoid.partialProd_succ]
        apply Or.inr
        apply Relation.lcomp₂.intro (ih σs es (λ i hi ↦ hsteps i (by omega)))
        exact hsteps n (by omega)
    rintro ⟨a, e, b⟩ ⟨n, σs, es, h₀, hn, hsteps, rfl⟩
    dsimp only at h₀ hn ⊢
    subst h₀
    subst hn
    exact main n σs es hsteps

/-- `step* ∘ᵣ₁ immediate` is what `μx. immediate ∪ step ∘ᵣ₁ x` denoted. The *least* fixed point of
the functional whose *greatest* one overshoots — the paper states both halves at 5:36, and this half
needs no hypothesis at all. -/
theorem Relation.lfp_divFun {α ε : Type _} [Monoid ε] (X : Set (α × ε × α)) (Y : Set (α × ε)) :
    OrderHom.lfp (Relation.divFun X Y) = Relation.star X ∘ᵣ₁ Y := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    rintro ⟨σ, e⟩ (hY | hstep)
    · rw [← one_mul e]
      apply Relation.lcomp₁.intro (Relation.star.refl σ) hY
    · exact Relation.star.lcomp₁_absorb hstep
  · have main : ∀ (n : ℕ) (σs : ℕ → α) (es : ℕ → ε) (e₂ : ε), (σs n, e₂) ∈ Y →
        (∀ i, i < n → (σs i, es i, σs (i + 1)) ∈ X) →
        (σs 0, Monoid.partialProd es n * e₂) ∈ OrderHom.lfp (Relation.divFun X Y) := by
      intro n
      induction n with
      | zero =>
        intro σs es e₂ hY _
        rw [Monoid.partialProd_zero, one_mul, ← OrderHom.map_lfp]
        exact Or.inl hY
      | succ n ih =>
        intro σs es e₂ hY hsteps
        rw [Monoid.partialProd_succ' es n, mul_assoc, ← OrderHom.map_lfp]
        apply Or.inr
        apply Relation.lcomp₁.intro (hsteps 0 (by omega))
        exact ih (λ i ↦ σs (i + 1)) (λ i ↦ es (i + 1)) e₂ hY (λ i hi ↦ hsteps (i + 1) (by omega))
    rintro ⟨σ, e⟩ ⟨σ', e₁, e₂, ⟨n, σs, es, h₀, hn, hsteps, rfl⟩, hY, rfl⟩
    dsimp only at h₀ hn ⊢
    subst h₀
    subst hn
    exact main n σs es e₂ hY hsteps

/-! ## The trace monoid satisfies all three

`Stream'.Seq` is the trace type (`Extra/Seq.lean`), and the mathematics behind these three lines
lives there, stated without mentioning a refinement predicate. Only the discharges are here, so that
`Extra/` never has to import this library.
-/

namespace Stream'.Seq
  variable {α : Type _}

  /-- Every finite prefix of a `Seq` product divides it. -/
  theorem hasPartialProdDvd : OmegaProd.HasPartialProdDvd (Seq α) := exists_mul_ωProduct

  /-- `Seq` products unfold. -/
  theorem hasUnfold : OmegaProd.HasUnfold (Seq α) := ωProduct_succ

  /-- A `Seq` sharing every partial product as a left factor is the product, once the factors keep
  coming. -/
  theorem hasProductLimit : OmegaProd.HasProductLimit (Seq α) :=
    λ e r x hx hne ↦ ωProduct_eq_of_forall_dvd (λ n ↦ ⟨r n, hx n⟩) hne
end Stream'.Seq

end
