module

public import Mathlib.Algebra.Group.Basic
public import Extra.Rel
public import Extra.List

public section

/-- The identity element of a trace monoid, i.e. the empty trace. Needs only `Monoid`, not the
`Trace` class below — most trace-manipulating code (`VerifiedCompiler/Relation.lean`,
`StrongRefinement.lean`) never needs a canonical `Rτ` and so only ever assumes `Monoid`. -/
abbrev Trace.τ {ε : Type _} [Monoid ε] : ε := One.one

theorem append_τ_eq {ε} [Monoid ε] (a : ε) : a * Trace.τ = a := mul_one a

theorem τ_append_eq {ε} [Monoid ε] (a : ε) : Trace.τ * a = a := one_mul a

/-- The *default* relation between two trace alphabets: exact correspondence. A pass that needs no
relaxation instantiates `StrongRefinement`'s relations at `Trace.Rτ`; a pass that reorders traces —
`Guarded2Network` does, moving message reception across the pass — threads its own `Rτ` through
those relations explicitly instead, and never touches this class.

`Rτ` occurs only positively in a refinement (inside the existential in `Terminating`'s conclusion),
never as a hypothesis, so there is no degenerate instantiation to exclude and no reflexivity or
antisymmetry law to state. What the composition lemmas below actually consume is left-totality and
closure under concatenation. -/
class Trace (εₛ εₜ : Type _) [Monoid εₛ] [Monoid εₜ] where
  /-- The canonical trace relation for this pair of types. -/
  Rτ : Rel εₛ εₜ
  Rτ_total : Relation.LeftTotal Rτ
  Rτ_closed : Relation.MulClosed Rτ

/-!
# Relating traces across languages

A pass need not preserve a trace exactly. `Guarded2Network` moves a reception from the consumption
site to the `T_rx` step, so source and target traces agree only up to a reordering that keeps every
send before its matching reception. Refinement is therefore stated against a *relation* between
traces rather than equality, with the source trace existentially quantified.

The relation is a parameter, not a fixed choice, and each composition lemma computes the relation
its conclusion carries: `Relation.rmul` (`⊗ᵣ`) when two executions are sequenced, since the traces
concatenate, and `Relation.Comp` (`∘ᵣ`) when a trace passes through an intermediate language. Only
the fixed-point lemmas constrain it, and there the constraint is what preservation of traces means
rather than a technical side condition.

`SCPrefix` is the aborting counterpart: relativized *prefix*, for a source that stopped early. It
is defined from the relation rather than being a second parameter, so that a composed refinement
still concludes something a reader can name.
-/

namespace Trace

variable {εₛ εₜ : Type _} [Monoid εₛ] [Monoid εₜ]

/-- `a ≼[R] b` — `a` is a **sequentially consistent prefix** of `b` under `R`: the source emitted
`a` and, had it not aborted, could have continued with some `δ` to produce a trace `R`-related to
the target's `b`.

The continuation is on the source side only — the target ran to completion, only the source stopped
early — and that asymmetry is the whole content of the definition. At `R = (· = ·)` over lists this
is `List.IsPrefix`, definitionally. -/
@[expose]
def SCPrefix (R : Rel εₛ εₜ) (a : εₛ) (b : εₜ) : Prop := ∃ δ, R (a * δ) b

@[inherit_doc SCPrefix]
notation:50 a:51 " ≼[" R:0 "] " b:51 => Trace.SCPrefix R a b

/-! ## `≼[·]` is a closure operator

Extensive, monotone and idempotent, with no hypotheses whatsoever on `R`: `a ≼[R] b` is the
smallest relation containing `R` and closed under dropping a suffix of its left-hand side, which is
exactly what "the source aborted partway" means.
-/

omit [Monoid εₜ] in
theorem scPrefix_of {R : Rel εₛ εₜ} {a : εₛ} {b : εₜ} (h : R a b) : a ≼[R] b := by
  exists 1
  rwa [mul_one]

omit [Monoid εₜ] in
theorem scPrefix_mono {R S : Rel εₛ εₜ} (hRS : ∀ x y, R x y → S x y) {a : εₛ} {b : εₜ}
    (h : a ≼[R] b) : a ≼[S] b := by
  obtain ⟨δ, h⟩ := h
  exact ⟨δ, hRS _ _ h⟩

omit [Monoid εₜ] in
theorem scPrefix_idem {R : Rel εₛ εₜ} {a : εₛ} {b : εₜ} : a ≼[SCPrefix R] b ↔ a ≼[R] b := by
  constructor
  · rintro ⟨δ, δ', h⟩
    exists δ * δ'
    rwa [← mul_assoc]
  · intro h
    exact scPrefix_of h

/-- A reflexive relation gives a reflexive `≼`, which is what a leaf proof uses to discharge an
abort against the trace the target actually emitted. Stated at one trace type, the only case where
it typechecks. -/
theorem scPrefix_refl {ε : Type _} [Monoid ε] {R : Rel ε ε} (hR : ∀ x, R x x) (a : ε) :
    a ≼[R] a := by
  exists 1
  rw [mul_one]
  exact hR a

/-! ## What the composition lemmas need

The three below are what a refinement algebra consumes in place of a prefix order's
`le_extend_mul`, `le_mul_right_inj` and `le_trans`. Only two hypotheses appear, both on the
relation itself and both holding of any relation that is reflexive and closed under
concatenation.
-/

/-- Sequencing, with the source aborting inside the *first* factor. The target still ran both and
emitted `b₁ * b₂`, so the tail `b₂` has to be matchable by something — which is exactly why the
second factor's relation must be left-total. -/
theorem scPrefix_rmul_left {R₁ R₂ : Rel εₛ εₜ} (tot : Relation.LeftTotal R₂) {a : εₛ} {b₁ b₂ : εₜ}
    (h : a ≼[R₁] b₁) : a ≼[R₁ ⊗ᵣ R₂] (b₁ * b₂) := by
  obtain ⟨δ, h⟩ := h
  obtain ⟨x₂, hx₂⟩ := tot b₂
  refine ⟨δ * x₂, a * δ, x₂, b₁, b₂, ?_, rfl, h, hx₂⟩
  rw [← mul_assoc]

/-- Sequencing, with the source completing the first factor and aborting inside the second. Needs
no hypothesis: the split is read off the two factors directly. -/
theorem scPrefix_rmul_right {R₁ R₂ : Rel εₛ εₜ} {a₁ a₂ : εₛ} {b₁ b₂ : εₜ}
    (h₁ : R₁ a₁ b₁) (h₂ : a₂ ≼[R₂] b₂) : (a₁ * a₂) ≼[R₁ ⊗ᵣ R₂] (b₁ * b₂) := by
  obtain ⟨δ, h₂⟩ := h₂
  refine ⟨δ, a₁, a₂ * δ, b₁, b₂, ?_, rfl, h₁, h₂⟩
  rw [mul_assoc]

omit [Monoid εₜ] in
/-- Composing across an intermediate language: an abort seen through two passes is an abort through
their composite. The first relation must be able to match the second's continuation, which
`Relation.right_extend` supplies from left-totality and closure. -/
theorem scPrefix_rcomp {ε : Type _} [Monoid ε] {R₁ : Rel εₛ ε} {R₂ : Rel ε εₜ}
    (tot : Relation.LeftTotal R₁) (cl : Relation.MulClosed R₁) {a : εₛ} {m : ε} {b : εₜ}
    (h₁ : a ≼[R₁] m) (h₂ : m ≼[R₂] b) : a ≼[R₁ ∘ᵣ R₂] b := by
  obtain ⟨δ₁, h₁⟩ := h₁
  obtain ⟨δ₂, h₂⟩ := h₂
  obtain ⟨z, hz⟩ := Relation.right_extend tot cl h₁ δ₂
  refine ⟨δ₁ * z, m * δ₂, ?_, h₂⟩
  rwa [← mul_assoc]

omit [Monoid εₜ] in
/-- The converse of `scPrefix_rcomp`, holding unconditionally.

This is why the aborting relation is *defined* from `R` rather than carried and composed alongside
it: `SCPrefix (R₁ ∘ᵣ R₂)` is contained in `SCPrefix R₁ ∘ᵣ SCPrefix R₂` for free, and the aborting
relation occurs positively in a refinement, so composing it would state strictly less. -/
theorem rcomp_scPrefix {ε : Type _} [Monoid ε] {R₁ : Rel εₛ ε} {R₂ : Rel ε εₜ} {a : εₛ} {b : εₜ}
    (h : a ≼[R₁ ∘ᵣ R₂] b) : (SCPrefix R₁ ∘ᵣ SCPrefix R₂) a b := by
  obtain ⟨δ, m, h₁, h₂⟩ := h
  exists m, ⟨δ, h₁⟩, 1
  rwa [mul_one]

/-- A fixed-point refinement needs `≼[R]` closed under a step of `R`, and `MulClosed R` already
gives it — so iterating imposes no condition beyond the one preservation itself states. -/
theorem scPrefix_of_rmul_scPrefix {R : Rel εₛ εₜ} (cl : Relation.MulClosed R) {a : εₛ} {b : εₜ}
    (h : (R ⊗ᵣ SCPrefix R) a b) : a ≼[R] b := by
  obtain ⟨a₁, a₂, b₁, b₂, rfl, rfl, h₁, δ, h₂⟩ := h
  exists δ
  rw [mul_assoc]
  exact cl _ _ _ _ h₁ h₂

end Trace

/-- The generic case: source and target traces of the same list type agree by plain equality — no
pass-specific relaxation. `Trace.SCPrefix Eq a b ↔ a <+: b` is `Iff.rfl` (`List.IsPrefix` unfolds to
`∃ t, l₁ ++ t = l₂`, matching `SCPrefix`'s `∃ δ, a * δ = b` at `Eq` up to `*` meaning `++`), so this
`≼[Rτ]` is the ordinary prefix order, and this is the degenerate case of the generalization rather
than merely isomorphic to it.

Deliberately a `def`, not an `instance`: a pass whose alphabet needs a different `Rτ` for the same
list type — `Guarded2Network` does — registers its own, and an ambient `Trace (List α) (List α)`
instance defaulting to `Eq` would silently compete with it. Name this explicitly where the default
is actually wanted. -/
@[reducible] def Trace.instList {α : Type _} : Trace (List α) (List α) where
  Rτ := Eq
  Rτ_total b := ⟨b, rfl⟩
  Rτ_closed := by rintro _ _ _ _ rfl rfl; rfl

end
