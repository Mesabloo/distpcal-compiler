module

meta import CustomPrelude
public import Mathlib.Algebra.Group.Basic
public import Extra.Rel
public import Extra.List
public import Extra.Seq

public section

/-- The identity element of a trace monoid, i.e. the empty trace. Needs only `Monoid`, not the
`Trace` class below — most trace-manipulating code (`VerifiedCompiler/Relation.lean`,
`StrongRefinement.lean`) never needs a canonical `Rτ` and so only ever assumes `Monoid`. -/
abbrev Trace.τ {ε : Type _} [Monoid ε] : ε := One.one

theorem append_τ_eq {ε} [Monoid ε] (a : ε) : a * Trace.τ = a := mul_one a

theorem τ_append_eq {ε} [Monoid ε] (a : ε) : Trace.τ * a = a := one_mul a

/-!
## Composing relations

Two ways of combining relations, both used to say how the `Trace` class below builds a refinement's
trace relation out of its factors'. They are different monoid structures on relations and
should not be confused: `∘ᵣ`'s unit is the diagonal, `⊗ᵣ`'s is the relation holding only of the two
units.

Relations are heterogeneous throughout — a source and a target need not draw their traces from the
same type.
-/

/-- Relational composition is mathlib's `Relation.Comp`; only the notation is ours, since mathlib
declares its `∘r` `local`. Named to match this file's `∘ᵣ₁`/`∘ᵣ₂`. -/
infixr:140 " ∘ᵣ " => Relation.Comp

/-- Pointwise product through the two monoids: the left-hand sides multiply and so do the
right-hand sides, each factor related by its own relation. Composing two refinements in sequence
combines their trace relations this way, since the traces concatenate. -/
@[expose]
def Relation.rmul {α β : Type _} [Monoid α] [Monoid β] (P Q : Rel α β) : Rel α β :=
  λ a b ↦ ∃ a₁ a₂ b₁ b₂, a = a₁ * a₂ ∧ b = b₁ * b₂ ∧ P a₁ b₁ ∧ Q a₂ b₂

@[inherit_doc] infixl:70 " ⊗ᵣ " => Relation.rmul

/-- Every right-hand element is related to by some left-hand one. For a trace relation this says
the target can emit nothing the source could not have emitted. -/
@[expose]
def Relation.LeftTotal {α β : Type _} (R : Rel α β) : Prop := ∀ b, ∃ a, R a b

/-- Closed under multiplication: as a subset of `α × β`, a submonoid. For a trace relation this is
the statement that the relation is preserved by concatenation, which is what a fixed-point
refinement needs of it. -/
@[expose]
def Relation.MulClosed {α β : Type _} [Monoid α] [Monoid β] (R : Rel α β) : Prop :=
  ∀ a b c d, R a b → R c d → R (a * c) (b * d)

/-- Closure under concatenation, in the form the composition lemmas consume: the pointwise product
of the relation with itself is again the relation. `MulClosed` states the same fact with the four
components named, which is the convenient shape to *prove* and the inconvenient one to *apply*. -/
theorem Relation.MulClosed.rmul_le {α β : Type _} [Monoid α] [Monoid β] {R : Rel α β}
    (cl : Relation.MulClosed R) : R ⊗ᵣ R ≤ R := by
  rintro _ _ ⟨a₁, a₂, b₁, b₂, rfl, rfl, h₁, h₂⟩
  exact cl _ _ _ _ h₁ h₂

/-- What `StrongRefinement.Comp`'s trace relation collapses to when both operands run at the same
one: `Rτ₁ ⊔ Rτ₁ ⊗ᵣ Rτ₂` with `Rτ₁ = Rτ₂ = R`. Only `rmul_le` is needed — `R ≤ R ⊔ _` is free, so no
unit law about `R 1 1` enters. -/
theorem Relation.MulClosed.sup_rmul_self {α β : Type _} [Monoid α] [Monoid β] {R : Rel α β}
    (cl : Relation.MulClosed R) : R ⊔ R ⊗ᵣ R = R :=
  sup_eq_left.mpr cl.rmul_le

/-- Any extension of the right-hand side can be matched by some extension of the left. Not an extra
assumption: it is what `LeftTotal` and `MulClosed` give together, and it is the form horizontal
composition actually consumes. -/
theorem Relation.right_extend {α β : Type _} [Monoid α] [Monoid β] {R : Rel α β}
    (tot : Relation.LeftTotal R) (cl : Relation.MulClosed R) {a : α} {b : β} (h : R a b) (z : β) :
    ∃ z', R (a * z') (b * z) := by
  obtain ⟨z', hz'⟩ := tot z
  exact ⟨z', cl _ _ _ _ h hz'⟩

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
  /-- The empty trace corresponds to the empty trace.

  Not implied by the two laws above: `Rτ_total` supplies *some* source trace over `1`, and nothing
  forces it to be `1`. Needed as the base case of "the first `n` steps' traces are related", which
  is what a divergence refinement uses to place an abort reached after `n` steps. -/
  Rτ_one : Rτ 1 1

/-- `Trace` extended with the infinite-product law the divergence lemmas need: two sequences related
pointwise by `Rτ` have related products. Separate from `Trace` because `Terminating`/`Aborting`
need only `Trace` and have nothing to do with infinite products. -/
class ωTrace (εₛ εₜ : Type _) [Monoid εₛ] [Monoid εₜ] [ωMonoid εₛ] [ωMonoid εₜ]
    extends Trace εₛ εₜ where
  /-- Pointwise `Rτ` lifts to the infinite product. -/
  Rτ_omega : ∀ (e' : ℕ → εₛ) (e : ℕ → εₜ), (∀ i, Rτ (e' i) (e i)) →
    Rτ (ωMonoid.ωProd e') (ωMonoid.ωProd e)

@[reducible, expose]
def Trace.comp {εₛ εₜ εᵤ} [Monoid εₛ] [Monoid εₜ] [Monoid εᵤ] [inst₁ : Trace εₛ εₜ] [inst₂ : Trace εₜ εᵤ] : Trace εₛ εᵤ where
  Rτ := inst₁.Rτ ∘ᵣ inst₂.Rτ
  Rτ_total := by
    intros z
    obtain ⟨y, h₂⟩ := inst₂.Rτ_total z
    obtain ⟨x, h₁⟩ := inst₁.Rτ_total y
    use x, y, h₁, h₂
  Rτ_closed := by
    rintro x z x' z' ⟨y, xRy, yRz⟩ ⟨y', x'Ry', y'Rz'⟩
    use y * y', ?_, ?_ <;> apply Rτ_closed <;> assumption
  Rτ_one := by
    use 1, Rτ_one, Rτ_one

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

/-- The canonical trace relation is idempotent for the pointwise product. `Rτ_closed` gives `≤`;
the converse is `Rτ_one`, splitting a trace as `ε * 1`. Both laws are the class's, which is why this
is stated here and not at `MulClosed` — `Relation.MulClosed.rmul_le` alone cannot prove it.

This is what lets the composition lemmas conclude at `Rτ` rather than at the `⊗ᵣ`/`⊔` shape their
proofs naturally produce, so that composing two refinements needs no repair at the call site. -/
theorem rmul_self [T : Trace εₛ εₜ] : T.Rτ ⊗ᵣ T.Rτ = T.Rτ :=
  le_antisymm T.Rτ_closed.rmul_le
    λ a b h ↦ ⟨a, 1, b, 1, (mul_one a).symm, (mul_one b).symm, h, T.Rτ_one⟩

@[inherit_doc rmul_self]
theorem sup_rmul_self [T : Trace εₛ εₜ] : T.Rτ ⊔ T.Rτ ⊗ᵣ T.Rτ = T.Rτ := by
  rw [rmul_self, sup_idem]

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
  iff_rintro ⟨δ, δ', h⟩ h
  · exists δ * δ'
    rwa [← mul_assoc]
  · exact scPrefix_of h

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
list type registers its own, and an ambient `Trace (List α) (List α)` instance defaulting to `Eq`
would silently compete with it. Name this explicitly where the default is actually wanted — as
`Guarded2Network` does, via a `scoped instance` (`Guarded2Network/Lemmas/Trace.lean`). `@[expose]`
so that a downstream `Rτ`-unfolding lemma can see the body. -/
@[expose, reducible] def Trace.instList {α : Type _} : Trace (List α) (List α) where
  Rτ := Eq
  Rτ_total b := ⟨b, rfl⟩
  Rτ_closed := by rintro _ _ _ _ rfl rfl; rfl
  Rτ_one := rfl

/-- The same at `Stream'.Seq`, the trace type the PlusCal semantics actually use
(`Core/GuardedPlusCal/Semantics/Denotational.lean`'s `Trace`). A `def` rather than an `instance` for
the same reason as `Trace.instList` — and this is the one `Guarded2Network` registers scoped, its
traces being preserved exactly. -/
@[expose, reducible] def Trace.instSeq {α : Type _} : Trace (Stream'.Seq α) (Stream'.Seq α) where
  Rτ := Eq
  Rτ_total b := ⟨b, rfl⟩
  Rτ_closed := by rintro _ _ _ _ rfl rfl; rfl
  Rτ_one := rfl

end
