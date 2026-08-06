module

public import Mathlib.Data.Seq.Basic
public import Mathlib.Algebra.Group.Defs

public section

/-!
# `Stream'.Seq` as a trace monoid

Traces are possibly-infinite: a diverging algorithm that keeps sending emits forever, and a finite
trace type cannot hold what it emits. `Stream'.Seq` is the coinductive possibly-finite sequence, and
concatenation makes it a monoid unconditionally — including `append_nil`, which holds because
appending to an infinite sequence absorbs the right operand rather than failing.

That absorption is the reason this is a monoid at all, and it is worth stating plainly since it is
the one law a reader expects to break: for infinite `s`, `s * t = s` for *every* `t`, so `s * 1 = s`
is a special case of absorption rather than a genuine right identity. Nothing downstream depends on
cancellativity, so the collapse is harmless — see `VerifiedCompiler/Trace.lean`, whose `SCPrefix`
lemmas are all introduction and elimination on `∃ δ`.

Mathlib proves the three laws but registers no algebraic instance, so they are bundled here.
-/

namespace Stream'.Seq
  variable {α : Type _}

  /-- The empty trace. -/
  instance : One (Seq α) := ⟨nil⟩

  /-- Concatenation of traces. -/
  instance : Mul (Seq α) := ⟨append⟩

  instance : Monoid (Seq α) where
    mul_assoc := append_assoc
    one_mul := nil_append
    mul_one := append_nil

  /-! ## Bridging the algebraic and the `Seq` APIs

  Deliberately **not** `@[simp]`, in either direction. Mathlib's `Seq` lemmas are stated with
  `append`/`nil` and are largely `@[simp]`; this development's trace algebra is stated with `*`/`1`
  (`Trace.τ`, `Relation.lcomp₁`, every `scPrefix_*` lemma). Normalizing either way would leave one
  of the two sets unable to fire, so the normal form stays `*`/`1` — matching the rest of the
  development — and reaching for Mathlib's `Seq` API is an explicit `rw`.
  -/

  /-- `1` is the empty sequence. -/
  theorem one_eq_nil : (1 : Seq α) = nil := rfl

  /-- Multiplication is concatenation. -/
  theorem mul_eq_append (s t : Seq α) : s * t = append s t := rfl

  /-! ## Absorption

  An infinite sequence swallows whatever is appended to it. Mathlib proves `append_nil`
  unconditionally but states no general absorption law, so it is proved here: the header's claim
  that right identity holds *because of* absorption rather than despite it should not rest on an
  unverified assertion.
  -/

  /-- Appending to a non-terminating sequence changes nothing. -/
  theorem append_eq_left_of_not_terminates {s : Seq α} (h : ¬s.Terminates) (t : Seq α) :
      append s t = s := by
    apply eq_of_bisim' (motive := λ a b ↦ ¬b.Terminates ∧ a = append b t) ⟨h, rfl⟩
    rintro a b ⟨hb, rfl⟩
    cases b with
    | nil => exact absurd terminates_nil hb
    | cons x b' =>
      exact Or.inr ⟨x, append b' t, b', cons_append .., rfl,
        λ h' ↦ hb (terminates_cons_iff.mpr h'), rfl⟩

  /-- `append_eq_left_of_not_terminates` in the algebraic vocabulary: a non-terminating trace is a
  left zero. This is why `Seq` is only a monoid and never cancellative — a product whose left factor
  is infinite tells you nothing about its right factor. -/
  theorem mul_eq_left_of_not_terminates {s : Seq α} (h : ¬s.Terminates) (t : Seq α) : s * t = s :=
    append_eq_left_of_not_terminates h t

  /-! ## Infinite products

  The trace of an execution that takes infinitely many steps: each step contributes a finite (in
  general, arbitrary) trace, and the whole is their infinite concatenation.

  Corecursion is not available for this. A corecursive concatenation has to decide whether the
  result is empty before producing anything, and with possibly-empty pieces that decision depends
  on all of them — the definition would not be productive. So the product is built the other way
  round: as the sup of the finite partial products, taken index by index. Index `k` of the product
  is whatever index `k` of some partial product is, if any partial product has one; the pieces only
  ever extend each other, so it does not matter which.

  This is total — *every* `e : ℕ → Seq α` has a product, with no side condition on the pieces being
  nonempty and no fairness or productivity assumption. That matters: the refinement lemma for
  divergence quantifies over an arbitrary step sequence, including one that emits nothing forever,
  and the trace it must produce there is `1`.
  -/

  /-- The product of the first `n` pieces: `e 0 * ⋯ * e (n-1)`, and `1` when `n = 0`. -/
  @[expose] def partialProd (e : ℕ → Seq α) : ℕ → Seq α
    | 0 => 1
    | n + 1 => partialProd e n * e n

  @[simp] theorem partialProd_zero {e : ℕ → Seq α} : partialProd e 0 = 1 := rfl

  @[simp] theorem partialProd_succ {e : ℕ → Seq α} {n : ℕ} :
      partialProd e (n + 1) = partialProd e n * e n := rfl

  /-- Appending on the right never disturbs an index the left operand already defines. -/
  theorem get?_mul_of_get? {s : Seq α} {k : ℕ} {a : α} (u : Seq α) (h : s.get? k = some a) :
      (s * u).get? k = some a := by
    induction k generalizing s with
    | zero =>
      cases s with
      | nil => simp at h
      | cons b s' =>
        rw [get?_cons_zero] at h
        rw [mul_eq_append, cons_append, get?_cons_zero, h]
    | succ k ih =>
      cases s with
      | nil => simp at h
      | cons b s' =>
        rw [get?_cons_succ] at h
        rw [mul_eq_append, cons_append, get?_cons_succ]
        exact ih h

  /-- Partial products only ever grow: an index defined by one is defined, identically, by every
  later one. -/
  theorem get?_partialProd_of_le {e : ℕ → Seq α} {m n k : ℕ} {a : α} (hmn : m ≤ n)
      (h : (partialProd e m).get? k = some a) : (partialProd e n).get? k = some a := by
    induction n with
    | zero => rwa [show m = 0 by omega] at h
    | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h' | h'
      · rw [partialProd_succ]
        exact get?_mul_of_get? _ (ih (by omega))
      · rwa [show m = n + 1 by omega] at h

  open Classical in
  /-- Index `k` of the infinite product: whatever some partial product holds there, if any does.
  Split out of `ωProduct` so that the `IsSeq` obligation and the characterization below are stated
  against a name rather than against a lambda buried in an anonymous constructor. -/
  @[expose] noncomputable def ωFun (e : ℕ → Seq α) (k : ℕ) : Option α :=
    if h : ∃ n, ((partialProd e n).get? k).isSome then (partialProd e (Nat.find h)).get? k else none

  theorem ωFun_eq_some {e : ℕ → Seq α} {k : ℕ} {a : α} :
      ωFun e k = some a ↔ ∃ n, (partialProd e n).get? k = some a := by classical
    unfold ωFun
    constructor
    · intro h
      split at h
      · exact ⟨_, h⟩
      · exact absurd h (by simp)
    · rintro ⟨n, hn⟩
      have hex : ∃ n, ((partialProd e n).get? k).isSome := ⟨n, by rw [hn]; rfl⟩
      rw [dif_pos hex]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
      rcases Nat.le_total (Nat.find hex) n with h' | h'
      · rw [get?_partialProd_of_le h' hb] at hn
        exact hb.trans hn
      · exact get?_partialProd_of_le h' hn

  theorem ωFun_eq_none {e : ℕ → Seq α} {k : ℕ} :
      ωFun e k = none ↔ ∀ n, (partialProd e n).get? k = none := by
    constructor
    · intro h n
      by_contra hn
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hn
      rw [ωFun_eq_some.mpr ⟨n, ha⟩] at h
      contradiction
    · intro h
      by_contra hne
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
      obtain ⟨n, hn⟩ := ωFun_eq_some.mp ha
      rw [h n] at hn
      contradiction

  /-- The infinite product `e 0 * e 1 * ⋯`, as the sup of the partial products.

  Total: no hypothesis on `e` whatsoever. -/
  @[expose] noncomputable def ωProduct (e : ℕ → Seq α) : Seq α :=
    ⟨ωFun e, by
      intro k hk
      rw [ωFun_eq_none] at hk ⊢
      exact λ n ↦ le_stable _ (Nat.le_succ k) (hk n)⟩

  @[simp] theorem get?_ωProduct_eq_ωFun {e : ℕ → Seq α} {k : ℕ} :
      (ωProduct e).get? k = ωFun e k := rfl

  /-- What the product holds at each index: exactly what some partial product holds there. -/
  theorem get?_ωProduct {e : ℕ → Seq α} {k : ℕ} {a : α} :
      (ωProduct e).get? k = some a ↔ ∃ n, (partialProd e n).get? k = some a :=
    ωFun_eq_some

  /-- A step sequence that never emits has the empty trace, with no productivity assumption
  anywhere. The case a corecursive definition could not have produced. -/
  @[simp] theorem ωProduct_const_one : ωProduct (λ _ : ℕ ↦ (1 : Seq α)) = 1 := by
    have hp : ∀ n, partialProd (λ _ : ℕ ↦ (1 : Seq α)) n = 1 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [partialProd_succ, ih, mul_one]
    apply Seq.ext
    intro k
    have hk : (ωProduct (λ _ : ℕ ↦ (1 : Seq α))).get? k = none := by
      rw [get?_ωProduct_eq_ωFun, ωFun_eq_none]
      intro n
      rw [hp n, one_eq_nil, get?_nil]
    rw [hk, one_eq_nil, get?_nil]
end Stream'.Seq

end
