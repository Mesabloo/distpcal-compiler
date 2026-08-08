module

meta import CustomPrelude
public import Mathlib.Data.Seq.Basic
public import Mathlib.Algebra.Group.Defs
public import Extra.Rel

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
    | nil =>
      absurd (terminates_nil (α := α))
      exact hb
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
      (h : (Monoid.partialProd e m).get? k = some a) : (Monoid.partialProd e n).get? k = some a := by
    induction n with
    | zero =>
      have hm : m = 0 := by omega
      rwa [hm] at h
    | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h' | h'
      · rw [Monoid.partialProd_succ]
        exact get?_mul_of_get? _ (ih (by omega))
      · have hm : m = n + 1 := by omega
        rwa [hm] at h

  open Classical in
  /-- Index `k` of the infinite product: whatever some partial product holds there, if any does.
  Split out of `ωProduct` so that the `IsSeq` obligation and the characterization below are stated
  against a name rather than against a lambda buried in an anonymous constructor. -/
  @[expose] noncomputable def ωFun (e : ℕ → Seq α) (k : ℕ) : Option α :=
    if h : ∃ n, ((Monoid.partialProd e n).get? k).isSome then (Monoid.partialProd e (Nat.find h)).get? k else none

  theorem ωFun_eq_some {e : ℕ → Seq α} {k : ℕ} {a : α} :
      ωFun e k = some a ↔ ∃ n, (Monoid.partialProd e n).get? k = some a := by classical
    unfold ωFun
    iff_rintro h ⟨n, hn⟩
    · split at h
      · exact ⟨_, h⟩
      · nomatch h
    · have hex : ∃ n, ((Monoid.partialProd e n).get? k).isSome := ⟨n, by rw [hn]; rfl⟩
      rw [dif_pos hex]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
      rcases Nat.le_total (Nat.find hex) n with h' | h'
      · rw [get?_partialProd_of_le h' hb] at hn
        exact hb.trans hn
      · exact get?_partialProd_of_le h' hn

  theorem ωFun_eq_none {e : ℕ → Seq α} {k : ℕ} :
      ωFun e k = none ↔ ∀ n, (Monoid.partialProd e n).get? k = none := by
    iff_intro h h
    · intro n
      by_contra hn
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hn
      rw [ωFun_eq_some.mpr ⟨n, ha⟩] at h
      contradiction
    · by_contra hne
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
      (ωProduct e).get? k = some a ↔ ∃ n, (Monoid.partialProd e n).get? k = some a :=
    ωFun_eq_some

  /-- A step sequence that never emits has the empty trace, with no productivity assumption
  anywhere. The case a corecursive definition could not have produced. -/
  @[simp] theorem ωProduct_const_one : ωProduct (λ _ : ℕ ↦ (1 : Seq α)) = 1 := by
    have hp : ∀ n, Monoid.partialProd (λ _ : ℕ ↦ (1 : Seq α)) n = 1 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [Monoid.partialProd_succ, ih, mul_one]
    apply Seq.ext
    intro k
    have hk : (ωProduct (λ _ : ℕ ↦ (1 : Seq α))).get? k = none := by
      rw [get?_ωProduct_eq_ωFun, ωFun_eq_none]
      intro n
      rw [hp n, one_eq_nil, get?_nil]
    rw [hk, one_eq_nil, get?_nil]
  /-- `Seq` products make it an `OmegaProd`. -/
  noncomputable instance : OmegaProd (Seq α) where
    ωProd := ωProduct

  @[simp] theorem ωProd_eq_ωProduct {e : ℕ → Seq α} : OmegaProd.ωProd e = ωProduct e := rfl

  /-! ## Factoring out a prefix

  What the aborting branch of a divergence refinement needs: the trace emitted before the abort is
  a factor of the whole product, so that a `≼` obligation against the product can be discharged
  against that factor.

  The terminating case is an induction on the index at which the prefix terminates — deliberately
  not on its *length*, since relating `Seq.take`/`Seq.drop` to `append` would need lemmas Mathlib
  does not have. The non-terminating case is absorption: nothing after an infinite prefix is
  observable, so the product is the prefix.
  -/

  /-- A terminating prefix can be factored out. `s` terminating and defining nothing that `u`
  disagrees with means `u` continues `s`. -/
  theorem exists_mul_of_get? {n : ℕ} : ∀ {s u : Seq α}, s.TerminatedAt n →
      (∀ k a, s.get? k = some a → u.get? k = some a) → ∃ r, u = s * r := by
    induction n with
    | zero =>
      intro s u hs _
      exists u
      rw [terminatedAt_zero_iff.mp hs, mul_eq_append, nil_append]
    | succ n ih =>
      intro s u hs h
      cases s with
      | nil =>
        exists u
        rw [mul_eq_append, nil_append]
      | cons b s' =>
        have hu : u = cons b u.tail := by
          apply head_eq_some
          apply h 0 b
          rw [get?_cons_zero]
        obtain ⟨r, hr⟩ := ih (cons_terminatedAt_succ_iff.mp hs) (λ k a hk ↦ by
          rw [get?_tail]
          apply h (k + 1)
          rwa [get?_cons_succ])
        exists r
        rewrite [hu, hr]
        simp only [mul_eq_append, cons_append]

  /-- Once a partial product is infinite, every later one equals it and the whole product stops
  there. -/
  theorem ωProduct_eq_of_not_terminates {e : ℕ → Seq α} {n : ℕ}
      (h : ¬(Monoid.partialProd e n).Terminates) : ωProduct e = Monoid.partialProd e n := by
    have hstab : ∀ m, n ≤ m → Monoid.partialProd e m = Monoid.partialProd e n := by
      intro m
      induction m with
      | zero =>
        intro hm
        have hn : n = 0 := by omega
        rw [hn]
      | succ m ih =>
        intro hm
        rcases Nat.lt_or_ge n (m + 1) with h' | h'
        · rw [Monoid.partialProd_succ, ih (by omega)]
          apply mul_eq_left_of_not_terminates h
        · have hn : n = m + 1 := by omega
          rw [hn]
    apply Seq.ext
    intro k
    apply Option.ext
    intro a
    iff_intro hk hk
    · obtain ⟨m, hm⟩ := get?_ωProduct.mp hk
      rcases Nat.le_total m n with h' | h'
      · apply get?_partialProd_of_le h' hm
      · rwa [hstab m h'] at hm
    · apply get?_ωProduct.mpr
      exact ⟨n, hk⟩

  /-- Every finite prefix of a `Seq` product is a left factor of it.

  Stated without naming `OmegaProd.HasPartialProdDvd`: the predicate belongs to the refinement
  framework (`VerifiedCompiler/ClosedForm.lean`), which discharges it from this lemma. Keeping the
  mathematics predicate-free is what stops `Extra/` from importing that library. -/
  theorem exists_mul_ωProduct (e : ℕ → Seq α) (n : ℕ) :
      ∃ r, ωProduct e = Monoid.partialProd e n * r := by
    by_cases h : (Monoid.partialProd e n).Terminates
    · obtain ⟨m, hm⟩ := h
      apply exists_mul_of_get? hm
      intro k a hk
      apply get?_ωProduct.mpr
      exact ⟨n, hk⟩
    · exists 1
      rw [mul_one]
      apply ωProduct_eq_of_not_terminates h

  /-! ## Reading past a finite left factor

  `get?_mul_of_get?` says a concatenation agrees with its left operand wherever that operand is
  defined. The complementary law — what the concatenation holds *after* the left operand runs out —
  is what the unfolding law below needs, and Mathlib has neither it nor the `append`/`take`/`drop`
  lemmas one would derive it from. It is proved here directly, by recursion on the index at which
  the left operand terminates.

  The minimality hypothesis is not decoration: without it the left operand may terminate strictly
  earlier than the stated index, and the two sides are then offset by the difference.
  -/

  /-- Past its last index, a concatenation is its right operand. -/
  theorem get?_mul_of_terminatedAt : ∀ {n : ℕ} {s : Seq α}, (∀ k, k < n → ¬s.TerminatedAt k) →
      s.TerminatedAt n → ∀ (t : Seq α) (j : ℕ), (s * t).get? (n + j) = t.get? j := by
    intro n
    induction n with
    | zero =>
      intro s _ hterm t j
      rw [terminatedAt_zero_iff.mp hterm, mul_eq_append, nil_append, Nat.zero_add]
    | succ n ih =>
      intro s hmin hterm t j
      cases s with
      | nil =>
        absurd (show (nil : Seq α).TerminatedAt 0 from rfl)
        exact hmin 0 (by omega)
      | cons b s' =>
        have hj : n + 1 + j = n + j + 1 := by omega
        rw [mul_eq_append, cons_append, hj, get?_cons_succ]
        apply ih ?_ (cons_terminatedAt_succ_iff.mp hterm)
        intro k hk h
        apply hmin (k + 1) (by omega)
        exact cons_terminatedAt_succ_iff.mpr h

  /-- A nonempty trace has a first element. -/
  theorem exists_get?_zero_of_ne_one {s : Seq α} (h : s ≠ 1) : ∃ a, s.get? 0 = some a := by
    cases s with
    | nil =>
      absurd (one_eq_nil (α := α)).symm
      exact h
    | cons b s' => exact ⟨b, get?_cons_zero b s'⟩

  /-- The first factor comes out in front of an infinite product.

  Both cases are decided by whether the first factor is finite. If it is not, absorption settles
  everything: the product stops there and so does the right-hand side. If it is, the two sides are
  compared index by index on either side of its last index — before it both are that factor, after
  it both are the product of the remaining factors. -/
  theorem ωProduct_succ (e : ℕ → Seq α) :
      ωProduct e = e 0 * ωProduct (λ i ↦ e (i + 1)) := by classical
    have hp1 : Monoid.partialProd e 1 = e 0 := by
      rw [Monoid.partialProd_succ, Monoid.partialProd_zero, one_mul]
    by_cases hterm : (e 0).Terminates
    · obtain ⟨L, hL, hLmin⟩ : ∃ L, (e 0).TerminatedAt L ∧ ∀ k, k < L → ¬(e 0).TerminatedAt k :=
        ⟨Nat.find hterm, Nat.find_spec hterm, λ k hk ↦ Nat.find_min hterm hk⟩
      apply Seq.ext
      intro k
      rcases Nat.lt_or_ge k L with hk | hk
      · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (hLmin k hk)
        rw [get?_ωProduct.mpr ⟨1, by rwa [hp1]⟩, get?_mul_of_get? _ hb]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
        rw [get?_mul_of_terminatedAt hLmin hL]
        apply Option.ext
        intro a
        rw [get?_ωProduct, get?_ωProduct]
        iff_rintro ⟨n, hn⟩ ⟨m, hm⟩
        · cases n with
          | zero =>
            rw [Monoid.partialProd_zero, one_eq_nil, get?_nil] at hn
            contradiction
          | succ m =>
            exists m
            rwa [Monoid.partialProd_succ', get?_mul_of_terminatedAt hLmin hL] at hn
        · exists m + 1
          rwa [Monoid.partialProd_succ', get?_mul_of_terminatedAt hLmin hL]
    · rw [mul_eq_left_of_not_terminates hterm, ← hp1]
      apply ωProduct_eq_of_not_terminates
      rwa [hp1]

  /-! ## Products of a sequence that keeps emitting

  The converse half of the paper's closed form needs the infinite product to be *determined* by its
  partial products, which it is only when those keep growing. Each nonempty factor extends the
  partial product by at least one index, so infinitely many of them reach every index — and an
  element sharing every partial product as a left factor then agrees with the product everywhere.
  -/

  /-- Infinitely many nonempty factors define every index of some partial product. -/
  theorem exists_get?_partialProd {e : ℕ → Seq α} (hne : ∀ n, ∃ m, n ≤ m ∧ e m ≠ 1) (k : ℕ) :
      ∃ n a, (Monoid.partialProd e n).get? k = some a := by classical
    induction k with
    | zero =>
      obtain ⟨m, _, hm⟩ := hne 0
      by_cases h : ∃ a, (Monoid.partialProd e m).get? 0 = some a
      · obtain ⟨a, ha⟩ := h
        exact ⟨m, a, ha⟩
      · obtain ⟨a, ha⟩ := exists_get?_zero_of_ne_one hm
        exists m + 1, a
        rw [Monoid.partialProd_succ,
          show (0 : ℕ) = 0 + 0 from rfl, get?_mul_of_terminatedAt (by omega) ?_]
        · exact ha
        · exact Option.eq_none_iff_forall_ne_some.mpr (λ a ha ↦ h ⟨a, ha⟩)
    | succ k ih =>
      obtain ⟨n, a, ha⟩ := ih
      obtain ⟨m, hnm, hm⟩ := hne n
      have hsa : (Monoid.partialProd e m).get? k = some a := get?_partialProd_of_le hnm ha
      by_cases h : ∃ b, (Monoid.partialProd e m).get? (k + 1) = some b
      · obtain ⟨b, hb⟩ := h
        exact ⟨m, b, hb⟩
      · obtain ⟨b, hb⟩ := exists_get?_zero_of_ne_one hm
        exists m + 1, b
        rw [Monoid.partialProd_succ, show k + 1 = k + 1 + 0 from rfl,
          get?_mul_of_terminatedAt ?_ ?_]
        · exact hb
        · intro i hi hterm
          have hik : i ≤ k := by omega
          rw [le_stable _ hik hterm] at hsa
          contradiction
        · exact Option.eq_none_iff_forall_ne_some.mpr (λ b hb ↦ h ⟨b, hb⟩)

  /-- A `Seq` having every partial product as a left factor is the product, once the factors keep
  coming. Predicate-free for the same reason as `exists_mul_ωProduct`. -/
  theorem ωProduct_eq_of_forall_dvd {e : ℕ → Seq α} {x : Seq α}
      (hx : ∀ n, ∃ r, x = Monoid.partialProd e n * r) (hne : ∀ n, ∃ m, n ≤ m ∧ e m ≠ 1) :
      x = ωProduct e := by
    apply Seq.ext
    intro k
    apply Option.ext
    intro a
    iff_intro hk hk
    · obtain ⟨n, b, hb⟩ := exists_get?_partialProd hne k
      obtain ⟨r, hr⟩ := hx n
      have hxb : x.get? k = some b := by
        rw [hr]
        exact get?_mul_of_get? _ hb
      rw [hxb] at hk
      apply get?_ωProduct.mpr
      exact ⟨n, hk ▸ hb⟩
    · obtain ⟨n, hn⟩ := get?_ωProduct.mp hk
      obtain ⟨r, hr⟩ := hx n
      rw [hr]
      exact get?_mul_of_get? _ hn
end Stream'.Seq

end
