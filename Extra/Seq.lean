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
end Stream'.Seq

end
