import Mathlib.Data.Finset.Basic

namespace Finset
  theorem disjoint_sdiff_sdiff_of_disjoint.{u} {α : Type u} [DecidableEq α] {s t u : Finset α} (h : Disjoint s u) : Disjoint (s \ t) (u \ t) := by
    simp_rw [Finset.disjoint_iff_ne, Finset.mem_sdiff, and_imp]
    intros x x_in_s x_not_in_t y y_in_u y_not_in_t
    exact Disjoint.forall_ne_finset h x_in_s y_in_u

  theorem not_mem_of_not_mem_sdiff.{u} {α : Type u} [DecidableEq α] {x : α} {t u : Finset α} (h : x ∉ t) (h' : x ∉ u \ t) : x ∉ u := by
    simp_all
