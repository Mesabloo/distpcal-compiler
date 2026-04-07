import Extra.Topology.IMetricSpace

namespace Bool
  open unitInterval

  protected def idist (x y : Bool) : I := if x = y then ⊥ else ⊤

  protected theorem idist_self (x : Bool) : Bool.idist x x = 0 := by
    unfold Bool.idist
    rw [if_pos rfl]
    rfl

  protected theorem idist_comm (x y : Bool) : Bool.idist x y = Bool.idist y x := by
    grind only [= Bool.idist]

  protected theorem idist_triangle (x y z : Bool) :
      (Bool.idist x z : ℝ) ≤ Bool.idist x y + Bool.idist y z := by
    grind only [= Bool.idist, = Set.mem_Icc, usr Subtype.property, unitInterval.bot_eq,
      unitInterval.coe_ne_one, unitInterval.coe_ne_zero, unitInterval.top_eq,
      unitInterval.zero_eq]

  protected theorem isOpen_iff (s : Set Bool) :
      IsOpen s ↔ ∀ x ∈ s, ∃ ε > (0 : ℝ), ∀ (y : Bool), ↑(Bool.idist x y) < ε → y ∈ s := by
    admit

  protected theorem eq_of_idist_eq_zero (x y : Bool) (h : Bool.idist x y = 0) : x = y := by
    unfold Bool.idist at h
    split at h
    · assumption
    · grind only [unitInterval.coe_ne_one, unitInterval.coe_ne_zero, unitInterval.top_eq]

  open Filter in
  instance : IMetricSpace Bool :=
    .ofIDistTopology Bool.idist Bool.idist_self Bool.idist_comm Bool.idist_triangle
      Bool.isOpen_iff Bool.eq_of_idist_eq_zero
end Bool
