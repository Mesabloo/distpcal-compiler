import Extra.Topology.IMetricSpace
import Mathlib.Topology.MetricSpace.Gluing

instance {α β} [IMetricSpace α] [IMetricSpace β] : IDist (α ⊕ β) where
  idist
    | .inl x, .inl y | .inr x, .inr y => idist x y
    | .inl _, .inr _ | .inr _, .inl _ => ⊤

open Uniformity in
theorem Sum.mem_uniformity {X Y} [IMetricSpace X] [IMetricSpace Y] (s : Set ((X ⊕ Y) × (X ⊕ Y))) :
    s ∈ 𝓤 (X ⊕ Y) ↔ ∃ ε > 0, ∀ a b, (idist a b : ℝ) < ε → (a, b) ∈ s := by
  constructor
  · rintro ⟨hsX, hsY⟩
    rcases IMetric.mem_uniformity_idist.1 hsX with ⟨εX, εX0, hX⟩
    rcases IMetric.mem_uniformity_idist.1 hsY with ⟨εY, εY0, hY⟩
    refine ⟨min (min εX εY) 1, lt_min (lt_min εX0 εY0) zero_lt_one, ?_⟩
    rintro (a | a) (b | b) h
    · exact hX (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_left _ _)))
    · cases not_le_of_gt (lt_of_lt_of_le h (min_le_right _ _)) (by rfl)
    · cases not_le_of_gt (lt_of_lt_of_le h (min_le_right _ _)) (by rfl)
    · exact hY (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_right _ _)))
  · rintro ⟨ε, ε0, H⟩
    constructor <;> rw [Filter.mem_map, IMetric.mem_uniformity_idist] <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩

instance Sum.instIMetricSpace {α β} [IMetricSpace α] [IMetricSpace β] : IMetricSpace (α ⊕ β) where
  idist_self x := by
    cases x <;> dsimp <;> erw [idist_self] <;> rfl
  idist_comm x y := by
    cases x <;> cases y <;> first
      | rfl
      | erw [idist_comm]; rfl
  idist_triangle x y z := by
    cases x <;> cases y <;> cases z
    · apply idist_triangle
    · change ↑(⊤ : unitInterval) ≤ (_ : ℝ) + ↑(⊤ : unitInterval)
      grind only [= Set.mem_Icc]
    · change (_ : ℝ) ≤ ↑(⊤ : unitInterval) + ↑(⊤ : unitInterval)
      grind only [= Set.mem_Icc, unitInterval.coe_ne_one, unitInterval.top_eq]
    · change ↑(⊤ : unitInterval) ≤ ↑(⊤ : unitInterval) + (_ : ℝ)
      grind only [= Set.mem_Icc]
    · change ↑(⊤ : unitInterval) ≤ ↑(⊤ : unitInterval) + (_ : ℝ)
      grind only [= Set.mem_Icc]
    · change (_ : ℝ) ≤ ↑(⊤ : unitInterval) + ↑(⊤ : unitInterval)
      grind only [= Set.mem_Icc, unitInterval.coe_ne_one, unitInterval.top_eq]
    · change ↑(⊤ : unitInterval) ≤ (_ : ℝ) + ↑(⊤ : unitInterval)
      grind only [= Set.mem_Icc]
    · apply idist_triangle
  eq_of_idist_eq_zero x y h := by
    cases x <;> cases y <;> dsimp at h
    · apply eq_of_idist_eq_zero at h
      rw [h]
    · change 1 = 0 at h
      grind only [unitInterval.coe_ne_one, unitInterval.coe_ne_zero]
    · change 1 = 0 at h
      grind only [unitInterval.coe_ne_one, unitInterval.coe_ne_zero]
    · apply eq_of_idist_eq_zero at h
      rw [h]
  toUniformSpace := Sum.instUniformSpace
  uniformity_idist := by
    apply uniformity_dist_of_mem_uniformity _ (λ x y ↦ idist x y : _ → _ → ℝ)
    apply Sum.mem_uniformity

theorem Isometry.sumMap' {W X Y Z} {f : W → X} {g : Y → Z} [IMetricSpace W] [IMetricSpace X] [IMetricSpace Y] [IMetricSpace Z]
  (hf : ∀ x y, idist (f x) (f y) = idist x y) (hg : ∀ x y, idist (g x) (g y) = idist x y) :
    ∀ x y, idist (Sum.map f g x) (Sum.map f g y) = idist x y := by
  intros x y
  rcases x, y with ⟨x|x, y|y⟩
  · erw [hf]; rfl
  · rfl
  · rfl
  · erw [hg]; rfl

theorem Isometry.sumMap {W X Y Z} {f : W → X} {g : Y → Z} [IMetricSpace W] [IMetricSpace X] [IMetricSpace Y] [IMetricSpace Z]
  (hf : Isometry f) (hg : Isometry g) :
    Isometry (Sum.map f g) := by
  apply Isometry.of_idist_eq
  apply Isometry.sumMap'
  · apply Isometry.to_idist_eq
    assumption
  · apply Isometry.to_idist_eq
    assumption

---------

nonrec abbrev Sigma.idist {α} {β : α → _} [DecidableEq α] [(x : α) → IDist (β x)] (x y : Sigma β) : unitInterval :=
  if h : x.1 = y.1 then idist (h ▸ x.2) y.2 else ⊤

theorem Sigma.idist_self {α} {β : α → _} [DecidableEq α] [(x : α) → PseudoIMetricSpace (β x)] (x : Sigma β) : Sigma.idist x x = 0 := by
  grind only [PseudoIMetricSpace.idist_self]

theorem Sigma.idist_comm {α} {β : α → _} [DecidableEq α] [(x : α) → PseudoIMetricSpace (β x)] (x y : Sigma β) : Sigma.idist x y = Sigma.idist y x := by
  grind only [= Set.mem_Icc, unitInterval.coe_ne_one, unitInterval.coe_ne_zero, unitInterval.top_eq,
    = Set.Ioc.mk_one, = Set.mem_Ioc, unitInterval.coe_lt_one, unitInterval.lt_one_iff_ne_one,
    PseudoIMetricSpace.idist_comm]

theorem Sigma.idist_triangle {α} {β : α → _} [DecidableEq α] [(x : α) → PseudoIMetricSpace (β x)] (x y z : Sigma β) :
    (Sigma.idist x z : ℝ) ≤ Sigma.idist x y + Sigma.idist y z := by
  grind only [idist_comm, = Set.mem_Icc, unitInterval.coe_ne_one, unitInterval.coe_ne_zero,
    unitInterval.top_eq, = Set.Ioc.mk_one, = Set.mem_Ioc, unitInterval.coe_lt_one,
    unitInterval.lt_one_iff_ne_one, PseudoIMetricSpace.idist_comm,
    PseudoIMetricSpace.idist_triangle]

nonrec theorem Sigma.eq_of_idist_eq_zero {α} {β : α → _} [DecidableEq α] [(x : α) → IMetricSpace (β x)] (x y : Sigma β) (h : Sigma.idist x y = 0) : x = y := by
  unfold Sigma.idist at h
  split_ifs at h with heq
  · let ⟨x1, x2⟩ := x
    let ⟨y1, y2⟩ := y

    cases heq

    congr
    apply eq_of_idist_eq_zero
    assumption
  · grind only [unitInterval.coe_ne_one, unitInterval.coe_ne_zero, unitInterval.top_eq]

theorem Sigma.idist_same {ι} {E : ι → _} [DecidableEq ι] [∀ i, IMetricSpace (E i)] (i : ι) (x y : E i) :
    idist (Sigma.mk i x) ⟨i, y⟩ = IDist.idist x y := by
  unfold Sigma.idist
  rw [dif_pos rfl]

theorem Sigma.idist_eq_top_of_ne {ι} {E : ι → _} [DecidableEq ι] [∀ i, IMetricSpace (E i)] {i j : ι} {x : E i} {y : E j} (h : i ≠ j) :
    idist (Sigma.mk i x) ⟨j, y⟩ = ⊤ := by
  unfold idist
  rw [dif_neg h]

theorem Sigma.fst_eq_of_dist_lt_one {ι} {E : ι → _} [DecidableEq ι] [∀ i, IMetricSpace (E i)] (x y : Σ i, E i) (h : idist x y < 1) : x.1 = y.1 := by
  cases x; cases y
  contrapose! h
  apply le_of_eq
  exact Sigma.idist_eq_top_of_ne h |>.symm

theorem Sigma.isOpen_iff' {ι} {E : ι → _} [DecidableEq ι] [∀ i, IMetricSpace (E i)] (s : Set (Σ i, E i)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, (idist x y : ℝ) < ε → y ∈ s := by
  iff_intro hs H
  · rintro ⟨i, x⟩ hx
    obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, Metric.ball x ε ⊆ Sigma.mk i ⁻¹' s :=
      Metric.isOpen_iff.1 (isOpen_sigma_iff.1 hs i) x hx
    refine ⟨min ε 1, lt_min εpos zero_lt_one, ?_⟩
    rintro ⟨j, y⟩ hy
    rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.idist_same, lt_min_iff] at hy
      exact hε (IMetric.mem_ball'.2 hy.1)
    · apply (lt_irrefl (1 : ℝ) _).elim
      calc
        1 = Sigma.idist ⟨i, x⟩ ⟨j, y⟩ := Sigma.idist_eq_top_of_ne hij |>.symm
        _ < 1 := hy.trans_le (min_le_right _ _)
  · refine isOpen_sigma_iff.2 fun i => IMetric.isOpen_iff.2 fun x hx => ?_
    obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ∀ y, (idist (⟨i, x⟩ : Σ j, E j) y : ℝ) < ε → y ∈ s :=
      H ⟨i, x⟩ hx
    refine ⟨ε, εpos, fun y hy => ?_⟩
    apply hε ⟨i, y⟩
    rw [Sigma.idist_same]
    exact IMetric.mem_ball'.1 hy

instance {α} {β : _ → _} [DecidableEq α] [(x : α) → IMetricSpace (β x)] : IMetricSpace (Σ x, β x) :=
  .ofIDistTopology Sigma.idist Sigma.idist_self Sigma.idist_comm Sigma.idist_triangle Sigma.isOpen_iff' Sigma.eq_of_idist_eq_zero

/-- The injection of a space in a disjoint union is an isometry -/
theorem Sigma.isometry_mk {ι} {E : ι → _} [DecidableEq ι] [∀ i, IMetricSpace (E i)] (i : ι) : Isometry (Sigma.mk i : E i → Σ k, E k) :=
  Isometry.of_idist_eq fun x y => Sigma.idist_same i x y

instance Sigma.completeSpace {ι} {E : ι → _} [DecidableEq ι] [∀ i, IMetricSpace (E i)] [∀ i, CompleteSpace (E i)] : CompleteSpace (Σ i, E i) := by
  set s : ι → Set (Σ i, E i) := fun i => Sigma.fst ⁻¹' {i}
  set U := { p : (Σ k, E k) × Σ k, E k | idist p.1 p.2 < 1 }
  have hc : ∀ i, IsComplete (s i) := fun i => by
    simp only [s, ← Set.range_sigmaMk]
    exact (Sigma.isometry_mk i).isUniformInducing.isComplete_range
  have hd : ∀ (i j), ∀ x ∈ s i, ∀ y ∈ s j, (x, y) ∈ U → i = j := fun i j x hx y hy hxy =>
    (Eq.symm hx).trans ((fst_eq_of_dist_lt_one _ _ hxy).trans hy)
  refine completeSpace_of_isComplete_univ ?_
  convert isComplete_iUnion_separated hc (IMetric.idist_mem_uniformity zero_lt_one) hd
  simp only [s, ← Set.preimage_iUnion, Set.iUnion_of_singleton, Set.preimage_univ]
