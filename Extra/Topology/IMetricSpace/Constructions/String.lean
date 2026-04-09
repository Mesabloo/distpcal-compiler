import Extra.Topology.IMetricSpace

open scoped unitInterval

/-!
  ## `IMetricSpace String` via the discrete metric

  We equip `String` with the discrete `IMetricSpace` instance:
  `idist s t = 0` if `s = t`, and `idist s t = 1` otherwise.

  This is the correct choice for two reasons:
  - `String` is the `.str` summand of `𝕍` (a direct data constructor in `Value.F`), so its
    metric contributes to the metric on `𝕍` via the `⊕` construction. Programs only test
    string equality, so the discrete metric faithfully captures the only observable proximity.
  - The label-type occurrences of `String` (domains of `String →ᵤ Option ℍ` in `.struct`
    and `.func`) do not depend on `IMetricSpace String`: the uniform topology on the domain
    of a `→ᵤ` does not enter the sup-metric on the function space.
  Levenshtein distance is unavailable: `Mathlib.Data.List.EditDistance` is absent from the
  pinned Mathlib version (v4.29.0-rc1).
-/

/-- The discrete `IMetricSpace` on `String`. -/
noncomputable instance instIMetricSpaceString : IMetricSpace String where
  idist s t := if s = t then (0 : I) else (1 : I)
  idist_self s := by simp
  idist_comm s t := by
    congr 1
    exact propext ⟨Eq.symm, Eq.symm⟩
  idist_triangle s t u := by
    by_cases h1 : s = t <;> by_cases h2 : t = u
    · subst h1 h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · -- s ≠ t and t ≠ u: both summands on the RHS are 1
      simp [h1, h2]
      split_ifs
      · change (0 : ℝ) ≤ 1 + 1; norm_num
      · change (1 : ℝ) ≤ 1 + 1; norm_num
  eq_of_idist_eq_zero s t h := by
    split_ifs at h with heq
    · exact heq
    · exact absurd h one_ne_zero

lemma String.idist_eq (s t : String) : idist s t = if s = t then (0 : I) else (1 : I) := rfl

/-- The discrete metric on `String` induces the discrete topology. -/
lemma String.discreteTopology : DiscreteTopology String := by
  rw [discreteTopology_iff_nhds]
  intro x
  apply le_antisymm _ (pure_le_nhds x)
  rw [Filter.le_def]
  intro s hs
  rw [Filter.mem_pure] at hs
  rw [IMetric.mem_nhds_iff]
  exists 1/2, one_half_pos
  intros y hy
  simp only [IMetric.ball, Set.mem_setOf_eq] at hy
  have heq : y = x := by
    by_contra h
    rw [String.idist_eq, if_neg h] at hy
    change (1 : ℝ) < 1/2 at hy
    norm_num at hy
  rw [heq]; exact hs

/-- `String` is complete under the discrete metric: every Cauchy sequence is eventually
constant, hence converges. -/
instance : CompleteSpace String := by
  haveI := String.discreteTopology
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  rw [Metric.cauchySeq_iff] at hu
  obtain ⟨N, hN⟩ := hu (1/2) (by norm_num)
  have hev : ∀ m ≥ N, u m = u N := by
    intro m hm
    have h := hN m hm N (le_refl N)
    simp only [dist] at h
    rw [String.idist_eq] at h
    split_ifs at h with heq
    · exact heq
    · change (1 : ℝ) < 1/2 at h; norm_num at h
  exists u N
  apply tendsto_const_nhds.congr'
  exact Filter.eventually_atTop.mpr ⟨N, λ n hn ↦ (hev n hn).symm⟩
