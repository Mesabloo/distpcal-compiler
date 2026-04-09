import Extra.Topology.IMetricSpace

open scoped unitInterval
open Classical

/-!
  ## `IMetricSpace (List α)` via the discrete metric

  We equip `List α` with the discrete `IMetricSpace` instance, regardless of whether `α`
  carries any metric or decidability structure:
    `idist xs ys = 0` if `xs = ys`, and `idist xs ys = 1` otherwise.

  Motivation:
  - Lists in this project are finite bookkeeping structures (scope stacks `ϙ`, channel
    environments `ξ`, statement sequences). They are constructed statically from syntax
    and never approximated by convergent sequences of "nearby" lists.
  - The `Store` isometry `Store.type ≃ᵢ X × List Y` requires only that `List Y` carry a
    well-defined `IMetricSpace`; no continuity of list operations is needed.
  - `DecidableEq` cannot be assumed: element types such as `String →ᵤ Option Address` are
    function types with no decidable equality. `open Classical` is appropriate since all
    metric instances in this project are noncomputable.
  - `CompleteSpace (List α)` holds unconditionally: every Cauchy sequence is eventually
    constant (open balls of radius `< 1` are singletons under the discrete metric).
-/

/-- The discrete `IMetricSpace` on `List α`, requiring no structure on `α`. -/
noncomputable instance instIMetricSpaceList {α} : IMetricSpace (List α) where
  idist xs ys := if xs = ys then (0 : I) else (1 : I)
  idist_self xs := by simp
  idist_comm xs ys := by
    congr 1
    exact propext ⟨Eq.symm, Eq.symm⟩
  idist_triangle xs ys zs := by
    by_cases h1 : xs = ys <;> by_cases h2 : ys = zs
    · subst h1 h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · -- xs ≠ ys and ys ≠ zs: both summands on the RHS are 1
      simp [h1, h2]
      split_ifs
      · change (0 : ℝ) ≤ 1 + 1; norm_num
      · change (1 : ℝ) ≤ 1 + 1; norm_num
  eq_of_idist_eq_zero xs ys h := by
    split_ifs at h with heq
    · exact heq
    · exact absurd h one_ne_zero

lemma List.idist_eq {α} (xs ys : List α) :
    idist xs ys = if xs = ys then (0 : I) else (1 : I) := rfl

/-- The discrete metric on `List α` induces the discrete topology. -/
lemma List.discreteTopology {α} : DiscreteTopology (List α) := by
  rw [discreteTopology_iff_nhds]
  intro xs
  apply le_antisymm _ (pure_le_nhds xs)
  rw [Filter.le_def]
  intro s hs
  rw [Filter.mem_pure] at hs
  rw [IMetric.mem_nhds_iff]
  exists 1/2, one_half_pos
  intros ys hy
  simp only [IMetric.ball, Set.mem_setOf_eq] at hy
  have heq : ys = xs := by
    by_contra h
    rw [List.idist_eq, if_neg h] at hy
    change (1 : ℝ) < 1/2 at hy
    norm_num at hy
  rwa [heq]

/-- `List α` is complete under the discrete metric: every Cauchy sequence is eventually
constant, hence converges. -/
instance instCompleteSpaceList {α} : CompleteSpace (List α) := by
  haveI := List.discreteTopology (α := α)
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  rw [Metric.cauchySeq_iff] at hu
  obtain ⟨N, hN⟩ := hu (1/2) (by norm_num)
  have hev : ∀ m ≥ N, u m = u N := by
    intro m hm
    have h := hN m hm N (le_refl N)
    simp only [dist] at h
    rw [List.idist_eq] at h
    split_ifs at h with heq
    · exact heq
    · change (1 : ℝ) < 1/2 at h; norm_num at h
  exists u N
  apply tendsto_const_nhds.congr'
  exact Filter.eventually_atTop.mpr ⟨N, λ n hn ↦ (hev n hn).symm⟩
