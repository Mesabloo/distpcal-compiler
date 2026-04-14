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
-/

/-- The discrete `IMetricSpace` on `String`. -/
noncomputable instance instIMetricSpaceString : DiscreteIMetricSpace String where
  __ := IMetricSpace.discrete

lemma String.idist_eq (s t : String) : idist s t = if s = t then ⊥ else ⊤ :=
  PseudoIMetricSpace.discrete.idist_eq

/-- The discrete metric on `String` induces the discrete topology. -/
lemma String.discreteTopology : DiscreteTopology String :=
  inferInstance

/-- `String` is complete under the discrete metric: every Cauchy sequence is eventually
constant, hence converges. -/
instance : CompleteSpace String :=
  DiscreteIMetricSpace.completeSpace
