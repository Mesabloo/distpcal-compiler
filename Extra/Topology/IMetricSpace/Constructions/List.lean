import Extra.Topology.IMetricSpace

open scoped unitInterval

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
noncomputable instance instIMetricSpaceList {α} [DecidableEq α] : DiscreteIMetricSpace (List α) where
  __ := IMetricSpace.discrete

lemma List.idist_eq {α} [DecidableEq α] (xs ys : List α) :
    idist xs ys = if xs = ys then (0 : I) else (1 : I) := rfl

/-- The discrete metric on `List α` induces the discrete topology. -/
lemma List.discreteTopology {α} [DecidableEq α] : DiscreteTopology (List α) :=
  inferInstance

/-- `List α` is complete under the discrete metric: every Cauchy sequence is eventually
constant, hence converges. -/
instance instCompleteSpaceList {α} [DecidableEq α] : CompleteSpace (List α) :=
  DiscreteIMetricSpace.completeSpace
