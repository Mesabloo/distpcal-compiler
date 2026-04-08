import Extra.Topology.IMetricSpace

instance Prod.instPseudoIMetricSpace {α β} [PseudoIMetricSpace α] [PseudoIMetricSpace β] : PseudoIMetricSpace (α × β) :=
  .of_metric_space_of_dist_le_one λ x y ↦ by
    change max (idist x.1 y.1) (idist x.2 y.2) ≤ 1
    apply max_le
    · exact unitInterval.le_one'
    · exact unitInterval.le_one'

instance Prod.instIMetricSpace {α β} [IMetricSpace α] [IMetricSpace β] : IMetricSpace (α × β) :=
  .of_metric_space_of_dist_le_one λ x y ↦ by
    change max (idist x.1 y.1) (idist x.2 y.2) ≤ 1
    apply max_le
    · exact unitInterval.le_one'
    · exact unitInterval.le_one'

theorem Isometry.prodMap' {α β γ δ} [PseudoIMetricSpace α] [PseudoIMetricSpace β] [PseudoIMetricSpace γ] [PseudoIMetricSpace δ]
  {f : α → β} {g : γ → δ} (hf : ∀ x y, idist (f x) (f y) = idist x y) (hg : ∀ x y, idist (g x) (g y) = idist x y) :
    ∀ x y, idist (Prod.map f g x) (Prod.map f g y) = idist x y := by
  apply Isometry.to_idist_eq
  apply Isometry.prodMap
  · apply Isometry.of_idist_eq
    assumption
  · apply Isometry.of_idist_eq
    assumption
