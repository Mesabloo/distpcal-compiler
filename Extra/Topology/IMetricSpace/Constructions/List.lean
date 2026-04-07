import Extra.Topology.IMetricSpace

instance {α} [IMetricSpace α] : IMetricSpace (List α) where
  idist := sorry
  idist_self := sorry
  idist_comm := sorry
  idist_triangle := sorry
  eq_of_idist_eq_zero := sorry
