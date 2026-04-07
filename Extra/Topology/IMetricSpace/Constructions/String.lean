import Extra.Topology.IMetricSpace

instance : IMetricSpace String where
  idist := sorry -- Levenshtein distance
  idist_self := sorry
  idist_comm := sorry
  idist_triangle := sorry
  eq_of_idist_eq_zero := sorry
