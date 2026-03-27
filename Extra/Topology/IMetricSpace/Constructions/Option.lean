import Extra.Topology.IMetricSpace

instance {α} [IMetricSpace α] : IMetricSpace (Option α) where
  idist
    | .none, .none => ⊥
    | .some x, .some y => idist x y
    | .some _, .none | .none, .some _ => ⊤
  idist_self x := by cases x <;> first | rfl | grind only [idist_self]
  idist_comm x y := by
    cases x <;> cases y <;> first | rfl | grind only [idist_comm]
  idist_triangle x y z := by
    cases x <;> cases y <;> cases z <;>
      grind only [= Set.mem_Icc, unitInterval.bot_eq, unitInterval.coe_ne_one, unitInterval.coe_ne_zero,
        unitInterval.top_eq, idist_triangle]
  eq_of_idist_eq_zero {x y} h := by
    split at h <;> grind only [eq_of_idist_eq_zero, unitInterval.coe_ne_one, unitInterval.coe_ne_zero, unitInterval.top_eq]
