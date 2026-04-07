import Extra.Topology.IMetricSpace
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Instances.Int

noncomputable instance : IMetricSpace ℕ := .transportMetricSpace

noncomputable instance : IMetricSpace ℤ := .transportMetricSpace
