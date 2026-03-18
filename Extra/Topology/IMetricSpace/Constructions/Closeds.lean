import Extra.Topology.IMetricSpace
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.UniformSpace.Closeds
import Extra.Topology.ClosedEmbedding.Tactic

open TopologicalSpace (Closeds)

universe u

noncomputable def Metric.hausdorffInfIDist {α} [PseudoIMetricSpace α] (x : α) (s : Set α) :=
  ⨅ y ∈ s, idist x y

noncomputable abbrev Metric.hausdorffIDist {α} [PseudoIMetricSpace α] (s t : Set α) :=
  max (⨆ x ∈ s, Metric.hausdorffInfIDist x t) (⨆ y ∈ s, Metric.hausdorffInfIDist y s)

noncomputable abbrev PseudoIMetricSpace.hausdorff {α} [IMetricSpace α] : PseudoIMetricSpace (Set α) where
  idist := Metric.hausdorffIDist
  idist_self := sorry
  idist_comm := sorry
  idist_triangle := sorry
  toUniformSpace := .hausdorff α
  uniformity_idist := by
    admit

/-- Two closed sets are at zero Hausdorff edistance if and only if they coincide. -/
theorem _root_.IsClosed.hausdorffIDist_zero_iff {α} {s t : Set α} [PseudoIMetricSpace α] (hs : IsClosed s) (ht : IsClosed t) :
    Metric.hausdorffIDist s t = 0 ↔ s = t := by
  admit

noncomputable instance {α : Type u} [IMetricSpace α] : IMetricSpace (Closeds α) where
  __ := PseudoIMetricSpace.hausdorff.induced SetLike.coe
  eq_of_idist_eq_zero s t h := by
    apply Closeds.ext
    erwa [IsClosed.hausdorffIDist_zero_iff] at h
    · exact s.isClosed
    · exact t.isClosed

instance (priority := high) Closeds.instCompleteSpace {α : Type u} [IMetricSpace α] [CompleteSpace α] : CompleteSpace (Closeds α) := by
  sorry

-- instance {α} [TopologicalSpace α] : TopologicalSpace (Closeds α) :=
--   .induced SetLike.coe (TopologicalSpace.vietoris α)

def Closeds.map {α β} [IMetricSpace α] [IMetricSpace β] (f : α → β) (hf : Topology.IsClosedEmbedding f) (x : Closeds α) : Closeds β where
  carrier := f '' ↑x
  isClosed' := by
    rw [← Topology.IsClosedEmbedding.isClosed_iff_image_isClosed]
    · exact Closeds.isClosed x
    · exact hf

def Closeds.closed_map {α β} [IMetricSpace α] [IMetricSpace β] (f : α → β) (x : Closeds α) : Closeds β where
  carrier := closure (f '' ↑x)
  isClosed' := isClosed_closure

theorem Closeds.closed_map_eq_map_of_closed_embedding {α β} [IMetricSpace α] [IMetricSpace β] {f : α → β}
  (hf : Topology.IsClosedEmbedding f) :
    Closeds.map f hf = Closeds.closed_map f := by
  funext x
  refine Closeds.ext ?_
  unfold closed_map map
  rw! [IsClosed.closure_eq]
  · rfl
  · exact Closeds.map f hf x |>.isClosed'

theorem Topology.IsClosedEmbedding.Closeds.closed_map {α β} [IMetricSpace α] [IMetricSpace β] {f : α → β} :
    Topology.IsClosedEmbedding (Closeds.closed_map f) := by

  admit

theorem Topology.IsClosedEmbedding.Closeds.map {α β} [IMetricSpace α] [IMetricSpace β] {f : α → β} (hf : Topology.IsClosedEmbedding f) :
    Topology.IsClosedEmbedding (Closeds.map _ hf) := by
  rw [Closeds.closed_map_eq_map_of_closed_embedding hf]
  exact Topology.IsClosedEmbedding.Closeds.closed_map


macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| apply Topology.IsClosedEmbedding.Closeds.map)
macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| apply Topology.IsClosedEmbedding.Closeds.closed_map)
