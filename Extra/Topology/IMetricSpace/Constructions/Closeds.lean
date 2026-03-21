import Extra.Topology.IMetricSpace
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.UniformSpace.Closeds
-- import Extra.Topology.ClosedEmbedding.Tactic
import Extra.Topology.ClosedEmbedding

open TopologicalSpace (Closeds)

universe u

noncomputable def IMetric.hausdorffInfIDist {α} [PseudoIMetricSpace α] (x : α) (s : Set α) :=
  ⨅ y ∈ s, idist x y

noncomputable abbrev IMetric.hausdorffIDist {α} [PseudoIMetricSpace α] (s t : Set α) :=
  max (⨆ x ∈ s, IMetric.hausdorffInfIDist x t) (⨆ y ∈ s, IMetric.hausdorffInfIDist y s)

theorem IMetric.hausdorffIDist_image {α β} [PseudoIMetricSpace α] [PseudoIMetricSpace β] {s t : Set α} {Φ : α → β} (h : Isometry Φ) :
    hausdorffIDist (Φ '' s) (Φ '' t) = hausdorffIDist s t :=
  sorry

noncomputable instance PseudoIMetricSpace.hausdorff {α} [IMetricSpace α] : PseudoIMetricSpace (Set α) where
  idist := IMetric.hausdorffIDist
  idist_self := sorry
  idist_comm := sorry
  idist_triangle := sorry
  toUniformSpace := .hausdorff α
  uniformity_idist := by
    admit

noncomputable instance IMetricSpace.hausdorff {α} [IMetricSpace α] : IMetricSpace (Set α) where
  eq_of_idist_eq_zero := by
    admit


/-- Two closed sets are at zero Hausdorff edistance if and only if they coincide. -/
theorem _root_.IsClosed.hausdorffIDist_zero_iff {α} {s t : Set α} [PseudoIMetricSpace α] (hs : IsClosed s) (ht : IsClosed t) :
    IMetric.hausdorffIDist s t = 0 ↔ s = t := by
  admit

noncomputable instance {α : Type u} [IMetricSpace α] : IMetricSpace (Closeds α) :=
  IMetricSpace.hausdorff.induced SetLike.coe SetLike.coe_injective'
  -- eq_of_idist_eq_zero s t h := by
  --   apply Closeds.ext
  --   erwa [IsClosed.hausdorffIDist_zero_iff] at h
  --   · exact s.isClosed
  --   · exact t.isClosed

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

theorem Closeds.map_isometry' {α β} [IMetricSpace α] [IMetricSpace β] {f : α → β} (hf : Topology.IsClosedEmbedding f)
  (hf' : ∀ x y, idist (f x) (f y) = idist x y) :
    ∀ x y, idist (Closeds.map _ hf x) (Closeds.map _ hf y) = idist x y := by
  change ∀ (x y : Closeds α), idist (f '' ↑x) (f '' ↑y) = idist x y
  exact λ _ _ ↦ IMetric.hausdorffIDist_image (Isometry.of_idist_eq hf')

theorem Closeds.map_isometry {α β} [IMetricSpace α] [IMetricSpace β] {f : α → β} (hf : Topology.IsClosedEmbedding f) (hf' : Isometry f) :
    Isometry (Closeds.map _ hf) := by
  apply Isometry.of_idist_eq
  apply Closeds.map_isometry'
  apply Isometry.to_idist_eq
  assumption

-- theorem Topology.IsClosedEmbedding.Closeds.closed_map {α β} [IMetricSpace α] [IMetricSpace β] {f : α → β} :
--     Topology.IsClosedEmbedding (Closeds.closed_map f) where
--   eq_induced := by
--     admit
--   injective := by
--     admit
--   isClosed_range := by
--     admit

-- theorem Topology.IsClosedEmbedding.Closeds.map {α β} [IMetricSpace α] [IMetricSpace β] {f : α → β}
--   (hf : Topology.IsClosedEmbedding f) (hf' : Isometry f) :
--     Topology.IsClosedEmbedding (Closeds.map _ hf) where
--   eq_induced := by

--     admit
--   injective := by
--     replace hf : Function.Injective (Set.image f) := by
--       rw [Set.image_injective]
--       exact hf.injective

--     intros x y h
--     rw [Closeds.ext_iff] at h ⊢
--     exact hf h
--   isClosed_range := by

--     admit

theorem Closeds.map_comp {α β γ} [IMetricSpace α] [IMetricSpace β] [IMetricSpace γ] {f : α → β} {g : β → γ}
  (hf : Topology.IsClosedEmbedding f) (hg : Topology.IsClosedEmbedding g) :
    Closeds.map _ hg ∘ Closeds.map _ hf = Closeds.map _ (hg.comp hf) := by
  funext _
  simp [Closeds.map, Set.image_image]

macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| apply Topology.IsClosedEmbedding.Closeds.map)
-- macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| apply Topology.IsClosedEmbedding.Closeds.closed_map)
