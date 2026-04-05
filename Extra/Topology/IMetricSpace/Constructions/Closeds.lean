import Extra.Topology.IMetricSpace
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.UniformSpace.Closeds
-- import Mathlib.Topology.MetricSpace.Closeds
-- import Extra.Topology.ClosedEmbedding.Tactic
import Extra.Topology.ClosedEmbedding

open TopologicalSpace (Closeds)

universe u

namespace IMetric
  noncomputable def hausdorffInfIDist {α} [PseudoIMetricSpace α] (x : α) (s : Set α) :=
    ⨅ y ∈ s, idist x y

  noncomputable abbrev hausdorffIDist {α} [PseudoIMetricSpace α] (s t : Set α) :=
    max (⨆ x ∈ s, IMetric.hausdorffInfIDist x t) (⨆ y ∈ t, IMetric.hausdorffInfIDist y s)

  theorem hausdorffIDist_self {α} [PseudoIMetricSpace α] {s : Set α} :
      hausdorffIDist s s = 0 := by
    unfold hausdorffIDist hausdorffInfIDist

    change _ = ⊥
    simp only [← iSup_union, Set.union_self, iSup₂_eq_bot, iInf₂_eq_bot]
    intros x x_in_s b b_pos
    exists x, x_in_s
    rwa [idist_self]

  theorem hausdorffIDist_comm {α} [PseudoIMetricSpace α] {s t : Set α} :
      hausdorffIDist s t = hausdorffIDist t s := by
    unfold hausdorffIDist
    erw [max_comm]

  theorem hausdorffIDist_idist_triangle {α} [PseudoIMetricSpace α] {s t u : Set α} :
      (hausdorffIDist s u : ℝ) ≤ hausdorffIDist s t + hausdorffIDist t u := by
    admit

  theorem hausdorffIDist_eq_of_idist_eq_zero {α} [IMetricSpace α] {s t : Set α} (h : hausdorffIDist s t = 0) :
      s = t := by
    unfold hausdorffIDist at h
    erw [sup_eq_bot_iff, iSup₂_eq_bot, iSup₂_eq_bot] at h
    admit

  theorem hausdorffIDist_image_le {α β} [PseudoIMetricSpace α] [PseudoIMetricSpace β] {s t : Set α} {Φ : α → β} (h : ∀ x y, idist (Φ x) (Φ y) ≤ idist x y) :
      hausdorffIDist (Φ '' s) (Φ '' t) ≤ hausdorffIDist s t :=
    sorry

  theorem hausdorffIDist_image {α β} [PseudoIMetricSpace α] [PseudoIMetricSpace β] {s t : Set α} {Φ : α → β} (h : Isometry Φ) :
      hausdorffIDist (Φ '' s) (Φ '' t) = hausdorffIDist s t :=
    sorry

  theorem hausdorffIDist_closure {α} [PseudoIMetricSpace α] {s t : Set α} :
      hausdorffIDist (closure s) (closure t) = hausdorffIDist s t := by
    admit

  theorem hausdorffIDist_zero_iff_closure_eq_closure {α} [IMetricSpace α] {s t : Set α} :
      hausdorffIDist s t = 0 ↔ closure s = closure t := by
    rw [← hausdorffIDist_closure]
    iff_intro h h
    · apply hausdorffIDist_eq_of_idist_eq_zero
      assumption
    · rw [h, hausdorffIDist_self]
end IMetric

noncomputable instance PseudoIMetricSpace.hausdorff {α} [PseudoIMetricSpace α] : PseudoIMetricSpace (Set α) where
  idist := IMetric.hausdorffIDist
  idist_self _ := IMetric.hausdorffIDist_self
  idist_comm _ _ := IMetric.hausdorffIDist_comm
  idist_triangle _ _ _ := IMetric.hausdorffIDist_idist_triangle
  toUniformSpace := .hausdorff α
  uniformity_idist := by
    admit

noncomputable instance IMetricSpace.hausdorff {α} [IMetricSpace α] : IMetricSpace (Set α) where
  eq_of_idist_eq_zero _ _ := IMetric.hausdorffIDist_eq_of_idist_eq_zero


/-- Two closed sets are at zero Hausdorff edistance if and only if they coincide. -/
theorem _root_.IsClosed.hausdorffIDist_zero_iff {α} {s t : Set α} [IMetricSpace α] :
    IMetric.hausdorffIDist s t = 0 ↔ s = t := by
  change idist s t = 0 ↔ s = t
  exact IMetricSpace.idist_eq_zero_iff

open unitInterval in
theorem IMetric.hausdorffIDist_le_iff {α} [PseudoIMetricSpace α] {s t : Set α} {r : I} :
    IMetric.hausdorffIDist s t ≤ r ↔ (∀ x ∈ s, ∃ y ∈ t, idist x y ≤ r) ∧ (∀ y ∈ t, ∃ x ∈ s, idist x y ≤ r) := by
  sorry

open unitInterval in
theorem IMetric.hausdorffIDist_image_le_of_le_sup {α} [PseudoIMetricSpace α] {s : Set α} {f : α → α} :
    IMetric.hausdorffIDist s (f '' s) ≤ ⨆ x ∈ s, idist x (f x) := by
  rw [IMetric.hausdorffIDist_le_iff]
  constructor
  · intros x x_in
    rw [Set.exists_mem_image]
    exists x, x_in
    apply le_iSup₂ (f := λ x (_ : x ∈ s) ↦ idist x (f x))
    assumption
  · intros y y_in
    rw [Set.mem_image] at y_in
    obtain ⟨x, x_in, rfl⟩ := y_in
    exists x, x_in
    apply le_iSup₂ (f := λ x (_ : x ∈ s) ↦ idist x (f x))
    assumption

theorem Set.image_isometry {α β} {f : α → β} [PseudoIMetricSpace α] [PseudoIMetricSpace β] (hf : Isometry f) :
    Isometry (Set.image f) := by
  apply Isometry.of_idist_eq λ x y ↦ ?_
  exact IMetric.hausdorffIDist_image hf

noncomputable instance {α : Type u} [IMetricSpace α] : IMetricSpace (Closeds α) :=
  IMetricSpace.hausdorff.induced SetLike.coe SetLike.coe_injective'
  -- eq_of_idist_eq_zero s t h := by
  --   apply Closeds.ext
  --   erwa [IsClosed.hausdorffIDist_zero_iff] at h
  --   · exact s.isClosed
  --   · exact t.isClosed

instance (priority := high) Closeds.instCompleteSpace {α : Type u} [IMetricSpace α] [CompleteSpace α] : CompleteSpace (Closeds α) :=
  -- This can't be equal to `TopologicalSpace.Closeds.instCompleteSpace` (from `Mathlib.Topology.MetricSpace.Closeds`)
  -- otherwise there is an instance mismatch further down, when using the completeness of `Closeds α`.
  -- In fact, this module cannot even be imported without clashing with this file's definitions.
  --
  -- So I'll guess we'll have to do the proof again.
  sorry

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

-- macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| apply Topology.IsClosedEmbedding.Closeds.map)
-- macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| apply Topology.IsClosedEmbedding.Closeds.closed_map)
