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

  -- Helper: biInf_lt_iff for infIDist
  lemma lt_hausdorffInfIDist_iff {α : Type*} [PseudoIMetricSpace α] (x : α) (s : Set α) (r : unitInterval) :
      IMetric.hausdorffInfIDist x s < r ↔ ∃ y ∈ s, idist x y < r := by
    exact biInf_lt_iff

  -- Empty set gives infIDist = 1 (as real)
  lemma hausdorffInfIDist_empty {α : Type*} [PseudoIMetricSpace α] (x : α) :
      IMetric.hausdorffInfIDist x ∅ = ⊤ := by
    unfold IMetric.hausdorffInfIDist
    haveI : Nonempty α := ⟨x⟩
    simp only [Set.mem_empty_iff_false, iInf_false, unitInterval.top_eq, iInf_const]

  -- infIDist of a point in s to t is ≤ hausdorffIDist s t
  lemma hausdorffIDist_ge_hausdorffInfIDist {α : Type*} [PseudoIMetricSpace α]
      {x : α} {s t : Set α} (hx : x ∈ s) :
      IMetric.hausdorffInfIDist x t ≤ IMetric.hausdorffIDist s t := by
    unfold IMetric.hausdorffIDist IMetric.hausdorffInfIDist
    change ⨅ z ∈ t, idist x z ≤ max (⨆ y ∈ s, ⨅ z ∈ t, idist y z) (⨆ y ∈ t, ⨅ z ∈ s, idist y z)
    exact le_trans (le_iSup₂ (f := fun y _ => ⨅ z ∈ t, idist y z) x hx) le_sup_left

  -- hausdorffIDist s ∅ = 1 when s is nonempty
  lemma hausdorffIDist_empty_right {α : Type*} [PseudoIMetricSpace α] {s : Set α} (hs : s.Nonempty) :
      IMetric.hausdorffIDist s ∅ = ⊤ := by
    obtain ⟨x, hx⟩ := hs
    apply le_antisymm
    · exact OrderTop.le_top (hausdorffIDist s ∅)
    · rw [← hausdorffInfIDist_empty x]
      apply hausdorffIDist_ge_hausdorffInfIDist hx (t := ∅)

  lemma hausdorffIDist_empty_left {α : Type*} [PseudoIMetricSpace α] {t : Set α} (ht : t.Nonempty) :
      IMetric.hausdorffIDist ∅ t = ⊤ := by
    rwa [hausdorffIDist_comm, hausdorffIDist_empty_right]

  -- ε-approximation of infimum (when infIDist < 1)
  private lemma exists_lt_hausdorffInfIDist {α : Type*} [PseudoIMetricSpace α]
      {x : α} {s : Set α} (δ : ℝ) (δ_pos : δ > 0) (h_lt : (IMetric.hausdorffInfIDist x s : ℝ) < 1) :
      ∃ y ∈ s, (idist x y : ℝ) < (IMetric.hausdorffInfIDist x s : ℝ) + δ := by
    have r_mem : min 1 ((IMetric.hausdorffInfIDist x s : ℝ) + δ) ∈ Set.Icc 0 1 :=
      ⟨le_min zero_le_one (by linarith [(IMetric.hausdorffInfIDist x s).2.1]), min_le_left _ _⟩

    set r : unitInterval := ⟨min 1 ((IMetric.hausdorffInfIDist x s : ℝ) + δ), r_mem⟩

    have hr_gt : IMetric.hausdorffInfIDist x s < r := by
      rw [← Subtype.coe_lt_coe]; simp only [r]; exact lt_min h_lt (by linarith)

    rw [lt_hausdorffInfIDist_iff] at hr_gt
    obtain ⟨y, hy, hlt_y⟩ := hr_gt
    exact ⟨y, hy, lt_of_lt_of_le (Subtype.coe_lt_coe.mpr hlt_y) (min_le_right _ _)⟩

  -- Key triangle helper: infIDist x t ≤ infIDist x s + hausdorffIDist s t
  private lemma hausdorffInfIDist_le_add {α : Type*} [PseudoIMetricSpace α] (x : α) (s t : Set α) :
      (IMetric.hausdorffInfIDist x t : ℝ) ≤ IMetric.hausdorffInfIDist x s + IMetric.hausdorffIDist s t := by
    by_cases hs : s = ∅
    · subst hs
      rw [hausdorffInfIDist_empty]
      apply le_add_of_le_of_nonneg
      · exact (IMetric.hausdorffInfIDist x t).2.2
      · exact (IMetric.hausdorffIDist (∅ : Set α) t).2.1
    · by_cases ht : t = ∅
      · subst ht
        rw [hausdorffInfIDist_empty, hausdorffIDist_empty_right (Set.nonempty_iff_ne_empty.mpr hs)]
        linarith [(IMetric.hausdorffInfIDist x s).2.1]
      · apply le_of_forall_pos_le_add
        intro ε ε_pos
        rcases lt_or_ge (IMetric.hausdorffInfIDist x s : ℝ) 1 with h1 | h1
        · obtain ⟨y, hy, hxy⟩ := exists_lt_hausdorffInfIDist (ε/2) (by linarith) h1
          have step1 : (IMetric.hausdorffInfIDist x t : ℝ) ≤ idist x y + IMetric.hausdorffInfIDist y t := by
            apply le_of_forall_pos_le_add
            intro δ δ_pos
            rcases lt_or_ge (IMetric.hausdorffInfIDist y t : ℝ) 1 with h2 | h2
            · obtain ⟨z, hz, hyz⟩ := exists_lt_hausdorffInfIDist (δ/2) (by linarith) h2
              have hxz : (IMetric.hausdorffInfIDist x t : ℝ) ≤ idist x z := by
                unfold IMetric.hausdorffInfIDist
                apply Subtype.coe_le_coe.mpr
                apply iInf₂_le _ hz
              linarith [idist_triangle x y z]
            · have : (IMetric.hausdorffInfIDist y t : ℝ) = 1 :=
                le_antisymm (IMetric.hausdorffInfIDist y t).2.2 h2
              linarith [(IMetric.hausdorffInfIDist x t).2.2, (idist x y).2.1]
          have step2 : (IMetric.hausdorffInfIDist y t : ℝ) ≤ IMetric.hausdorffIDist s t :=
            hausdorffIDist_ge_hausdorffInfIDist hy
          linarith
        · have heq : (IMetric.hausdorffInfIDist x s : ℝ) = 1 :=
            le_antisymm (IMetric.hausdorffInfIDist x s).2.2 h1
          linarith [(IMetric.hausdorffInfIDist x t).2.2,
                    (IMetric.hausdorffIDist s t).2.1]

  -- Helper: push iSup ≤ b + c through ℝ addition (handles b+c possibly > 1)
  private lemma iSup_le_real_add' {α : Type*} [PseudoIMetricSpace α] {s : Set α}
      {f : α → unitInterval} {b c : ℝ} (hbc : 0 ≤ b + c)
      (hf : ∀ x ∈ s, (f x : ℝ) ≤ b + c) :
      (⨆ x ∈ s, f x : unitInterval).val ≤ b + c := by
    rcases le_or_gt 1 (b + c) with h | h
    · exact le_trans (⨆ x ∈ s, f x).2.2 h
    · have hmem : b + c ∈ Set.Icc 0 1 := ⟨hbc, le_of_lt h⟩
      set r : unitInterval := ⟨b + c, hmem⟩
      have : (⨆ x ∈ s, f x : unitInterval) ≤ r := by
        apply iSup₂_le
        intro x hx
        exact Subtype.coe_le_coe.mp (hf x hx)
      exact Subtype.coe_le_coe.mpr this

  theorem hausdorffIDist_idist_triangle {α : Type*} [PseudoIMetricSpace α] {s t u : Set α} :
      (hausdorffIDist s u : ℝ) ≤ hausdorffIDist s t + hausdorffIDist t u := by
    unfold hausdorffIDist
    apply max_le
    · apply iSup_le_real_add'
          (by linarith [(IMetric.hausdorffIDist s t).2.1, (IMetric.hausdorffIDist t u).2.1])
      intro x hx
      calc (IMetric.hausdorffInfIDist x u : ℝ)
          ≤ IMetric.hausdorffInfIDist x t + IMetric.hausdorffIDist t u :=
            hausdorffInfIDist_le_add x t u
        _ ≤ IMetric.hausdorffIDist s t + IMetric.hausdorffIDist t u := by
            apply add_le_add ?_ (le_refl _)
            apply hausdorffIDist_ge_hausdorffInfIDist hx
    · apply iSup_le_real_add'
          (by linarith [(IMetric.hausdorffIDist s t).2.1, (IMetric.hausdorffIDist t u).2.1])
      intro y hy
      have h_triangle := hausdorffInfIDist_le_add y t s
      have h_yt : (IMetric.hausdorffInfIDist y t : ℝ) ≤ IMetric.hausdorffIDist t u := by
        have h1 := @hausdorffIDist_ge_hausdorffInfIDist α _ y u t hy
        simp only [hausdorffIDist_comm (s := u) (t := t)] at h1
        exact h1
      have h_ts : (IMetric.hausdorffIDist t s : ℝ) = IMetric.hausdorffIDist s t := by
        congr 1; exact hausdorffIDist_comm
      linarith

  theorem hausdorffIDist_image_le {α β} [PseudoIMetricSpace α] [PseudoIMetricSpace β] {s t : Set α} {Φ : α → β} (h : ∀ x y, idist (Φ x) (Φ y) ≤ idist x y) :
      hausdorffIDist (Φ '' s) (Φ '' t) ≤ hausdorffIDist s t :=
    sorry

  theorem hausdorffIDist_image {α β} [PseudoIMetricSpace α] [PseudoIMetricSpace β] {s t : Set α} {Φ : α → β} (h : Isometry Φ) :
      hausdorffIDist (Φ '' s) (Φ '' t) = hausdorffIDist s t :=
    sorry

  theorem hausdorffIDist_closure {α} [PseudoIMetricSpace α] {s t : Set α} :
      hausdorffIDist (closure s) (closure t) = hausdorffIDist s t := by
    admit

  theorem hausdorffIDist_zero_iff_closure_eq_closure {α} [PseudoIMetricSpace α] {s t : Set α} :
      hausdorffIDist s t = 0 ↔ closure s = closure t := by
    sorry

  /-- Two closed sets are at zero Hausdorff edistance if and only if they coincide. -/
  theorem hausdorffIDist_eq_of_idist_eq_zero {α} {s t : Set α} [PseudoIMetricSpace α] (hs : IsClosed s) (ht : IsClosed t) :
      IMetric.hausdorffIDist s t = 0 ↔ s = t := by
    rw [hausdorffIDist_zero_iff_closure_eq_closure, IsClosed.closure_eq hs, IsClosed.closure_eq ht]
end IMetric

noncomputable instance PseudoIMetricSpace.hausdorff {α} [PseudoIMetricSpace α] : PseudoIMetricSpace (Set α) where
  idist := IMetric.hausdorffIDist
  idist_self _ := IMetric.hausdorffIDist_self
  idist_comm _ _ := IMetric.hausdorffIDist_comm
  idist_triangle _ _ _ := IMetric.hausdorffIDist_idist_triangle
  toUniformSpace := .hausdorff α
  uniformity_idist := by
    admit

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

noncomputable instance {α : Type u} [PseudoIMetricSpace α] : PseudoIMetricSpace (Closeds α) :=
  PseudoIMetricSpace.hausdorff.induced SetLike.coe -- SetLike.coe_injective'

noncomputable instance {α : Type u} [IMetricSpace α] : IMetricSpace (Closeds α) where
  eq_of_idist_eq_zero s t h := by
    apply Closeds.ext
    erwa [IMetric.hausdorffIDist_eq_of_idist_eq_zero] at h
    · exact s.isClosed
    · exact t.isClosed

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
