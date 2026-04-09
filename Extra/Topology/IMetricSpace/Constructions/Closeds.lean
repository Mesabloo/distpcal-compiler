import Extra.Topology.IMetricSpace
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.UniformSpace.Closeds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
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
    change ⨅ z ∈ t, idist x z ≤ max (⨆ y ∈ s, ⨅ z ∈ t, idist y z) (⨆ y ∈ t, ⨅ z ∈ s, idist y z)
    exact le_trans (le_iSup₂ (f := λ y _ ↦ ⨅ z ∈ t, idist y z) x hx) le_sup_left

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
    have r_mem : min 1 ((IMetric.hausdorffInfIDist x s : ℝ) + δ) ∈ unitInterval := by
      constructor
      · apply le_min zero_le_one
        grind only [= Set.mem_Icc]
      · apply min_le_left

    set r : unitInterval := ⟨min 1 ((IMetric.hausdorffInfIDist x s : ℝ) + δ), r_mem⟩

    have hr_gt : IMetric.hausdorffInfIDist x s < r := by
      change (hausdorffInfIDist x s : ℝ) < (min 1 _ : ℝ)
      apply lt_min h_lt
      linarith

    rw [lt_hausdorffInfIDist_iff] at hr_gt
    obtain ⟨y, hy, hlt_y⟩ := hr_gt
    exists y, hy
    apply lt_of_lt_of_le
    · exact hlt_y
    · apply min_le_right

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
    · have hmem : b + c ∈ unitInterval := ⟨hbc, le_of_lt h⟩
      set r : unitInterval := ⟨b + c, hmem⟩
      have : (⨆ x ∈ s, f x : unitInterval) ≤ r := by
        apply iSup₂_le
        intro x hx
        exact Subtype.coe_le_coe.mp (hf x hx)
      exact Subtype.coe_le_coe.mpr this

  theorem hausdorffIDist_idist_triangle {α : Type*} [PseudoIMetricSpace α] {s t u : Set α} :
      (hausdorffIDist s u : ℝ) ≤ hausdorffIDist s t + hausdorffIDist t u := by
    -- unfold hausdorffIDist
    apply max_le
    · apply iSup_le_real_add'
      · apply Left.add_nonneg
        · apply unitInterval.nonneg
        · apply unitInterval.nonneg
      · intros x hx
        calc (IMetric.hausdorffInfIDist x u : ℝ)
            ≤ IMetric.hausdorffInfIDist x t + IMetric.hausdorffIDist t u :=
              hausdorffInfIDist_le_add x t u
          _ ≤ IMetric.hausdorffIDist s t + IMetric.hausdorffIDist t u := by
              apply add_le_add ?_ (le_refl _)
              apply hausdorffIDist_ge_hausdorffInfIDist hx
    · apply iSup_le_real_add'
      · apply Left.add_nonneg
        · apply unitInterval.nonneg
        · apply unitInterval.nonneg
      · intros y hy
        have h_triangle := hausdorffInfIDist_le_add y t s
        have h_yt : (IMetric.hausdorffInfIDist y t : ℝ) ≤ IMetric.hausdorffIDist t u := by
          have h1 := @hausdorffIDist_ge_hausdorffInfIDist α _ y u t hy
          simp only [hausdorffIDist_comm (s := u) (t := t)] at h1
          exact h1
        have h_ts : (IMetric.hausdorffIDist t s : ℝ) = IMetric.hausdorffIDist s t := by
          congr 1
          exact hausdorffIDist_comm
        linarith

  lemma hausdorffInfIDist_image_le {α β} [PseudoIMetricSpace α] [PseudoIMetricSpace β]
      {t : Set α} {Φ : α → β} (hΦ : ∀ x y, idist (Φ x) (Φ y) ≤ idist x y) (x : α) :
      IMetric.hausdorffInfIDist (Φ x) (Φ '' t) ≤ IMetric.hausdorffInfIDist x t := by
    unfold IMetric.hausdorffInfIDist
    rw [iInf_image]
    exact iInf₂_mono (λ y _ ↦ hΦ x y)

  theorem hausdorffIDist_image_le {α β} [PseudoIMetricSpace α] [PseudoIMetricSpace β] {s t : Set α} {Φ : α → β} (h : ∀ x y, idist (Φ x) (Φ y) ≤ idist x y) :
      hausdorffIDist (Φ '' s) (Φ '' t) ≤ hausdorffIDist s t := by
    apply max_le_max <;> {
      rw [iSup_image]
      exact iSup₂_mono (λ x _ ↦ hausdorffInfIDist_image_le h x)
    }

  lemma hausdorffInfIDist_image {α β} [PseudoIMetricSpace α] [PseudoIMetricSpace β]
      {t : Set α} {Φ : α → β} (hΦ : Isometry Φ) (x : α) :
      IMetric.hausdorffInfIDist (Φ x) (Φ '' t) = IMetric.hausdorffInfIDist x t := by
    unfold IMetric.hausdorffInfIDist
    simp_rw [iInf_image, hΦ.to_idist_eq]

  theorem hausdorffIDist_image {α β} [PseudoIMetricSpace α] [PseudoIMetricSpace β] {s t : Set α} {Φ : α → β} (h : Isometry Φ) :
      hausdorffIDist (Φ '' s) (Φ '' t) = hausdorffIDist s t := by
    simp_rw [hausdorffIDist, iSup_image, hausdorffInfIDist_image h]

  -- infIDist x (closure s) = infIDist x s: closure adds limit points approached from s
  lemma hausdorffInfIDist_closure {α} [PseudoIMetricSpace α] (x : α) (s : Set α) :
      IMetric.hausdorffInfIDist x (closure s) = IMetric.hausdorffInfIDist x s := by
    unfold IMetric.hausdorffInfIDist
    apply le_antisymm (iInf_le_iInf_of_subset subset_closure)
    apply le_iInf₂
    intro y hy
    rw [IMetric.mem_closure_iff] at hy
    apply Subtype.coe_le_coe.mp
    apply le_of_forall_pos_le_add
    intro δ δ_pos
    have hε : min 1 (δ/2) > 0 := by positivity
    obtain ⟨z, hz, hyz⟩ := hy ⟨min 1 (δ/2), ⟨le_of_lt hε, min_le_left _ _⟩⟩ hε
    have h1 : (⨅ w ∈ s, idist x w : unitInterval) ≤ (idist x z : ℝ) :=
      Subtype.coe_le_coe.mpr (iInf₂_le _ hz)
    have h2 : (idist y z : ℝ) < δ :=
      lt_of_lt_of_le (lt_of_lt_of_le hyz (min_le_right _ _)) (by linarith)
    linarith [idist_triangle x y z]

  -- The sup of infIDist · t over closure s equals the sup over s:
  -- closure adds points approached from s, but the function x ↦ infIDist x t is uniformly
  -- continuous so the sup over the closure cannot exceed the sup over the set.
  lemma iSup_hausdorffInfIDist_closure {α} [PseudoIMetricSpace α] (s t : Set α) :
      ⨆ x ∈ closure s, IMetric.hausdorffInfIDist x t = ⨆ x ∈ s, IMetric.hausdorffInfIDist x t := by
    apply le_antisymm _ (iSup_le_iSup_of_subset subset_closure)
    apply iSup₂_le
    intro x hx
    rw [IMetric.mem_closure_iff] at hx
    apply Subtype.coe_le_coe.mp
    apply le_of_forall_pos_le_add
    intro ε ε_pos
    have hε : min 1 (ε/2) > 0 := by positivity
    obtain ⟨y, hy, hxy⟩ := hx ⟨min 1 (ε/2), ⟨le_of_lt hε, min_le_left _ _⟩⟩ hε
    have hxy_lt : (idist x y : ℝ) < ε :=
      lt_of_lt_of_le (lt_of_lt_of_le (Subtype.coe_lt_coe.mpr hxy) (min_le_right _ _)) (by linarith)
    have hyt : (IMetric.hausdorffInfIDist y t : ℝ) ≤
        (⨆ z ∈ s, IMetric.hausdorffInfIDist z t : unitInterval).val :=
      Subtype.coe_le_coe.mpr (le_iSup₂ (f := λ z _ ↦ IMetric.hausdorffInfIDist z t) y hy)
    -- infIDist x t ≤ idist x y + infIDist y t (reverse triangle inequality)
    have htri : (IMetric.hausdorffInfIDist x t : ℝ) ≤ idist x y + IMetric.hausdorffInfIDist y t := by
      apply le_of_forall_pos_le_add
      intro δ δ_pos
      rcases lt_or_ge (IMetric.hausdorffInfIDist y t : ℝ) 1 with h | h
      · have hr_mem : min 1 (IMetric.hausdorffInfIDist y t + δ/2) ∈ unitInterval :=
          ⟨le_min zero_le_one (by linarith [(IMetric.hausdorffInfIDist y t).2.1]), min_le_left _ _⟩
        set r := (⟨min 1 (IMetric.hausdorffInfIDist y t + δ/2), hr_mem⟩ : unitInterval)
        have hrgt : IMetric.hausdorffInfIDist y t < r := by
          rw [← Subtype.coe_lt_coe]
          exact lt_min h (by linarith)
        rw [lt_hausdorffInfIDist_iff] at hrgt
        obtain ⟨z, hz, hyz⟩ := hrgt
        have hxz : (IMetric.hausdorffInfIDist x t : ℝ) ≤ idist x z := by
          exact Subtype.coe_le_coe.mpr (iInf₂_le _ hz)
        linarith [idist_triangle x y z, lt_of_lt_of_le (Subtype.coe_lt_coe.mpr hyz) (min_le_right _ _)]
      · linarith [(IMetric.hausdorffInfIDist x t).2.2, (idist x y).2.1,
                  le_antisymm (IMetric.hausdorffInfIDist y t).2.2 h]
    linarith

  theorem hausdorffIDist_closure {α} [PseudoIMetricSpace α] {s t : Set α} :
      hausdorffIDist (closure s) (closure t) = hausdorffIDist s t := by
    simp only [hausdorffIDist, hausdorffInfIDist_closure, iSup_hausdorffInfIDist_closure]

  -- infIDist x t = ⊥ iff x is in the closure of t
  lemma mem_closure_iff_hausdorffInfIDist_eq_bot {α} [PseudoIMetricSpace α] {x : α} {t : Set α} :
      IMetric.hausdorffInfIDist x t = ⊥ ↔ x ∈ closure t := by
    constructor
    · intro h
      rw [IMetric.mem_closure_iff]
      intro r r_pos
      rw [← lt_hausdorffInfIDist_iff, h]
      exact r_pos
    · intro hx
      rw [IMetric.mem_closure_iff] at hx
      apply eq_bot_iff.mpr
      by_contra h
      push_neg at h
      obtain ⟨y, hy, hxy⟩ := hx (IMetric.hausdorffInfIDist x t) h
      exact absurd (lt_of_le_of_lt (iInf₂_le (f := λ y _ ↦ idist x y) y hy) hxy) (lt_irrefl _)

  theorem hausdorffIDist_zero_iff_closure_eq_closure {α} [PseudoIMetricSpace α] {s t : Set α} :
      hausdorffIDist s t = 0 ↔ closure s = closure t := by
    constructor
    · intro h
      rw [← hausdorffIDist_closure] at h
      change max _ _ = ⊥ at h
      rw [max_eq_bot] at h
      obtain ⟨h1, h2⟩ := h
      rw [iSup₂_eq_bot] at h1 h2
      apply Set.Subset.antisymm
      · intro x hx
        have := (mem_closure_iff_hausdorffInfIDist_eq_bot.mp (h1 x hx))
        rwa [closure_closure] at this
      · intro y hy
        have := (mem_closure_iff_hausdorffInfIDist_eq_bot.mp (h2 y hy))
        rwa [closure_closure] at this
    · intro h
      rw [← hausdorffIDist_closure, h, hausdorffIDist_self]

  theorem hausdorffIDist_eq_of_idist_eq_zero {α} {s t : Set α} [PseudoIMetricSpace α] (hs : IsClosed s) (ht : IsClosed t) :
      IMetric.hausdorffIDist s t = 0 ↔ s = t := by
    rw [hausdorffIDist_zero_iff_closure_eq_closure, IsClosed.closure_eq hs, IsClosed.closure_eq ht]
end IMetric

-- Helper: for (s,t) in hausdorffEntourage, hausdorffIDist s t < ε (requires ε ≤ 1)
private lemma mem_hausdorffEntourage_of_hausdorffIDist_lt {α : Type*} [PseudoIMetricSpace α]
    {s t : Set α} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : (IMetric.hausdorffIDist s t : ℝ) < ε) :
    (s, t) ∈ hausdorffEntourage {p : α × α | (idist p.1 p.2 : ℝ) < ε} := by
  simp only [hausdorffEntourage, SetRel.preimage, SetRel.image, Set.subset_def, Set.mem_setOf_eq]
  set r : unitInterval := ⟨ε, le_of_lt hε, hε1⟩
  have hr : IMetric.hausdorffIDist s t < r := h
  change max (⨆ x ∈ s, IMetric.hausdorffInfIDist x t) (⨆ y ∈ t, IMetric.hausdorffInfIDist y s) < r at hr
  rw [max_lt_iff] at hr
  obtain ⟨hr1, hr2⟩ := hr

  constructor
  · intros x hx
    have := lt_of_le_of_lt (le_iSup₂ (f := λ x _ ↦ IMetric.hausdorffInfIDist x t) x hx) hr1
    rw [IMetric.lt_hausdorffInfIDist_iff] at this
    obtain ⟨y, hy, hxy⟩ := this
    exists y, hy
  · intros y hy
    have := lt_of_le_of_lt (le_iSup₂ (f := λ y _ ↦ IMetric.hausdorffInfIDist y s) y hy) hr2
    rw [IMetric.lt_hausdorffInfIDist_iff] at this
    obtain ⟨x, hx, hyx⟩ := this
    exists x, hx
    rw [idist_comm];
    exact hyx

-- Helper: for (s,t) in hausdorffEntourage{idist < ε}, hausdorffIDist s t ≤ ε (requires ε ≤ 1)
private lemma hausdorffIDist_le_of_mem_hausdorffEntourage {α : Type*} [PseudoIMetricSpace α]
    {s t : Set α} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : (s, t) ∈ hausdorffEntourage {p : α × α | (idist p.1 p.2 : ℝ) < ε}) :
    (IMetric.hausdorffIDist s t : ℝ) ≤ ε := by
  simp only [hausdorffEntourage, SetRel.preimage, SetRel.image, Set.subset_def, Set.mem_setOf_eq] at h
  obtain ⟨h1, h2⟩ := h
  change (max (⨆ x ∈ s, IMetric.hausdorffInfIDist x t : unitInterval)
            (⨆ y ∈ t, IMetric.hausdorffInfIDist y s : unitInterval) : ℝ) ≤ ε
  push_cast [max_le_iff]
  constructor
  · apply le_of_forall_pos_le_add
    intro δ δ_pos
    have : (⨆ x ∈ s, IMetric.hausdorffInfIDist x t : unitInterval) ≤ ⟨ε, le_of_lt hε, hε1⟩ :=
      iSup₂_le λ x hx ↦ by
        obtain ⟨y, hy, hxy⟩ := h1 x hx
        exact le_trans (iInf₂_le (f := λ y _ ↦ idist x y) y hy) (le_of_lt hxy)
    linarith [Subtype.coe_le_coe.mpr this]
  · apply le_of_forall_pos_le_add
    intro δ δ_pos
    have : (⨆ y ∈ t, IMetric.hausdorffInfIDist y s : unitInterval) ≤ ⟨ε, le_of_lt hε, hε1⟩ :=
      iSup₂_le λ y hy ↦ by
        obtain ⟨x, hx, hxy⟩ := h2 y hy
        exact le_trans (iInf₂_le (f := λ x _ ↦ idist y x) x hx)
                       (by rw [idist_comm]; exact le_of_lt hxy)
    linarith [Subtype.coe_le_coe.mpr this]

noncomputable instance PseudoIMetricSpace.hausdorff {α} [PseudoIMetricSpace α] : PseudoIMetricSpace (Set α) where
  idist := IMetric.hausdorffIDist
  idist_self _ := IMetric.hausdorffIDist_self
  idist_comm _ _ := IMetric.hausdorffIDist_comm
  idist_triangle _ _ _ := IMetric.hausdorffIDist_idist_triangle
  toUniformSpace := .hausdorff α
  uniformity_idist := by
    -- The Hausdorff uniform space uniformity = ⨅ ε > 0, 𝓟{hausdorffIDist < ε}
    -- via equivalence of filter bases with the entourage-based description.
    have lhs_basis : ((uniformity α).lift' hausdorffEntourage).HasBasis
        (λ ε : ℝ ↦ 0 < ε) (λ ε ↦ hausdorffEntourage {p : α × α | (idist p.1 p.2 : ℝ) < ε}) :=
      IMetric.uniformity_basis_idist.lift' monotone_hausdorffEntourage

    have rhs_basis : (⨅ ε > 0, Filter.principal {p : Set α × Set α |
        (IMetric.hausdorffIDist p.1 p.2 : ℝ) < ε}).HasBasis
        (λ ε : ℝ ↦ 0 < ε) (λ ε ↦ {p : Set α × Set α | (IMetric.hausdorffIDist p.1 p.2 : ℝ) < ε}) :=
      Filter.hasBasis_biInf_principal
        (λ a (ha : a ∈ Set.Ioi 0) b (hb : b ∈ Set.Ioi 0) ↦
          ⟨min a b, Set.mem_Ioi.mpr (lt_min ha hb),
            λ p hp ↦ Set.mem_setOf.mpr (lt_of_lt_of_le (Set.mem_setOf.mp hp) (min_le_left _ _)),
            λ p hp ↦ Set.mem_setOf.mpr (lt_of_lt_of_le (Set.mem_setOf.mp hp) (min_le_right _ _))⟩)
        ⟨1, Set.mem_Ioi.mpr one_pos⟩
    change (uniformity α).lift' hausdorffEntourage = _
    apply le_antisymm
    · -- For each ε > 0, show {hausdorffIDist < ε} ∈ LHS filter
      rw [rhs_basis.ge_iff]
      intro ε hε
      apply Filter.mem_of_superset (lhs_basis.mem_of_mem (show 0 < min 1 (ε / 2) by positivity))
      intro ⟨s, t⟩ hst
      exact Set.mem_setOf.mpr <| lt_of_le_of_lt
        (hausdorffIDist_le_of_mem_hausdorffEntourage (by positivity) (min_le_left _ _) hst)
        (lt_of_le_of_lt (min_le_right _ _) (by linarith))
    · -- For each ε > 0, show hausdorffEntourage{idist < ε} ∈ RHS filter
      rw [lhs_basis.ge_iff]
      intro ε hε
      apply Filter.mem_of_superset (rhs_basis.mem_of_mem (show min 1 ε ∈ Set.Ioi 0 from
        Set.mem_Ioi.mpr (by positivity)))
      intro ⟨s, t⟩ hst
      apply monotone_hausdorffEntourage (Set.setOf_subset_setOf.mpr
        fun p (hp : (idist p.1 p.2 : ℝ) < min 1 ε) => lt_of_lt_of_le hp (min_le_right _ _))
      exact mem_hausdorffEntourage_of_hausdorffIDist_lt (by positivity) (min_le_left _ _)
        (Set.mem_setOf.mp hst)

-- If for every x ∈ s there exists y ∈ t with idist x y ≤ r, and vice versa,
-- then hausdorffIDist s t ≤ r.
open unitInterval in
theorem IMetric.hausdorffIDist_le_iff {α} [PseudoIMetricSpace α] {s t : Set α} {r : I}
  (h₁ : ∀ x ∈ s, ∃ y ∈ t, idist x y ≤ r) (h₂ : ∀ y ∈ t, ∃ x ∈ s, idist x y ≤ r) :
    IMetric.hausdorffIDist s t ≤ r := by
  unfold IMetric.hausdorffIDist IMetric.hausdorffInfIDist
  apply max_le
  · apply iSup₂_le; intro x hx
    obtain ⟨y, hy, hxy⟩ := h₁ x hx
    exact iInf₂_le_of_le y hy hxy
  · apply iSup₂_le; intro y hy
    obtain ⟨x, hx, hxy⟩ := h₂ y hy
    exact iInf₂_le_of_le x hx (idist_comm x y ▸ hxy)

theorem IMetric.hausdorffIDist_image_le_of_le_sup {α} [PseudoIMetricSpace α] {s : Set α} {f : α → α} :
    IMetric.hausdorffIDist s (f '' s) ≤ ⨆ x ∈ s, idist x (f x) := by
  apply IMetric.hausdorffIDist_le_iff
  · intros x x_in
    exists f x, Set.mem_image_of_mem _ x_in
    exact le_iSup₂ (f := λ x _ ↦ idist x (f x)) x x_in
  · rintro y ⟨x, x_in, rfl⟩
    exists x, x_in
    exact le_iSup₂ (f := λ x _ ↦ idist x (f x)) x x_in

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

-- Helper for completeness proof: from hausdorffIDist s t < ε, get a nearby point in t
lemma IMetric.exists_idist_lt_of_hausdorffIDist_lt {α : Type*} [PseudoIMetricSpace α]
    {s t : Set α} {x : α} (hx : x ∈ s) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : (IMetric.hausdorffIDist s t : ℝ) < ε) :
    ∃ y ∈ t, (idist x y : ℝ) < ε := by
  have : IMetric.hausdorffInfIDist x t < ⟨ε, le_of_lt hε, hε1⟩ := by
    apply lt_of_le_of_lt
    apply IMetric.hausdorffIDist_ge_hausdorffInfIDist hx
    exact h
  rw [IMetric.lt_hausdorffInfIDist_iff] at this
  obtain ⟨y, hy, hxy⟩ := this
  exists y, hy

-- This can't be equal to `TopologicalSpace.Closeds.instCompleteSpace` (from `Mathlib.Topology.MetricSpace.Closeds`)
-- otherwise there is an instance mismatch further down, when using the completeness of `Closeds α`.
-- In fact, this module cannot even be imported without clashing with this file's definitions.
instance (priority := high) Closeds.instCompleteSpace {α : Type u} [IMetricSpace α] [CompleteSpace α] : CompleteSpace (Closeds α) := by
  let B : ℕ → ℝ := λ n ↦ (2 : ℝ)⁻¹ ^ n
  have B_pos : ∀ n, 0 < B n := λ n ↦ by positivity
  have B_le_one : ∀ n, B n ≤ 1 := λ n ↦ by
    simp only [B]
    exact pow_le_one₀ (by positivity) (by norm_num)
  have B_add : ∀ n k : ℕ, B (n + k) = B n / 2 ^ k := λ n k ↦ by
    simp [B, pow_add, inv_pow]; ring
  apply Metric.complete_of_convergent_controlled_sequences B B_pos
  intro s hs
  let t0 : Set α := ⋂ n, closure (⋃ m ≥ n, (s m : Set α))
  let t : Closeds α := ⟨t0, isClosed_iInter λ _ ↦ isClosed_closure⟩
  -- Inductive stepping: from z ∈ s (n+k), find z' ∈ s (n+k+1) with dist z z' ≤ B(n+k).
  -- Using hs with N = n+k: dist (s(n+k)) (s(n+k+1)) < B(n+k).
  have step : ∀ n k (z : (s (n + k) : Set α)),
      ∃ z' : (s (n + k + 1) : Set α), dist (z : α) z' ≤ B (n + k) := by
    intro n k z
    have hdist : (IMetric.hausdorffIDist (s (n + k) : Set α) (s (n + k + 1)) : ℝ) < B (n + k) :=
      hs (n + k) (n + k) (n + k + 1) (le_refl _) (Nat.le_succ _)
    obtain ⟨z', hz', hdz⟩ := IMetric.exists_idist_lt_of_hausdorffIDist_lt
        z.2 (B_pos (n + k)) (B_le_one (n + k)) hdist
    exists ⟨z', hz'⟩
    exact le_of_lt hdz
  -- I1: from x ∈ s n, find y ∈ t0 with dist x y ≤ 2 * B n.
  -- Build chain z with z 0 = x, z k ∈ s(n+k), dist(z k)(z(k+1)) ≤ B(n+k) = (2*B n)/2/2^k.
  have I1 : ∀ n, ∀ x ∈ (s n : Set α), ∃ y ∈ t0, dist x y ≤ 2 * B n := by
    intro n x hx
    -- Build chain inductively: z k ∈ s(n+k), dist(z k)(z(k+1)) ≤ (2*Bn)/2/2^k = B(n+k)
    obtain ⟨z, hz₀, hz⟩ : ∃ z : ∀ k, (s (n + k) : Set α),
        (z 0 : α) = x ∧ ∀ k, dist (z k : α) (z (k + 1) : α) ≤ (2 * B n) / 2 / 2 ^ k := by
      have chain_step : ∀ l (zl : (s (n + l) : Set α)),
          ∃ zl' : (s (n + l + 1) : Set α), dist (zl : α) zl' ≤ (2 * B n) / 2 / 2 ^ l := by
        intro l zl
        exists (step n l zl).choose
        have hspec := (step n l zl).choose_spec
        rw [show (2 * B n) / 2 / 2 ^ l = B (n + l) from by rw [B_add]; ring]
        exact hspec
      exact ⟨λ k ↦ Nat.recOn k ⟨x, hx⟩ (λ l zl ↦ (chain_step l zl).choose),
             by simp, λ k ↦ (chain_step k _).choose_spec⟩
    -- Chain is Cauchy
    obtain ⟨y, hy_lim⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hz)
    exists y
    constructor
    · -- y ∈ t0 = ⋂ n, closure(⋃ m≥n, s m)
      apply Set.mem_iInter.mpr
      intro k
      apply mem_closure_of_tendsto hy_lim
      rw [Filter.eventually_atTop]
      exact ⟨k, λ m hm ↦ Set.mem_iUnion₂.mpr ⟨n + m, by linarith, (z m).2⟩⟩
    · -- dist x y ≤ 2 * B n via dist_le_of_le_geometric_two_of_tendsto₀
      rw [← hz₀]
      exact dist_le_of_le_geometric_two_of_tendsto₀ hz hy_lim
  -- I2: from y ∈ t0, find x ∈ s n with dist y x ≤ 2 * B n
  have I2 : ∀ n, ∀ y ∈ t0, ∃ x ∈ (s n : Set α), dist y x ≤ 2 * B n := by
    intro n y hy
    obtain ⟨z, hz, dyz⟩ := Metric.mem_closure_iff.mp (Set.mem_iInter.mp hy n) (B n) (B_pos n)
    obtain ⟨m, hm, hzm⟩ := Set.mem_iUnion₂.mp hz
    -- hausdorffIDist (s m) (s n) < B n (from hs with N = n)
    have hdist : (IMetric.hausdorffIDist (s m : Set α) (s n) : ℝ) < B n := by
      have h : dist (s m) (s n) < B n := by
        rw [dist_comm]; exact hs n n m (le_refl n) hm
      exact h
    obtain ⟨w, hw, dzw⟩ := IMetric.exists_idist_lt_of_hausdorffIDist_lt hzm (B_pos n) (B_le_one n) hdist
    exists w, hw
    apply le_of_lt
    calc dist y w
        ≤ dist y z + dist z w := dist_triangle y z w
      _ < B n + B n           := by linarith [show dist z w = (idist z w : ℝ) from rfl]
      _ = 2 * B n             := by ring
  -- Bound dist (s n) t ≤ 2 * B n via hausdorffIDist_le_iff
  -- Note: 2 * B n may exceed 1 for small n (e.g. n = 0), but dist ≤ 1 handles that trivially.
  have main : ∀ n, dist (s n) t ≤ 2 * B n := by
    intro n
    show (IMetric.hausdorffIDist (s n : Set α) (t : Set α) : ℝ) ≤ 2 * B n
    by_cases h1 : 1 ≤ 2 * B n
    · -- 2 * B n ≥ 1, trivial since hausdorffIDist ≤ 1
      exact le_trans (IMetric.hausdorffIDist (s n : Set α) (t : Set α)).2.2 h1
    · -- 2 * B n < 1, use hausdorffIDist_le_iff with r = ⟨2 * B n, ...⟩
      push_neg at h1
      have hge0 : (0 : ℝ) ≤ 2 * B n := by positivity
      set r : unitInterval := ⟨2 * B n, hge0, le_of_lt h1⟩
      have hle : IMetric.hausdorffIDist (s n : Set α) (t : Set α) ≤ r := by
        apply IMetric.hausdorffIDist_le_iff
        · intro x hx
          obtain ⟨y, hy, hd⟩ := I1 n x hx
          exists y, hy
        · intro y hy
          obtain ⟨x, hx, hd⟩ := I2 n y hy
          exists x, hx
          rw [idist_comm]; exact_mod_cast hd
      exact_mod_cast hle
  -- Conclude: s n → t in Closeds α
  exists t
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hlim : Filter.Tendsto (λ n ↦ 2 * B n) Filter.atTop (nhds 0) := by
    simp only [B]
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2:ℝ)⁻¹) (by positivity) (by norm_num)).const_mul 2
    simpa using h
  have hev := (tendsto_order.mp hlim).2 ε hε
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  exists N
  intro n hn
  exact lt_of_le_of_lt (main n) (hN n hn)

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
