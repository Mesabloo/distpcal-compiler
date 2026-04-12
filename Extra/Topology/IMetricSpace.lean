import CustomPrelude
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Order.Hom.CompleteLattice

namespace unitInterval
  @[simp] theorem top_eq : (⊤ : I) = 1 := rfl
  @[simp] theorem bot_eq : (⊥ : I) = 0 := rfl

  @[simp] theorem zero_eq : (0 : I) = ⟨0, by simp⟩ := rfl

  theorem coe_zero_eq : ↑(0 : I) = (0 : ℝ) := rfl

  theorem le_iff_le_val (x y : I) : x ≤ y ↔ x.val ≤ y.val := by rfl

  @[simp]
  theorem mul_bot {x : I} : x * ⊥ = ⊥ := by
    grind only [←= bot_unique, mul_le_right]

  @[simp]
  theorem bot_mul {x : I} : ⊥ * x = ⊥ := by
    rw [mul_comm, mul_bot]

  @[simp]
  theorem mul_top {x : I} : x * ⊤ = x := by
    rw [top_eq, mul_one]

  @[simp]
  theorem top_mul {x : I} : ⊤ * x = x := by
    rw [mul_comm, mul_top]

  noncomputable def half : I where
    val := 1 / 2
    property := by bound

  @[bound]
  theorem half_pos : half > 0 := by
    simp [half, zero_eq, Subtype.mk_lt_mk]

  theorem half_mul_le_self {ε : I} : half * ε ≤ ε := by
    grind only [mul_le_right]

  theorem half_mul_lt_self_of_pos {ε : I} (h : ε > 0) : half * ε < ε := by
    change (1 / 2 * (ε : ℝ)) < (ε : ℝ)
    grind only [= Set.mem_Icc, coe_zero_eq, coe_ne_zero, unitInterval.pos_iff_ne_zero]

  @[simp]
  theorem half_mul_half_eq : (half * half : ℝ) = 1 / 4 := by
    grind [= half.eq_def]

  theorem half_mul_toReal_eq_div_two (x : I) : ↑(half * x) = (↑x / 2 : ℝ) := by
    change (1 / 2 * x : ℝ) = _
    grind only

  theorem toNNReal_cast_eq_toNNReal {ε : I} : (ε : ℝ).toNNReal = toNNReal ε := by
    rw [Real.toNNReal_of_nonneg]
    rfl

  theorem coe_iSup_le {ι} {f : ι → I} {a : ℝ} (ha : 0 ≤ a) (h : ∀ (i : ι), (f i).val ≤ a) :
      (iSup f).val ≤ a := by
    cases isEmpty_or_nonempty ι with
    | inl _ =>
      simpa only [iSup_of_empty] using ha
    | inr _ =>
      rw [iSup, Set.Icc.coe_sSup (by norm_num) (Set.range_nonempty f), ← Set.range_comp]
      exact ciSup_le h

  theorem coe_iSup₂_le {ι} {ι' : ι → _} {f : (x : ι) → ι' x → I} {a : ℝ} (ha : 0 ≤ a) (h : ∀ (i : ι) (j : ι' i), (f i j).val ≤ a) :
      (⨆ x, ⨆ y, f x y).val ≤ a := by
    apply coe_iSup_le ha λ i ↦ ?_
    apply coe_iSup_le ha λ j ↦ ?_
    exact h i j

  theorem coe_le_iSup {ι} {f : ι → I} {i : ι} :
      (f i).val ≤ (iSup f).val := by
    rw [Subtype.coe_le_coe]
    apply le_iSup

  theorem coe_le_iSup₂ {ι} {ι' : ι → _} {f : (x : ι) → ι' x → I} {i : ι} {j : ι' i} :
      (f i j).val ≤ (⨆ x, ⨆ y, f x y).val := by
    rw [Subtype.coe_le_coe]
    apply le_iSup₂

  -- theorem iSup_eq_zero {ι} {f : ι → I} :
  --     ⨆ i, f i = ⊥ ↔ ∀ (i : ι), f i = ⊥ := by
  --   admit

  private lemma coe_iSup_eq {ι} [Nonempty ι] (f : ι → I) :
      (⨆ i, f i).val = ⨆ i, (f i).val := by
    rw [iSup, Set.Icc.coe_sSup (by norm_num) (Set.range_nonempty f), ← Set.range_comp]
    rfl

  private lemma real_mul_iSup {ι} [Nonempty ι] (f : ι → I) (a : I) :
      a.val * ⨆ x, (f x).val = ⨆ x, a.val * (f x).val := by
    have hbdd : BddAbove (Set.range λ x ↦ (f x).val) :=
      ⟨1, λ _ ⟨i, hi⟩ ↦ hi ▸ (f i).2.2⟩
    rw [← Monotone.map_ciSup_of_continuousAt
          (f := λ y ↦ a.val * y)
          (continuousAt_const.mul continuousAt_id)
          (λ x y h ↦ mul_le_mul_of_nonneg_left h a.2.1)
          hbdd]

  theorem mul_iSup {ι} {f : ι → I} {a : I} :
      a * ⨆ x, f x = ⨆ x, a * f x := by
    apply le_antisymm
    · rw [Subtype.mk_le_mk]
      cases isEmpty_or_nonempty ι with
      | inl h =>
        haveI := h
        simp
      | inr _ =>
        change a.val * (⨆ x, f x).val ≤ (⨆ x, a * f x).val
        rw [coe_iSup_eq f, real_mul_iSup f a, coe_iSup_eq (a * f ·)]
        exact le_refl _
    · apply iSup_le
      intro x
      exact mul_le_mul_of_nonneg_left (le_iSup f x) a.2.1

  theorem iSup_mul {ι} {f : ι → I} {a : I} :
      (⨆ x, f x) * a = ⨆ x, f x * a := by
    simp [mul_comm, mul_iSup]

  theorem div_coe_eq_of_one_le {a : I} {b : ℝ} (hb : 1 ≤ b) :
      (a : ℝ) / b = Subtype.val {
        val := a.val / b
        property := ⟨div_nonneg (nonneg a) (le_trans zero_le_one hb),
                     div_le_one_of_le₀ (by grind only [=Set.mem_Icc]) (le_trans zero_le_one hb)⟩
        : I
      } :=
    rfl
end unitInterval

open scoped unitInterval

class IDist (α : Type _) where
  /-- The distance between two points, in the interval `[0, 1]`. -/
  idist : α → α → I

attribute [reducible] IDist.idist

export IDist (idist)

instance instDistOfIDist {α} [IDist α] : Dist α where
  dist x y := idist x y

/-- Creating a uniform space from an extended distance. -/
@[instance_reducible]
def uniformSpaceOfIDist {α} (idist : α → α → I) (idist_self : ∀ x : α, idist x x = 0)
    (idist_comm : ∀ x y : α, idist x y = idist y x)
    (idist_triangle : ∀ x y z : α, (idist x z : ℝ) ≤ idist x y + idist y z) : UniformSpace α :=
  .ofFun (λ x y ↦ idist x y : α → α → ℝ)
    (λ x ↦ by beta_reduce; exact idist_self x ▸ unitInterval.coe_zero_eq)
    (λ x y ↦ by beta_reduce; exact idist_comm x y ▸ rfl)
    idist_triangle
    UniformSpace.ofDist_aux

open scoped Uniformity Filter in
class PseudoIMetricSpace (α : Type _) extends IDist α where
  idist_self : ∀ x, idist x x = 0
  idist_comm : ∀ x y, idist x y = idist y x
  idist_triangle : ∀ x y z : α, (idist x z : ℝ) ≤ idist x y + idist y z
  toUniformSpace : UniformSpace α := uniformSpaceOfIDist idist idist_self idist_comm idist_triangle
  uniformity_idist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | (idist p.1 p.2 : ℝ) < ε } := by intros; rfl

export PseudoIMetricSpace (idist_self idist_comm idist_triangle)

attribute [instance_reducible, instance] PseudoIMetricSpace.toUniformSpace

class IMetricSpace (α : Type _) extends PseudoIMetricSpace α where
  eq_of_idist_eq_zero : ∀ x y, idist x y = 0 → x = y

export IMetricSpace (eq_of_idist_eq_zero)

theorem IMetricSpace.idist_eq_zero_iff {α} {x y : α} [IMetricSpace α] :
    idist x y = 0 ↔ x = y := by
  iff_intro h h
  · exact eq_of_idist_eq_zero _ _ h
  · subst h
    rw [idist_self]

@[instance_reducible]
def PseudoIMetricSpace.of_metric_space_of_dist_le_one {α} [inst : PseudoMetricSpace α]
  (h : ∀ x y : α, dist x y ≤ 1 := by intros; bound) :
    PseudoIMetricSpace α where
  idist x y := ⟨dist x y, dist_nonneg, h x y⟩
  idist_self x := by rw! [dist_self]; rfl
  idist_comm x y := by rw! [dist_comm]; rfl
  idist_triangle x y z := dist_triangle x y z
  toUniformSpace := inst.toUniformSpace
  uniformity_idist := by rw [inst.uniformity_dist]

@[instance_reducible]
def IMetricSpace.of_metric_space_of_dist_le_one {α} [inst : MetricSpace α]
  (h : ∀ x y : α, dist x y ≤ 1 := by intros; bound) :
    IMetricSpace α where
  __ := PseudoIMetricSpace.of_metric_space_of_dist_le_one h
  eq_of_idist_eq_zero {x y} eq := by
    replace eq : dist x y = 0 := by injection eq
    exact eq_of_dist_eq_zero eq

theorem edist_nonneg {α} [PseudoEMetricSpace α] {x y : α} : 0 ≤ edist x y := by
  exact zero_le (edist x y)

@[instance_reducible]
def PseudoIMetricSpace.of_emetric_space_of_dist_le_one {α} [inst : PseudoEMetricSpace α]
  (h : ∀ x y : α, edist x y ≤ 1 := by intros; bound) :
    PseudoIMetricSpace α where
  idist x y := ⟨(edist x y).toReal,
                ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (h _ _)) edist_nonneg,
                ENNReal.toReal_mono ENNReal.one_ne_top (h x y)⟩
  idist_self x := by rw! [edist_self]; rfl
  idist_comm x y := by rw! [edist_comm]; rfl
  idist_triangle x y z := by
    change (edist _ _).toReal ≤ (edist _ _).toReal + (edist _ _).toReal

    have : edist x y ≠ ⊤ := by
      apply ne_top_of_le_ne_top (b := 1)
      · exact ENNReal.one_ne_top
      · apply h
    have : edist y z ≠ ⊤ := by
      apply ne_top_of_le_ne_top (b := 1)
      · exact ENNReal.one_ne_top
      · apply h

    rw [← ENNReal.toReal_add]
    · apply ENNReal.toReal_mono
      · apply ENNReal.Finiteness.add_ne_top
        · assumption
        · assumption
      · apply edist_triangle x y z
    · assumption
    · assumption
  toUniformSpace := inst.toUniformSpace
  uniformity_idist := by
    rw [inst.uniformity_edist]
    apply le_antisymm
    · apply le_iInf₂; intro ε hε
      apply iInf₂_le_of_le (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
      apply Filter.principal_mono.mpr
      intro ⟨f, g⟩ hfg
      simp only [Set.mem_setOf_eq] at *
      rw [show ε = (ENNReal.ofReal ε).toReal from (ENNReal.toReal_ofReal hε.le).symm, ENNReal.toReal_lt_toReal]
      · exact hfg
      · apply ne_top_of_le_ne_top (b := 1)
        · exact ENNReal.one_ne_top
        · apply h
      · apply ENNReal.ofReal_ne_top
    · apply le_iInf₂; intro ε hε
      by_cases hε_top : ε = ⊤
      · apply iInf₂_le_of_le 1 one_pos
        apply Filter.principal_mono.mpr
        intro ⟨f, g⟩ _hfg
        simp only [Set.mem_setOf_eq]
        subst hε_top
        apply LE.le.trans_lt (b := 1)
        · apply h
        · exact ENNReal.one_lt_top
      · have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
        apply iInf₂_le_of_le ε.toReal hε_real_pos
        apply Filter.principal_mono.mpr
        intro ⟨f, g⟩ hfg
        simp only [Set.mem_setOf_eq] at *
        rwa [← ENNReal.toReal_lt_toReal _ hε_top]
        apply ne_top_of_le_ne_top (b := 1)
        · exact ENNReal.one_ne_top
        · apply h

@[instance_reducible]
def IMetricSpace.of_emetric_space_of_dist_le_one {α} [inst : EMetricSpace α]
  (h : ∀ x y : α, edist x y ≤ 1 := by intros; bound) :
    IMetricSpace α where
  __ := PseudoIMetricSpace.of_emetric_space_of_dist_le_one h
  eq_of_idist_eq_zero {x y} eq := by
    have h' : (edist x y).toReal = 0 := congr_arg Subtype.val eq
    have hedge : edist x y = 0 := by
      rw [ENNReal.toReal_eq_zero_iff] at h'
      apply Or.resolve_right h'
      apply ne_top_of_le_ne_top (b := 1)
      · exact ENNReal.one_ne_top
      · apply h
    exact edist_eq_zero.mp hedge

instance (priority := low) {α} [inst : PseudoIMetricSpace α] : PseudoMetricSpace α where
  dist x y := idist x y
  dist_self x := by rw [idist_self]; rfl
  dist_comm x y := by rw [idist_comm]
  dist_triangle x y z := idist_triangle x y z
  toUniformSpace := inst.toUniformSpace
  uniformity_dist := by rw [inst.uniformity_idist]

instance (priority := low) {α} [IMetricSpace α] : MetricSpace α where
  eq_of_dist_eq_zero {x y} h := by
    apply eq_of_idist_eq_zero
    change (idist x y : ℝ) = 0 at h
    grind only [= Set.Icc.mk_zero]

namespace IMetric
  theorem toUniformSpace_eq.{u} {α : Type u} [inst : PseudoIMetricSpace α]  :
      ‹PseudoIMetricSpace α›.toUniformSpace = uniformSpaceOfIDist idist idist_self idist_comm idist_triangle :=
    UniformSpace.ext PseudoIMetricSpace.uniformity_idist

  open Uniformity in
  theorem uniformity_basis_idist.{u} {α : Type u} [inst : PseudoIMetricSpace α] :
      (𝓤 α).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : α × α | idist p.1 p.2 < ε } := by
    rw [toUniformSpace_eq]
    exact UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _

  open Uniformity in
  theorem mem_uniformity_idist.{u} {α : Type u} [PseudoIMetricSpace α] {s : Set (α × α)} :
      s ∈ uniformity α ↔ ∃ ε > 0, ∀ ⦃a b : α⦄, (idist a b : ℝ) < ε → (a, b) ∈ s :=
    IMetric.uniformity_basis_idist.mem_uniformity_iff

  open Uniformity in
  /-- A constant size neighborhood of the diagonal is an entourage. -/
  theorem idist_mem_uniformity {α} [PseudoIMetricSpace α] {ε : ℝ} (ε0 : 0 < ε) : { p : α × α | dist p.1 p.2 < ε } ∈ 𝓤 α :=
    mem_uniformity_idist.2 ⟨ε, ε0, fun _ _ ↦ id⟩

  def ball {α} [IDist α] (x : α) (ε : ℝ) : Set α :=
    { y | idist y x < ε }

  open Topology in
  theorem nhds_basis_ball {α} [PseudoIMetricSpace α] {x : α} : (𝓝 x).HasBasis (0 < ·) (ball x) :=
    nhds_basis_uniformity uniformity_basis_idist

  open Topology in
  theorem mem_nhds_iff {α} [PseudoIMetricSpace α] {s : Set α} {x : α} : s ∈ 𝓝 x ↔ ∃ ε > 0, ball x ε ⊆ s :=
    nhds_basis_ball.mem_iff

  theorem isOpen_iff {α} [IMetricSpace α] {s : Set α} : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s := by
    simp only [isOpen_iff_mem_nhds, mem_nhds_iff]

  @[simp]
  theorem mem_ball {α} [PseudoIMetricSpace α] {x y : α} {ε : ℝ} : y ∈ ball x ε ↔ dist y x < ε :=
    Iff.rfl

  theorem mem_ball' {α} [PseudoIMetricSpace α] {x y : α} {ε : ℝ} : y ∈ ball x ε ↔ idist x y < ε := by
    rw [idist_comm, mem_ball]
    rfl

  theorem mem_closure_iff {α} [PseudoIMetricSpace α] {s : Set α} {a : α} :
      a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, idist a b < ε := by
    trans
    · apply mem_closure_iff_nhds_basis nhds_basis_ball
    · simp only [mem_ball']
      iff_intro h h
      · intros ε ε_pos
        specialize h ε ε_pos
        exact h
      · intros i i_pos
        specialize h ⟨min 1 i, _, _⟩ _
        1,2: grind only [= min_def]
        · simp [*]
        · obtain ⟨y, y_in_s, idist_lt_min_one_i⟩ := h
          exists y, y_in_s
          grind only [= min_def, Subtype.mk_lt_mk]

  theorem denseRange_iff {α β} [PseudoIMetricSpace α] {f : β → α} :
      DenseRange f ↔ ∀ x, ∀ r > 0, ∃ y, idist x (f y) < r := by
    rw [Metric.denseRange_iff]
    iff_intro h h
    · intros x r r_pos
      exact h x r r_pos
    · intros x r r_pos
      obtain ⟨y, idist_lt⟩ := h x ⟨min 1 r, le_min zero_le_one (le_of_lt r_pos), min_le_left _ _⟩ (lt_min zero_lt_one r_pos)
      exists y
      by_cases r_le : 1 ≤ r
      · rw! [min_eq_left r_le] at idist_lt
        apply LT.lt.trans_le (b := 1)
        · exact idist_lt
        · assumption
      · apply le_of_not_ge at r_le
        rw! [min_eq_right r_le] at idist_lt
        exact idist_lt
end IMetric

@[instance_reducible]
def PseudoIMetricSpace.induced {α β} (f : α → β) (m : PseudoIMetricSpace β) : PseudoIMetricSpace α where
  idist x y := idist (f x) (f y)
  idist_self _ := idist_self _
  idist_comm _ _ := idist_comm _ _
  idist_triangle _ _ _ := idist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_idist := (IMetric.uniformity_basis_idist.comap (Prod.map f f)).eq_biInf

@[instance_reducible]
def IMetricSpace.induced {α β} (f : α → β) (hf : Function.Injective f) (m : IMetricSpace β) : IMetricSpace α :=
  { m.toPseudoIMetricSpace.induced f with
    eq_of_idist_eq_zero x y h := hf (m.eq_of_idist_eq_zero (f x) (f y) h)
  }

@[instance_reducible]
def PseudoIMetricSpace.ofIDistTopology.{u} {α : Type u} [TopologicalSpace α] (idist : α → α → I)
  (idist_self : ∀ x, idist x x = 0) (idist_comm : ∀ x y, idist x y = idist y x)
  (idist_triangle : ∀ x y z, (idist x z : ℝ) ≤ idist x y + idist y z)
  (H : ∀ s, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, (idist x y : ℝ) < ε → y ∈ s) :
    PseudoIMetricSpace α where
  idist
  idist_self
  idist_comm
  idist_triangle
  toUniformSpace :=
    (uniformSpaceOfIDist idist idist_self idist_comm idist_triangle).replaceTopology (by
      rw [TopologicalSpace.ext_iff]
      intros s
      trans
      · exact H s
      · apply forall₂_congr
        intros x x_in_s
        symm
        apply Filter.HasBasis.mem_iff
        refine (UniformSpace.hasBasis_ofFun (exists_gt (0 : ℝ)) (λ x y ↦ idist x y : _ → _ → ℝ) ?_ ?_ ?_ ?_).comap (Prod.mk x)
        · simp only [unitInterval.zero_eq, implies_true, idist_self]
        · solve_by_elim
        · assumption
        · apply UniformSpace.ofDist_aux
    )
  uniformity_idist := rfl

@[instance_reducible]
def IMetricSpace.ofIDistTopology.{u} {α : Type u} [TopologicalSpace α] (idist : α → α → I)
  (idist_self : ∀ x, idist x x = 0) (idist_comm : ∀ x y, idist x y = idist y x)
  (idist_triangle : ∀ x y z, (idist x z : ℝ) ≤ idist x y + idist y z)
  (H : ∀ s, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, (idist x y : ℝ) < ε → y ∈ s)
  (eq_of_idist_eq_zero : ∀ x y, idist x y = 0 → x = y) :
    IMetricSpace α where
  __ := PseudoIMetricSpace.ofIDistTopology idist idist_self idist_comm idist_triangle H
  eq_of_idist_eq_zero

theorem Isometry.of_idist_eq.{u, v} {α : Type u} {β : Type v} [PseudoIMetricSpace α] [PseudoIMetricSpace β] {f : α → β}
    (h : ∀ (x y : α), idist (f x) (f y) = idist x y) : Isometry f := by
  apply Isometry.of_dist_eq
  change ∀ x y, (idist (f x) (f y) : ℝ) = idist x y
  solve_by_elim

theorem Isometry.to_idist_eq.{u, v} {α : Type u} {β : Type v} [PseudoIMetricSpace α] [PseudoIMetricSpace β] {f : α → β}
    (h : Isometry f) : ∀ (x y : α), idist (f x) (f y) = idist x y := by
  intros x y

  change ∀ x y, _ at h
  conv at h => enter [2, 2]; rw [edist_dist, edist_dist]
  change ∀ x y, ENNReal.ofReal (idist (f x) (f y) : ℝ) = ENNReal.ofReal (idist x y) at h

  specialize h x y
  injections _ h
  rw [max_eq_left, max_eq_left] at h
  · grind only
  · grind only [= Set.mem_Icc]
  · grind only [= Set.mem_Icc]

lemma uniformContinuous_idist {α} [PseudoIMetricSpace α] :
    UniformContinuous fun p : α × α => idist p.1 p.2 :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun {a b} h =>
      calc dist (dist a.1 a.2) (dist b.1 b.2) ≤ dist a.1 b.1 + dist a.2 b.2 :=
        dist_dist_dist_le _ _ _ _
      _ ≤ dist a b + dist a b := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ < ε / 2 + ε / 2 := add_lt_add h h
      _ = ε := add_halves ε⟩

protected lemma UniformContinuous.idist {α β} [PseudoIMetricSpace α] [UniformSpace β] {f g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous λ b ↦ idist (f b) (g b) :=
  uniformContinuous_idist.comp (hf.prodMk hg)

@[continuity]
lemma continuous_idist {α} [PseudoIMetricSpace α] :
    Continuous fun p : α × α ↦ idist p.1 p.2 :=
  uniformContinuous_idist.continuous

@[continuity]
nonrec theorem Continuous.idist {α β} [PseudoIMetricSpace α] [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    Continuous λ (b : β) ↦ idist (f b) (g b) :=
  continuous_idist.comp₂ hf hg

section Transport
  noncomputable def transport (x : ℝ) (h : x ≥ 0) : I where
    val := x / (1 + x)
    property := by constructor <;> bound

  @[simp] theorem transport_zero : transport 0 (by rfl) = 0 := by
    grind only [= transport, = Set.Icc.mk_zero]

  theorem transport_eq {x : ℝ} {hx : x ≥ 0} : transport x hx = 1 - (1 / (1 + x)) := by
    grind only [= transport]

  theorem transport_add {x y : ℝ} {hx : x ≥ 0} {hy : y ≥ 0} :
      (transport (x + y) (Left.add_nonneg hx hy) : ℝ) ≤ transport x hx + transport y hy := by
    unfold transport

    change (x + y) / (1 + (x + y)) ≤ x / (1 + x) + y / (1 + y)
    rw [add_div]
    apply add_le_add
    · rw [div_le_div_iff₀] <;> bound
    · rw [div_le_div_iff₀] <;> bound

  theorem transport_mono {x y : ℝ} {hx : x ≥ 0} {hy : y ≥ 0} (h : x ≤ y) :
      transport x hx ≤ transport y hy := by
    unfold transport

    change x / (1 + x) ≤ y / (1 + y)
    rw [div_le_div_iff₀]
    · grind only
    · positivity
    · positivity

  theorem transport_strictMono {x y : ℝ} {hx : x ≥ 0} {hy : y ≥ 0} (h : x < y) :
      transport x hx < transport y hy := by
    show x / (1 + x) < y / (1 + y)
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith

  theorem transport_lt_one {x : ℝ} {hx : x ≥ 0} : (transport x hx : ℝ) < 1 := by
    show x / (1 + x) < 1
    rw [div_lt_one (by linarith)]
    linarith

  theorem transport_pos {x : ℝ} (hx : x > 0) : (transport x hx.le : ℝ) > 0 := by
    show 0 < x / (1 + x)
    exact div_pos hx (by linarith)

  theorem lt_of_transport_lt {x y : ℝ} {hx : x ≥ 0} {hy : y ≥ 0}
      (h : (transport x hx : ℝ) < transport y hy) : x < y := by
    rcases lt_trichotomy x y with hlt | rfl | hgt
    · exact hlt
    · exact absurd h (lt_irrefl _)
    · exact absurd h (not_lt.mpr (transport_strictMono hgt).le)

  theorem transport_lt_iff {x : ℝ} {hx : x ≥ 0} {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) :
      (transport x hx : ℝ) < ε ↔ x < ε / (1 - ε) := by
    show x / (1 + x) < ε ↔ x < ε / (1 - ε)
    have h1ε : (1 : ℝ) - ε > 0 := by linarith
    constructor
    · intro h
      rw [div_lt_iff₀ (by linarith)] at h
      rw [lt_div_iff₀ h1ε]
      nlinarith
    · intro h
      rw [div_lt_iff₀ (by linarith)]
      rw [lt_div_iff₀ h1ε] at h
      nlinarith

  open scoped Real in
  @[instance_reducible]
  noncomputable def IMetricSpace.transportMetricSpace {α} [inst : MetricSpace α] : IMetricSpace α where
    idist x y := transport (dist x y) dist_nonneg
    idist_self x := by rw! [dist_self, transport_zero]; rfl
    idist_comm x y := by rw! [dist_comm]; rfl
    idist_triangle x y z := by
      have : dist x y + dist y z ≥ 0 := by positivity

      trans (transport (dist x y + dist y z) this : ℝ)
      · exact transport_mono (dist_triangle x y z)
      · apply transport_add
    eq_of_idist_eq_zero {x y} h := by
      generalize_proofs dist_mem_I at h
      injection h with h
      grind only [dist_le_zero]
    toUniformSpace := inst.toUniformSpace
    uniformity_idist := by
      rw [PseudoMetricSpace.uniformity_dist]
      apply le_antisymm
      · apply le_iInf₂ λ δ δ_pos ↦ ?_
        by_cases hδ : δ < 1
        · apply iInf₂_le_of_le (δ / (1 - δ)) (div_pos δ_pos (by linarith))
          apply Filter.principal_mono.mpr
          intro p (hxy : dist p.1 p.2 < δ / (1 - δ))
          change (transport (dist p.1 p.2) dist_nonneg : ℝ) < δ
          exact (transport_lt_iff δ_pos hδ).mpr hxy
        · apply iInf₂_le_of_le 1 one_pos
          apply Filter.principal_mono.mpr
          intro p (_ : dist p.1 p.2 < 1)
          change (transport (dist p.1 p.2) dist_nonneg : ℝ) < δ
          exact lt_of_lt_of_le transport_lt_one (not_lt.mp hδ)
      · apply le_iInf₂ λ δ δ_pos ↦ ?_
        apply iInf₂_le_of_le (transport δ δ_pos.le : ℝ) (transport_pos δ_pos)
        apply Filter.principal_mono.mpr
        intro p (hxy : (transport (dist p.1 p.2) dist_nonneg : ℝ) < (transport δ δ_pos.le : ℝ))
        change dist p.1 p.2 < δ
        exact lt_of_transport_lt hxy
end Transport

theorem PseudoIMetricSpace.dist_eq {α} [PseudoIMetricSpace α] {x y : α} :
    dist x y = (idist x y : ℝ) := by
  rfl

theorem PseudoIMetricSpace.edist_eq {α} [PseudoIMetricSpace α] {x y : α} :
    edist x y = ENNReal.ofReal (idist x y : ℝ) := by
  rw [← PseudoIMetricSpace.dist_eq, edist_dist]
