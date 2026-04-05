import CustomPrelude
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Isometry

namespace unitInterval
  @[simp] theorem top_eq : (⊤ : I) = 1 := rfl
  @[simp] theorem bot_eq : (⊥ : I) = 0 := rfl

  @[simp] theorem zero_eq : (0 : I) = ⟨0, by simp⟩ := rfl

  theorem coe_zero_eq : ↑(0 : I) = (0 : ℝ) := rfl

  theorem le_iff_le_val (x y : I) : x ≤ y ↔ x.val ≤ y.val := by rfl

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
@[reducible] def uniformSpaceOfIDist {α} (idist : α → α → I) (idist_self : ∀ x : α, idist x x = 0)
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
def IMetricSpace.of_metric_space_of_dist_le_one {α} [inst : MetricSpace α]
  (h : ∀ x y : α, dist x y ≤ 1 := by intros; bound) :
    IMetricSpace α where
  idist x y := ⟨dist x y, dist_nonneg, h x y⟩
  idist_self x := by rw! [dist_self]; rfl
  idist_comm x y := by rw! [dist_comm]; rfl
  idist_triangle x y z := dist_triangle x y z
  eq_of_idist_eq_zero {x y} eq := by
    replace eq : dist x y = 0 := by injection eq
    exact eq_of_dist_eq_zero eq
  toUniformSpace := inst.toUniformSpace
  uniformity_idist := by rw [inst.uniformity_dist]

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
    · admit
    · admit
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
