import CustomPrelude
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Sums.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Defs.Induced
import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.CompleteLattice.Group

/- Some general stuff, don't care. -/

@[variable_alias]
class abbrev CompleteEMetricSpace.{u} (α : Type u) := EMetricSpace α, CompleteSpace α

noncomputable instance {α β : Type _} [CompleteEMetricSpace β] : CompleteEMetricSpace (α → β) where
  edist f g := ⨆ x : α, edist (f x) (g x) -- uniform distance
  edist_self f := by simp
  edist_comm f g := by
    congr
    ext1 x
    rw [edist_comm]
  edist_triangle f g h := by
    rw [iSup_le_iff]
    intros i
    trans ⨆ i, edist (f i) (g i) + edist (g i) (h i)
    · rw [le_iSup_iff]
      intros b h'
      specialize h' i
      trans edist (f i) (g i) + edist (g i) (h i)
      · apply edist_triangle
      · assumption
    · apply iSup_add_le
  eq_of_edist_eq_zero {f g} h := by
    apply funext
    change _ = ⊥ at h
    simp_rw [iSup_eq_bot] at h
    exact eq_of_edist_eq_zero ∘' h
  complete := by
    admit

noncomputable instance {α β : Type _} [inst : CompleteEMetricSpace β] : CompleteEMetricSpace (α → β) where
  __ := inferInstanceAs (EMetricSpace (α → β))
  complete := (inferInstanceAs (CompleteEMetricSpace (α → β))).complete

def ndi {α β : Type _} [EMetricSpace α] [EMetricSpace β] (f : α → β) : Prop :=
  ∀ x y : α, edist (f x) (f y) ≤ edist x y

theorem id_ndi {α : Type _} [EMetricSpace α] : ndi (id : α → α) := by
  intros x y
  rfl

theorem ndi_comp {α β γ : Type _} {g : β → γ} {f : α → β} [EMetricSpace α] [EMetricSpace β] [EMetricSpace γ] (hg : ndi g) (hf : ndi f) :
    ndi (g ∘ f) := by
  unfold ndi at hg hf ⊢
  intros x y
  trans edist (f x) (f y)
  · apply hg
  · apply hf

namespace CategoryTheory.Functor.OfSequence
  def mapOp.{u, v} {C : Type u} [Category.{v, u} C] {X : ℕ → C} (f : (n : ℕ) → X (n + 1) ⟶ X n) (i j : ℕ) (h : j ≥ i) :
      X j ⟶ X i :=
    Quiver.Hom.unop <| map (Quiver.Hom.op ∘' f) i j h
end CategoryTheory.Functor.OfSequence

/-!
We define the (large) category `𝒞` of complete metric spaces.
-/

open CategoryTheory

/-- `Obj` is the type of complete metric spaces, the objects of our soon-to-be-defined category. -/
structure Obj.{u} : Type (u + 1) where
  α : Type u
  [toInhabited : Inhabited α]
  [toCompleteSpace : CompleteEMetricSpace α]
private abbrev Obj.Type (o : Obj) := o.α
private abbrev Obj.Inhabited (o : Obj) := o.toInhabited
private abbrev Obj.Metric (o : Obj) := o.toCompleteSpace

-- private abbrev Obj.mk (α : Type _) [CompleteMetricSpace α] : Obj := ⟨α, inferInstance⟩

instance (priority := high) {o : Obj} : CompleteEMetricSpace o.α := o.Metric
instance {o : Obj} : Inhabited o.α := o.Inhabited

-- TODO: reuse some definitions and results from mathlib (such as `Cocone`s etc.)

-- NOTE: isn't this some sort of specialized product category?
-- Definition 3.1
/-- The category `𝒞` of complete metric spaces. -/
instance instCategoryCompleteMetricSpace : LargeCategory Obj where
  Hom := λ o₁ o₂ ↦ { x : (o₁.α → o₂.α) × (o₂.α → o₁.α) // Isometry x.1 ∧ Topology.IsEmbedding x.1 ∧ ndi x.2 ∧ (x.2 ∘ x.1) = id }
  id := λ o ↦ { val := ⟨id, id⟩, property := ⟨isometry_id, Topology.IsEmbedding.id, id_ndi, rfl⟩ }
  comp := λ ⟨⟨i₁, j₁⟩, ⟨iso_i₁, embed_i₁, ndi_j₁, comp_eq_id₁⟩⟩ ⟨⟨i₂, j₂⟩, ⟨iso_i₂, embed_i₂, ndi_j₂, comp_eq_id₂⟩⟩ ↦
    { val := ⟨i₂ ∘ i₁, j₁ ∘ j₂⟩,
      property := ⟨Isometry.comp (g := i₂) iso_i₂ iso_i₁, Topology.IsEmbedding.comp (g := i₂) embed_i₂ embed_i₁, ndi_comp (g := j₁) ndi_j₁ ndi_j₂, by
        convert_to j₁ ∘ (j₂ ∘ i₂) ∘ i₁ = id
        rwa [comp_eq_id₂, Function.id_comp]⟩ }

noncomputable instance {x y : Obj} : EMetricSpace (x ⟶ y) :=
  inferInstanceAs (EMetricSpace { _x : (x.α → y.α) × (y.α → x.α) // _ })

abbrev i {x y : Obj} (h : x ⟶ y) : x.1 → y.1 := h.1.1
abbrev j {x y : Obj} (h : x ⟶ y) : y.1 → x.1 := h.1.2


open ENNReal

-- Definition 3.2
/--
  `δ ι`, for every arrow `ι : M₁ ⟶ M₂ ∈ 𝒞`, can be regarded as a measure of the quality with which `M₂` is approximated by `M₁`:
  the smaller `δ ι`, the denser `M₁` is embedded into `M₂`.
-/
noncomputable def δ {M₁ M₂ : Obj} (ι : M₁ ⟶ M₂) : ℝ≥0∞ := edist (i ι ∘ j ι) id

-- Definition 3.3.a
-- TODO: switch to this representation later, for use with `Cocone` etc.
-- structure Tower (C : Type _) [Category C] where
--   F : ℕ ⥤ C
--   jsp : (n : ℕ) → F.obj n ⟶ F.obj (n + 1)
def Tower (C : Type _) [Category C] := (D : ℕ → C) × ((n : ℕ) → D n ⟶ D (n + 1))
abbrev Tower.D {C : Type _} [Category C] (T : Tower C) : ℕ → C := T.1
abbrev Tower.ι {C : Type _} [Category C] (T : Tower C) : (n : ℕ) → T.D n ⟶ T.D (n + 1) := T.2

theorem Tower.Obj.j_comp_i_eq_id {T : Tower Obj} {n : ℕ} : j (T.ι n) ∘ i (T.ι n) = id := by
  let ⟨_, _, _, _, comp_eq_id⟩ := T.ι n
  dsimp [j, i]
  assumption

def Tower.map {C D : Type _} [Category C] [Category D] (F : C ⥤ D) (T : Tower C) : Tower D := ⟨F.obj ∘' T.D, F.map ∘' T.ι⟩

-- Definition 3.3.b
def Tower.IsConverging (T : Tower Obj) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m n, (h : m > n) → n ≥ N → δ (Functor.OfSequence.map T.ι n m (le_of_lt h)) < ε

-- Definition 3.6
-- TODO: use `Cocone`?
def Tower.IsCone {C : Type _} [Category C] (T : Tower C) (D : C) (γ : (n : ℕ) → T.D n ⟶ D) : Prop :=
  ∀ n : ℕ, γ n = T.ι n ≫ γ (n + 1)

-- Definition 3.7
-- TODO: use `Limits.IsInitial`?
def Tower.IsInitialCone {C : Type _} [Category C] (T : Tower C) (D : C) (γ : (n : ℕ) → T.D n ⟶ D) : Prop :=
  T.IsCone D γ ∧ ∀ D' γ', T.IsCone D' γ' → ∃! (ι : D ⟶ D'), ∀ n : ℕ, γ n ≫ ι = γ' n

-- Lemma 3.8
/-- `D` is an initial cone iff `id_D` is the limit of the sequence `(γₙ)ₙ`. -/
lemma initiality (T : Tower Obj) (converging : T.IsConverging) (D : Obj) (γ : (n : ℕ) → T.D n ⟶ D) :
    T.IsInitialCone D γ ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n > N, edist id (i (γ n) ∘ j (γ n)) < ε := by
  admit

open scoped ENNReal in
section
  private def D (T : Tower Obj) : Type _ := { seq : (n : ℕ) → (T.D n).α // ∀ n : ℕ, j (T.ι n) (seq (n + 1)) = seq n }

  private noncomputable abbrev d (T : Tower Obj) (x y : D T) : ℝ≥0∞ := ⨆ n : ℕ, edist (x.val n) (y.val n)

  lemma ENNReal.iSup_add_le_add_iSup {ι : Type _} {u v : ι → ℝ≥0∞} : ⨆ x, (u + v) x ≤ (⨆ x, u x) + ⨆ x, v x :=
    iSup_le λ i ↦ add_le_add (le_iSup u i) (le_iSup v i)

  -- Lemma 3.10
  private noncomputable def instCompleteEMetricSpaceD (T : Tower Obj) (converging : T.IsConverging) : CompleteEMetricSpace (D T) where
    edist := d T
    edist_self x := by
      unfold d
      simp_rw [edist_self, ENNReal.iSup_eq_zero]
      exact λ _ ↦ True.intro
    edist_comm x y := by
      unfold d
      simp_rw [edist_comm]
    edist_triangle x y z := by
      unfold d
      trans ⨆ n, (edist (x.val n) (y.val n) + edist (y.val n) (z.val n))
      · apply iSup_mono
        intros i
        apply edist_triangle
      · apply ENNReal.iSup_add_le_add_iSup
    eq_of_edist_eq_zero {x y} h := by
      unfold d at h
      apply Subtype.ext
      funext n
      rw [ENNReal.iSup_eq_zero] at h
      apply eq_of_edist_eq_zero
      exact h n
    complete := by admit

  private def instInhabitedD (T : Tower Obj) : Inhabited (D T) := by
    rw [D]
    let x : (T.D 0).α := default
    apply Inhabited.mk
    fapply Subtype.mk
    · intro k
      exact Functor.OfSequence.map (X := λ k ↦ (T.D k).α) (i ∘' T.ι) 0 k (Nat.zero_le k) x
    · intro n
      by_cases n_zero : n = 0 <;> beta_reduce
      · subst n
        dsimp [Functor.OfSequence.map, Function.dcomp]
        change (j (T.ι 0) ∘ i (T.ι 0)) x = x
        rw [Tower.Obj.j_comp_i_eq_id]
        rfl
      · -- TODO: show that the sequence can be uncons-ed, then rw with `j ∘ i = id`
        admit

  private def γ (T : Tower Obj) (converging : T.IsConverging) (n : ℕ) : T.D n ⟶ {α := D T, toInhabited := instInhabitedD T, toCompleteSpace := instCompleteEMetricSpaceD T converging} where
    val := ⟨λ x ↦ {
      val := λ k ↦
        if h : k < n
        then Functor.OfSequence.mapOp (X := λ k ↦ (T.D k).α) (j ∘' T.ι) k n (le_of_lt h) x
        else if h' : k = n
        then h' ▸ x
        else Functor.OfSequence.map (X := λ k ↦ (T.D k).α) (i ∘' T.ι) n k (Nat.le_of_not_lt h) x,
      property := by
        admit
    }, λ x ↦ x.val n⟩
    property := by
      admit

  -- Definition 3.9
  noncomputable def directLimit (T : Tower Obj) (converging : T.IsConverging) : { x : (D : Obj) × ((n : ℕ) → T.D n ⟶ D) // T.IsCone x.1 x.2 } := {
    val := ⟨{α := D T, toInhabited := instInhabitedD T, toCompleteSpace := instCompleteEMetricSpaceD T converging}, γ T converging⟩
    property := by
      admit
  }

  -- attribute [-instance] instTopologicalSpaceSigma in
  -- noncomputable def directLimit.measure {T : Tower Obj} {converging : T.IsConverging} (x : (directLimit T converging).1.1.Type) : ℕ∞ :=
  --   -- FIXME: No...
  --   -- Ideally this would be defined similarly to the degree in [De Bakker & Zucker]...
  --   -- Though there is no way for us to do that because we are not using sets...unless we trick the system
  --   -- and use `Set.univ`...
  --   -- But then we would have `Set.univ : Set (D n)` and `Set.univ : Set (D (n - 1))`, which are of incompatible types.
  --   -- Anyways, `Set.univ` doesn't work for our purpose because we may wish to consider sets which do not represent ALL
  --   -- representable values.
  --   sorry
  --   -- have iso_i (n : ℕ) : Isometry (i (T.ι n)) := let ⟨⟨_, _⟩, ⟨iso_i, _, _, _⟩⟩ := T.ι n; iso_i
  --   -- let : PseudoMetricSpace ((n : ℕ) × (T.D n).Type) := Metric.inductivePremetric iso_i
  --   -- @Metric.toInductiveLimit (X := λ k ↦ (T.D k).Type) (f := i ∘' T.ι) inferInstance iso_i 0 (x.1 0)
  --   --   |>.lift Sigma.fst λ x y h ↦ by
  --   --     admit
end

-- Lemma 3.11
lemma directLimit.is_initial_cone (T : Tower Obj) (T_converging : T.IsConverging) :
    T.IsInitialCone (directLimit T T_converging).1.1 (directLimit T T_converging).1.2 := by
  admit

-- Definition 3.12
def Functor.Contracting (F : Obj ⥤ Obj) : Prop :=
  ∃ ε < 1, ∀ D E : Obj, ∀ ι : D ⟶ E, δ (F.map ι) ≤ ε * δ ι

-- Lemma 3.13
lemma Functor.Contracting.preserves_converging_towers
  (F : Obj ⥤ Obj) (contracting : Functor.Contracting F) (T : Tower Obj) (converging : T.IsConverging) :
    (T.map F).IsConverging := by
  admit

-- Lemma 3.13
lemma Functor.Contracting.preserves_initial_cones
  (F : Obj ⥤ Obj) (contracting : Functor.Contracting F) (T : Tower Obj) (converging : T.IsConverging) (D : Obj)
  (γ : (n : ℕ) → T.D n ⟶ D) (D_cone : T.IsCone D γ) :
    (T.map F).IsInitialCone (F.obj D) (F.map ∘' γ) := by
  admit

section
  private def D' {C : Type _} [Category C] (F : C ⥤ C) (D₀ : C) : (n : ℕ) → C
    | 0 => D₀
    | n + 1 => F.obj (D' F D₀ n)

  private def ι {C : Type _} [Category C] (F : C ⥤ C) {D₀ : C} (ι₀ : D₀ ⟶ F.obj D₀) : (n : ℕ) → D' F D₀ n ⟶ D' F D₀ (n + 1)
    | 0 => ι₀
    | n + 1 => F.map (ι F ι₀ n)

  -- Theorem 3.14
  noncomputable def Functor.fixed_point' {C : Type _} [Category C] (F : C ⥤ C) (D₀ : C) (ι₀ : D₀ ⟶ F.obj D₀)
    {T : Tower C} (D : C) (γ : (n : ℕ) → T.D n ⟶ D) (D_initial_cone : T.IsInitialCone D γ)
    (FD_initial_cone : (T.map F).IsInitialCone (F.obj D) (F.map ∘' γ)) (T_def : T = ⟨D' F D₀, ι F ι₀⟩ := by rfl) :
      D ≅ F.obj D :=
    /- NOTE:
      Given that the direct limit of a converging tower is an initial cone of such tower,
      and that any contracting functor `F` preserves initial cones,
      do we have that the direct limit forms an initial object of the `F`-algebra?
      In which case, we freely obtain the isomorphism.

      Then hom-contractiveness guarantees that our initial object is unique up to isomorphism.
    -/
    have T_D_eq : T.D = D' F D₀ := T_def ▸ rfl
    have T_ι_eq : T.ι = λ n ↦ T_D_eq ▸ ι F ι₀ n := T_def ▸ rfl

    have T_D_succ_eq n : T.D (n + 1) = F.obj (T.D n) := T_D_eq ▸ rfl

    let T' : Tower C := ⟨λ n ↦ D' F D₀ (n + 1), λ n ↦ ι F ι₀ (n + 1)⟩
    have T'_eq : T' = T.map F := T_def ▸ rfl

    have T'_D_eq : T'.D = T.D ∘ (· + 1) := T_D_eq ▸ rfl
    have T'_ι_eq : T'.ι = T'_D_eq ▸ (T.ι ∘' (· + 1)) := T_ι_eq ▸ by
      apply eq_of_heq
      rw [heq_eqRec_iff_heq]
      refine Function.hfunext rfl (λ n n' eq ↦ ?_)
      cases eq
      dsimp [Function.dcomp]
      rw [heq_eqRec_iff_heq]

    have T'_D_eq' : T'.D = F.obj ∘ T.D := by
      funext n
      erw [T'_D_eq, Function.comp, T_D_succ_eq]
      rfl

    have D_initial_cone : T'.IsInitialCone D (T'_D_eq ▸ γ ∘' (· + 1)) := by
      constructor
      · intros n
        replace D_initial_cone := D_initial_cone.1 (n + 1)
        admit
      · intros D' γ' D'_cone
        admit
    have FD_initial_cone : T'.IsInitialCone (F.obj D) (T'_D_eq' ▸ F.map ∘' γ) := by
      constructor
      · intros n
        replace FD_initial_cone := FD_initial_cone.1 n
        admit
      · intros D' γ' D'_cone
        admit

    let (eq := hom_def) hom := Classical.choose <| D_initial_cone.2 _ _ FD_initial_cone.1
    -- have hom_spec := Classical.choose_spec <| D_initial_cone.2 _ _ FD_initial_cone.1
    let (eq := inv_def) inv := Classical.choose <| FD_initial_cone.2 _ _ D_initial_cone.1
    -- have inv_spec := Classical.choose_spec <| FD_initial_cone.2 _ _ D_initial_cone.1

    {
      hom
      inv
      hom_inv_id := by
        admit
      inv_hom_id := by
        admit
    }

  noncomputable abbrev Functor.fixed_point {C : Type _} [Category C] (F : C ⥤ C) (D₀ : C) (ι₀ : D₀ ⟶ F.obj D₀) :
      let T : Tower C := ⟨D' F D₀, ι F ι₀⟩
      ∀ (D : C) (γ : (n : ℕ) → T.D n ⟶ D) (_ : T.IsInitialCone D γ)
        (_ : (T.map F).IsInitialCone (F.obj D) (F.map ∘' γ)), D ≅ F.obj D :=
    Functor.fixed_point' F D₀ ι₀
end

-- Corollary 3.15
def Functor.Contracting.exists_fixed_point
  (F : Obj ⥤ Obj) (contracting : Functor.Contracting F) (D₀ : Obj) (ι₀ : D₀ ⟶ F.obj D₀) :
    Σ D : Obj, D ≅ F.obj D := by
  sorry


------------------------------------------------------------
---   Base-point category and stuff to be inserted here  ---
------------------------------------------------------------

-- TODO: Definition 4.1
-- TODO: Theorem 4.2




-- Definition 4.3
def Functor.HomContracting (F : Obj ⥤ Obj) : Prop :=
  ∀ P Q : Obj, ∃ ε < 1, ∀ ι ι' : P ⟶ Q, edist (F.map ι) (F.map ι') ≤ ε * edist ι ι'

-- Theorem 4.4
section
  @[reducible]
  private def D'' (F : Obj ⥤ Obj) : (n : ℕ) → Obj
    | 0 => Obj.mk PUnit
    | n + 1 => F.obj (D'' F n)

  @[reducible]
  private def ι'' (F : Obj ⥤ Obj) : (n : ℕ) → D'' F n ⟶ D'' F (n + 1)
    | 0 => ⟨⟨λ .unit ↦ default, λ _ ↦ .unit⟩, ⟨
      by apply isometry_subsingleton,
      by apply Topology.IsEmbedding.of_subsingleton,
      by admit,
      by rfl⟩⟩
    | n + 1 => F.map (ι'' F n)

  theorem jsp (F : Obj ⥤ Obj) (contracting : Functor.Contracting F) (hom_contracting : Functor.HomContracting F) : Tower.IsConverging ⟨D'' F, ι'' F⟩ := by
    -- because `F` is contracting, the tower should eventually converge
    admit

  noncomputable def Functor.exists_unique_fixed_point_of_contracting_of_hom_contracting
    (F : Obj ⥤ Obj) (contracting : Functor.Contracting F) (hom_contracting : Functor.HomContracting F) :
      Σ' (D : Obj) (fixed_point : F.obj D ≅ D), ∀ (D' : Obj) (iso_fixed_point : F.obj D' ≅ D'), D ≅ D' :=
    let T : Tower Obj := ⟨D'' F, ι'' F⟩
    have T_converging : T.IsConverging := jsp F ‹_› ‹_›

    let iso : F.obj (directLimit T T_converging).1.1 ≅ (directLimit T T_converging).1.1 :=
      have D''_eq : D'' F = D' F (D'' F 0) := by
        funext n
        induction n <;> unfold D' D''
        case zero => rfl
        case succ _ IH => rw [IH]
      have ι''_eq : ι'' F = D''_eq ▸ ι F (ι'' F 0) := by
        apply eq_of_heq
        rw [heq_eqRec_iff_heq]
        refine Function.hfunext rfl λ n n' eq ↦ ?_
        cases eq
        induction n <;> unfold ι ι''
        case zero => rfl
        case succ _ IH => congr <;> {rw [D''_eq]; rfl}

      Functor.fixed_point' F (D'' F 0) (ι'' F 0) (directLimit T T_converging).1.1 (directLimit T T_converging).1.2
        (directLimit.is_initial_cone T T_converging)
        (Functor.Contracting.preserves_initial_cones F contracting T T_converging _ _ (directLimit T T_converging).2)
        (by unfold T; congr; nth_rw 1 [ι''_eq]; apply eqRec_heq_self)
        |>.symm

    let iso_unique (D' : Obj) (iso : F.obj D' ≅ D') : (directLimit T T_converging).1.1 ≅ D' := by
      admit

    { fst := (directLimit T T_converging).1.1
      snd.fst := iso
      snd.snd := iso_unique
    }
end

open Classical in
noncomputable def Functor.Contracting.fixedPointMeasure
  {F : Obj ⥤ Obj} {contracting : Functor.Contracting F} {hom_contracting : Functor.HomContracting F} {D fix fix_unique}
  (h : ⟨D, fix, fix_unique⟩ = Functor.exists_unique_fixed_point_of_contracting_of_hom_contracting F contracting hom_contracting)
  (x : D.Type) :
    ℕ∞ :=
  letI γ := (directLimit ⟨D'' F, ι'' F⟩ (jsp F ‹_› ‹_›)).1.2
  haveI D_eq := PSigma.noConfusion h λ fst_eq snd_eq ↦ fst_eq

  if h : ∃ (k : ℕ), i (D_eq ▸ γ (k + 1)) (j (F.map (γ k)) (D_eq ▸ i fix.inv x)) = x then
    ↑(choose h)
  else
    ⊤

/-! # Functors
-/

section Functors
  -- Definition 5.1
  inductive Func.{u} : Type (u+1) where
    | const (α : Type u) [Inhabited α] [CompleteEMetricSpace α]
    | id (ε : ℝ) (h : ε > 0 := by norm_num)
    | «fun» (F₁ F₂ : Func)
    | fun1 (F₁ F₂ : Func)
    | sum (F₁ F₂ : Func)
    | prod (F₁ F₂ : Func)
    | power (F : Func)
    | comp (F₁ F₂ : Func)

  -- Lemma 5.2

  def K.{u, v} (α : Type u) [Inhabited α] [CompleteEMetricSpace α] : Obj.{v} ⥤ Obj.{u} where
    obj _ := Obj.mk α
    map _ := {
      val := ⟨id, id⟩
      property := ⟨isometry_id, Topology.IsEmbedding.id, id_ndi, rfl⟩
    }

  noncomputable def instCompleteEMetricSpaceDistMul {α} [CompleteEMetricSpace α] {ε : ℝ} (h : ε > 0) : CompleteEMetricSpace α where
    edist := λ x y ↦ ENNReal.ofReal ε * edist x y
    edist_self x := by norm_num [edist_self]
    edist_comm x y := by norm_num [edist_comm]
    edist_triangle x y z := by admit
    eq_of_edist_eq_zero h := by admit
    uniformity_edist := by admit
    __ := inferInstanceAs (CompleteSpace α)

  noncomputable def Id'.{u} (ε : ℝ) (h : ε > 0 := by norm_num) : Obj.{u} ⥤ Obj.{u} where
    obj P := {
      α := P.α
      toInhabited := inferInstance
      toCompleteSpace := instCompleteEMetricSpaceDistMul h
    }
    map {X Y} := λ ⟨⟨i, j⟩, ⟨iso_i, embed_i, ndi_j, comp_eq_id⟩⟩ ↦ {
      val := ⟨λ x ↦ i x, λ x ↦ j x⟩
      property := by
        split_ands
        · intros x y
          change ENNReal.ofReal ε * edist _ _ = ENNReal.ofReal ε * edist _ _
          congr 1
          exact iso_i x y
        · assumption
        · intros x y
          change ENNReal.ofReal ε * edist _ _ ≤ ENNReal.ofReal ε * edist _ _
          apply mul_le_mul_of_nonneg_left
          · exact ndi_j x y
          · apply zero_le
        · assumption
    }
    map_id X := by

      admit
    map_comp {X Y Z} f g := by
      admit

  noncomputable def Fun.{u, v, w} (F₁ : Obj.{u} ⥤ Obj.{v}) (F₂ : Obj.{u} ⥤ Obj.{w}) : Obj.{u} ⥤ Obj.{max v w} where
    obj P := Obj.mk ((F₁.obj P).α → (F₂.obj P).α)
    map {X Y} ι :=
      let ⟨⟨i₁, j₁⟩, ⟨iso_i₁, embed_i₁, ndi_j₁, comp_eq_id₁⟩⟩ := F₁.map ι
      let ⟨⟨i₂, j₂⟩, ⟨iso_i₂, embed_i₂, ndi_j₂, comp_eq_id₂⟩⟩ := F₂.map ι
      { val := ⟨λ f ↦ i₂ ∘ f ∘ j₁, λ g ↦ j₂ ∘ g ∘ i₁⟩
        property := by -- TODO: extract
          and_intros
          ·
            admit
          ·
            admit
          ·
            admit
          ·
            admit
      }

  noncomputable def Fun1.{u, v, w} (F₁ : Obj.{u} ⥤ Obj.{v}) (F₂ : Obj.{u} ⥤ Obj.{w}) : Obj.{u} ⥤ Obj.{max v w} where
    obj P := Obj.mk ((F₁.obj P).α → (F₂.obj P).α)
    map ι :=
      let ⟨⟨i₁, j₁⟩, ⟨iso_i₁, embed_i₁, ndi_j₁, comp_eq_id₁⟩⟩ := F₁.map ι
      let ⟨⟨i₂, j₂⟩, ⟨iso_i₂, embed_i₂, ndi_j₂, comp_eq_id₂⟩⟩ := F₂.map ι
      { val := ⟨λ f ↦ i₂ ∘ f ∘ j₁, λ g ↦ j₂ ∘ g ∘ i₁⟩
        property := by admit
      }


  -- FIXME: Why is there no `EMetricSpace` on `_ ⊕ _`??????
  local instance {α β} [CompleteEMetricSpace α] [CompleteEMetricSpace β] : CompleteEMetricSpace (α ⊕ β) := sorry

  -- attribute [instance] Metric.metricSpaceSum in
  noncomputable def Sum'.{u, v, w} (F₁ : Obj.{u} ⥤ Obj.{v}) (F₂ : Obj.{u} ⥤ Obj.{w}) : Obj.{u} ⥤ Obj.{max v w} where
    obj P := Obj.mk ((F₁.obj P).α ⊕ (F₂.obj P).α)
    map ι :=
      let ⟨⟨i₁, j₁⟩, _⟩ := F₁.map ι
      let ⟨⟨i₂, j₂⟩, _⟩ := F₂.map ι
      { val := ⟨λ p ↦ p.map i₁ i₂, λ q ↦ q.map j₁ j₂⟩
        property := by admit
      }

  theorem ENNReal.ofReal_max {x y : ℝ} : ENNReal.ofReal (max x y) = max (ENNReal.ofReal x) (ENNReal.ofReal y) := by
    unfold ENNReal.ofReal
    -- erw [Real.coe_toNNReal' (max x y)]

    admit

  theorem Prod.map.isometry_of_isometry {α β γ δ : Type _} {f : α → β} {g : γ → δ}
    [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ] [PseudoMetricSpace δ]
    (h₁ : Isometry f) (h₂ : Isometry g) :
      Isometry (Prod.map f g) := by
    intro ⟨a, b⟩ ⟨c, d⟩
    rw [edist_dist]
    change ENNReal.ofReal (max (dist (f a) (f c)) (dist (g b) (g d))) = _
    rw [ENNReal.ofReal_max, ← edist_dist, ← edist_dist, h₁, h₂, edist_dist, edist_dist, ← ENNReal.ofReal_max, edist_dist]
    rfl

  def Prod'.{u, v, w} (F₁ : Obj.{u} ⥤ Obj.{v}) (F₂ : Obj.{u} ⥤ Obj.{w}) : Obj.{u} ⥤ Obj.{max v w} where
    obj P := Obj.mk ((F₁.obj P).α × (F₂.obj P).α)
    map ι :=
      let ⟨⟨i₁, j₁⟩, ⟨iso_i₁, _, _, _⟩⟩ := F₁.map ι
      let ⟨⟨i₂, j₂⟩, ⟨iso_i₂, _, _, _⟩⟩ := F₂.map ι
      { val := ⟨λ p ↦ p.map i₁ i₂, λ q ↦ q.map j₁ j₂⟩
        property := by
          and_intros
          · -- change Isometry (Prod.map i₁ i₂)
            -- apply Prod.map.isometry_of_isometry <;> assumption
            admit
          · admit
          · admit
          · admit
      }

  open scoped Function in
  noncomputable instance {α} [CompleteEMetricSpace α] : CompleteEMetricSpace {s : Set α // IsClosed s} where
    -- TODO: find the proof somewhere
    edist := EMetric.hausdorffEdist on Subtype.val
    edist_self := λ ⟨s, _⟩ ↦ EMetric.hausdorffEdist_self
    edist_comm := λ ⟨s, _⟩ ⟨t, _⟩ ↦ EMetric.hausdorffEdist_comm
    edist_triangle := λ ⟨s, _⟩ ⟨t, _⟩ ⟨u, _⟩ ↦ EMetric.hausdorffEdist_triangle
    eq_of_edist_eq_zero := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      admit
      -- rw [IsClosed.hausdorffEdist_zero_iff_eq hx hy] at h
      -- · simp [h]
      -- ·
      --   admit
    complete := by admit

  noncomputable def Power.{u, v} (F : Obj.{u} ⥤ Obj.{v}) : Obj.{u} ⥤ Obj.{v} where
    obj P := @Obj.mk { s : Set (F.obj P).α // IsClosed s } ⟨⟨∅, isClosed_empty⟩⟩ inferInstance
    map ι :=
      let ⟨⟨i, j⟩, ⟨iso_i, embed_i, _, _⟩⟩ := F.map ι
      { val := ⟨λ ⟨X, h⟩ ↦ ⟨i '' X, by rwa [← Topology.IsClosedEmbedding.isClosed_iff_image_isClosed iso_i.isClosedEmbedding]⟩,
                λ ⟨Y, h⟩ ↦ ⟨closure (j '' Y), isClosed_closure⟩⟩
        property := by admit
      }

  def Comp.{u, v, w} (F₁ : Obj.{v} ⥤ Obj.{w}) (F₂ : Obj.{u} ⥤ Obj.{v}) : Obj.{u} ⥤ Obj.{w} := F₂ ⋙ F₁

  noncomputable def Func.interp.{u} : Func.{u} → Obj.{u} ⥤ Obj.{u}
    | const k => K k
    | id ε h => Id' ε h
    | «fun» F₁ F₂ => Fun F₁.interp F₂.interp
    | fun1 F₁ F₂ => Fun1 F₁.interp F₂.interp
    | sum F₁ F₂ => Sum' F₁.interp F₂.interp
    | prod F₁ F₂ => Prod' F₁.interp F₂.interp
    | power F => Power F.interp
    | comp F₁ F₂ => Comp F₁.interp F₂.interp

  open scoped ENNReal

  -- Definition 5.3
  noncomputable def Func.contractCoeff : Func → ℝ≥0∞
    | const _ => 0
    | id ε _h => ENNReal.ofReal ε
    | «fun» F₁ F₂ => max (⊤ * F₁.contractCoeff) F₂.contractCoeff
    | fun1 F₁ F₂ => F₁.contractCoeff + F₂.contractCoeff
    | sum F₁ F₂ => max F₁.contractCoeff F₂.contractCoeff
    | prod F₁ F₂ => max F₁.contractCoeff F₂.contractCoeff
    | power F => F.contractCoeff
    | comp F₁ F₂ => F₁.contractCoeff * F₂.contractCoeff

  namespace Func
    scoped notation "𝓀" "(" M ")" => Func.const M
    scoped notation "𝟙⟨" ε ", " h "⟩" => Func.id ε h
    scoped notation "𝟙⟨" ε "⟩" => Func.id ε
    scoped notation:70 F₁:70 " ⟶ᶠ " F₂:71 => Func.«fun» F₁ F₂
    scoped notation:70 F₁:70 " ⟶₁ᶠ " F₂:71 => Func.fun1 F₁ F₂
    scoped notation:75 F₁:76 " ⊕ᶠ " F₂:75 => Func.sum F₁ F₂
    scoped notation:77 F₁:78 " ×ᶠ " F₂:77 => Func.prod F₁ F₂
    scoped notation "𝒫ᶜˡ" "(" F ")" => Func.power F
    scoped notation:75 F₁:75 " ∘ᶠ " F₂:76 => Func.comp F₁ F₂
  end Func

  -- Theorem 5.4.1
  lemma jsp₄ (F : Func) {P Q : Obj} (ι : P ⟶ Q) :
      δ (F.interp.map ι) ≤ F.contractCoeff * δ ι := by
    fun_induction Func.interp F with
    | case1 α =>
      change edist (id ∘ id) id ≤ 0 * δ ι
      norm_num
    | case2 ε h =>
      change edist (_ ∘ _) id ≤ ENNReal.ofReal ε * δ ι
      rw [Id']

      sorry
    | case3 F₁ F₂ F₁_ih F₂_ih => sorry
    | case4 F₁ F₂ F₁_ih F₂_ih => sorry
    | case5 F₁ F₂ F₁_ih F₂_ih => sorry
    | case6 F₁ F₂ F₁_ih F₂_ih => sorry
    | case7 F ih => sorry
    | case8 F₁ F₂ F₁_ih F₂_ih => sorry

  -- Corollary 5.5.1
  theorem Func.contracting_of_contractCoeff_lt_one (F : Func) (h : F.contractCoeff < 1) : Functor.Contracting F.interp := by
    exists F.contractCoeff
    constructor
    · change _ < 1
      assumption
    · intros D E ι
      exact jsp₄ F ι

  -- Theorem 5.4.2
  lemma jsp₅ (F : Func) {P Q : Obj} (ι ι' : P ⟶ Q) :
      edist (F.interp.map ι) (F.interp.map ι') ≤ F.contractCoeff * edist ι ι' := by
    fun_induction Func.interp F with
    | case1 α =>

      admit
    | case2 ε h => admit
    | case3 F₁ F₂ F₁_ih F₂_ih => admit
    | case4 F₁ F₂ F₁_ih F₂_ih => admit
    | case5 F₁ F₂ F₁_ih F₂_ih => sorry
    | case6 F₁ F₂ F₁_ih F₂_ih => sorry
    | case7 F ih => sorry
    | case8 F₁ F₂ F₁_ih F₂_ih => sorry

  -- Corollary 5.5.2
  theorem Func.homContracting_of_contractCoeff_lt_one (F : Func) (h : F.contractCoeff < 1) : Functor.HomContracting F.interp := by
    intros P Q
    exists F.contractCoeff
    constructor
    · change _ < 1
      assumption
    · intros ι ι'
      exact jsp₅ F ι ι'

  -- Corollary 5.6
  @[reducible]
  noncomputable def Func.exists_iso_of_contracting (F : Func) (h : F.contractCoeff < 1) :
      Σ' (D : Obj) (_ : F.interp.obj D ≅ D), (∀ (D' : Obj) (_ : F.interp.obj D' ≅ D'), D ≅ D') :=
    haveI contracting := Func.contracting_of_contractCoeff_lt_one F h
    haveI hom_contracting := Func.homContracting_of_contractCoeff_lt_one F h
    Functor.exists_unique_fixed_point_of_contracting_of_hom_contracting _ contracting hom_contracting
end Functors

namespace Proc
  theorem comp_i_eq_i_comp {P Q R : Obj} {f : Q ⟶ R} {g : P ⟶ Q} : i f ∘ i g = i (g ≫ f) := by
    let ⟨⟨i₁, _⟩, ⟨_, _, _, _⟩⟩ := f
    let ⟨⟨i₂, _⟩, ⟨_, _, _, _⟩⟩ := g
    rfl

  theorem i_inv_i_hom_eq_id {D D' : Obj} (iso : D ≅ D') (x : D.α) : i iso.inv (i iso.hom x) = x := by
    change (i iso.inv ∘ i iso.hom) x = x
    rw [comp_i_eq_i_comp, iso.hom_inv_id]
    rfl

  theorem i_hom_i_inv_eq_id {D D' : Obj} (iso : D ≅ D') (x : D'.α) : i iso.hom (i iso.inv x) = x := by
    change (i iso.hom ∘ i iso.inv) x = x
    rw [comp_i_eq_i_comp, iso.inv_hom_id]
    rfl

  theorem j_ι_i_ι_eq_id {D D' : Obj} {ι : D ⟶ D'} {x} : j ι (i ι x) = x := by
    let ⟨⟨i, j⟩, ⟨_, _, _, comp_eq_id⟩⟩ := ι
    rw [funext_iff] at comp_eq_id
    exact comp_eq_id x

  open Classical in
  noncomputable instance : EMetricSpace Prop where
    edist p q := if p ↔ q then ⊥ else ⊤
    edist_self p := by simp
    edist_comm p q := by
      split_ifs with h₁ h₂ h₃ <;> solve
        | simp [h₁] at h₂
        | simp [h₃] at h₁
        | norm_num
    edist_triangle p q r := by
      split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ <;> solve
        | simp [h₅, h₆] at h₁
        | norm_num
    eq_of_edist_eq_zero {p q} h := by
      split_ifs at h with h₁
      · exact propext h₁
      · simp at h

  instance : UniformSpace Prop := ⊥

  noncomputable instance : CompleteEMetricSpace Prop := inferInstance

  instance : MetricSpace Bool where
    __ := MetricSpace.ofDistTopology (λ x y ↦ if x = y then 0 else 1)
      (λ x ↦ if_pos rfl)
      (λ x y ↦ by conv_lhs => enter [0, x, y, 1]; apply propext eq_comm)
      (λ x y z ↦ by
        beta_reduce
        split_ifs <;> solve
          | norm_num
          | subst_vars; contradiction)
      (λ s ↦ by
        beta_reduce
        admit)
      (λ x y h ↦ by
        beta_reduce at h
        split_ifs at h <;> solve
          | assumption
          | simp at h)

  instance : CompleteEMetricSpace Bool := inferInstance

  open scoped Func in
  section
    noncomputable abbrev Branch.F.{u} (α β γ δ : Type u) [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ] :
        Func.{u} :=
         𝓀(γ) ×ᶠ (𝓀(α) ×ᶠ 𝓀(ULift Bool) ⟶₁ᶠ 𝟙⟨1/2⟩)
      ⊕ᶠ 𝓀(γ) ×ᶠ 𝓀(α) ×ᶠ 𝟙⟨1/2⟩
      ⊕ᶠ 𝓀(γ) ×ᶠ 𝟙⟨1/2⟩
      ⊕ᶠ 𝓀(γ) ×ᶠ 𝟙⟨1/2⟩
      ⊕ᶠ 𝓀(δ) ×ᶠ 𝟙⟨1/2⟩

    noncomputable abbrev F.{u} (α β γ δ : Type u) [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ] :
        Func.{u} :=
         𝓀(β)
      ⊕ᶠ 𝓀(PUnit)
      ⊕ᶠ (𝓀(δ) ⟶ᶠ 𝒫ᶜˡ(Branch.F α β γ δ))
  end

  theorem F.interp_eq.{u} {α β γ δ : Type u} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ] :
      (F α β γ δ).interp =
        Sum' (K β) (Sum' (K PUnit)
          (Fun.{u, u, u} (K δ) (Power (Sum' (Prod' (K γ) (Fun1 (Prod' (K α) (K (ULift Bool))) (Id' (1/2))))
            (Sum' (Prod' (K γ) (Prod' (K α) (Id' (1/2)))) (Sum' (Prod' (K γ) (Id' (1/2)))
              (Sum' (Prod' (K γ) (Id' (1/2))) (Prod' (K δ) (Id' (1/2)))))))))) := rfl

  -- theorem Proc.F.interp_map_eq.{u} {α β γ δ : Type u} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ] :
  --     ∀ D E (ι : D ⟶ E), ((F α β γ δ).interp.map ι).1 =
  --       ⟨
  --         Sum.map id (Sum.map id λ f ↦ ?_ ∘ f ∘ id),
  --         Sum.map id (Sum.map id λ g ↦ ?_ ∘ g ∘ id)
  --       ⟩ := by
  --   intros D E ι

  --   admit

  -- TODO: some match patterns

  lemma F.contractCoeff_lt_one.{u} {α β γ δ : Type u} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ] :
      (Proc.F α β γ δ).contractCoeff < 1 := by
    norm_num [Proc.F, Branch.F, Func.contractCoeff]

  lemma jsp₆ {D D' D''} (iso : D ≅ D') (iso' : D' ≅ D'') {x} : i (iso ≪≫ iso').hom x = i iso'.hom (i iso.hom x) := by
    rw [Iso.trans_hom, ← comp_i_eq_i_comp, Function.comp_def]

  lemma dom_fixpoint_eq.{u} {α β γ δ : Type u} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ]
    {P fix fix_unique} (h : ⟨P, fix, fix_unique⟩ = Func.exists_iso_of_contracting (Proc.F α β γ δ) Proc.F.contractCoeff_lt_one) :
      P = (directLimit ⟨D'' (Proc.F α β γ δ).interp, ι'' (Proc.F α β γ δ).interp⟩
                       (jsp _ (Func.contracting_of_contractCoeff_lt_one _ Proc.F.contractCoeff_lt_one) (Func.homContracting_of_contractCoeff_lt_one _ Proc.F.contractCoeff_lt_one))).1.1 := by
    injection h with _ _

  -- theorem Proc.recOn'.extracted_2.{u} {α β γ δ : Type u} [inst : Inhabited α] [inst_1 : Inhabited β]
  --   [inst_2 : Inhabited γ] [inst_3 : Inhabited δ] [inst_4 : CompleteEMetricSpace α] [inst_5 : CompleteEMetricSpace β]
  --   [inst_6 : CompleteEMetricSpace γ] [inst_7 : CompleteEMetricSpace δ] {P : Obj} {fix : (F α β γ δ).interp.obj P ≅ P}
  --   {fix_unique : (D' : Obj) → ((F α β γ δ).interp.obj D' ≅ D') → (P ≅ D')} {k m : ℕ}
  --   (h : ⟨P, ⟨fix, fix_unique⟩⟩ = (F α β γ δ).exists_iso_of_contracting Proc.F.contractCoeff_lt_one)
  --   (f : (((Func.const δ).fun (Branch.F α β γ δ).power).interp.obj P).α) (y : ((Func.const δ).interp.obj P).α) (c : γ)
  --   (p : P.α) (_b_in_1 _b_in : Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, p)))) ∈ (f y).val)
  --   (spec_h₁ :
  --     i (⋯ ▸ (↑(directLimit ⟨D'' (F α β γ δ).interp, ι'' (F α β γ δ).interp⟩ ⋯)).snd (k + 1))
  --         (j
  --           ((F α β γ δ).interp.map
  --             ((↑(directLimit ⟨D'' (F α β γ δ).interp, ι'' (F α β γ δ).interp⟩ ⋯)).snd k))
  --           (⋯ ▸ i fix.inv p)) =
  --       p)
  --   (spec_h₂ :
  --     i (⋯ ▸ (↑(directLimit ⟨D'' (F α β γ δ).interp, ι'' (F α β γ δ).interp⟩ ⋯)).snd (m + 1))
  --         (j
  --           ((F α β γ δ).interp.map
  --             ((↑(directLimit ⟨D'' (F α β γ δ).interp, ι'' (F α β γ δ).interp⟩ ⋯)).snd m))
  --           (⋯ ▸ Sum.inr (Sum.inr f))) =
  --       i fix.hom (Sum.inr (Sum.inr f))) :
  --     k < m := by
  --   admit


  noncomputable def F.map.{u} {α β γ δ : Type u} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ]
    {P D : Obj} (f : P.α → D.α) :
      ((Proc.F α β γ δ).interp.obj P).α → ((Proc.F α β γ δ).interp.obj D).α
    | Sum.inl v => Sum.inl v
    | Sum.inr (Sum.inl .unit) => Sum.inr (Sum.inl .unit)
    | Sum.inr (Sum.inr g) => Sum.inr (Sum.inr λ σ ↦ ⟨closure (f' '' (g σ).val), isClosed_closure⟩)
  where
    f' : ((Branch.F α β γ δ).interp.obj P).α → ((Branch.F α β γ δ).interp.obj D).α
      | Sum.inl ⟨c, π⟩ => Sum.inl ⟨c, λ v ↦ f (π v)⟩
      | Sum.inr (Sum.inl ⟨c, v, p⟩) => Sum.inr (Sum.inl ⟨c, v, f p⟩)
      | Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩)) => Sum.inr (Sum.inr (Sum.inl ⟨c, f p⟩))
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩))) => Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, f p⟩)))
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨σ, p⟩))) => Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨σ, f p⟩)))

  noncomputable def cata₁.{u} {α β γ δ : Type u} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ]
    {P fix fix_unique} (h : ⟨P, fix, fix_unique⟩ = Func.exists_iso_of_contracting (Proc.F α β γ δ) Proc.F.contractCoeff_lt_one)
    {D : Obj} (φ : ((Proc.F α β γ δ).interp.obj D).α → D.α) :
      P.α → D.α :=
    -- fix.inv ≫ (Proc.F α β γ δ).interp.map (Proc.cata h φ) ≫ φ
    λ x ↦ φ <| F.map (Proc.cata₁ h φ) <| i fix.inv x
  termination_by x => 0
  decreasing_by
    -- TODO: assume termination for now, but it should hold…right?
    all: admit

  noncomputable def cata₂.{u} {α β γ δ : Type u} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ]
    {P fix fix_unique} (h : ⟨P, fix, fix_unique⟩ = Func.exists_iso_of_contracting (Proc.F α β γ δ) Proc.F.contractCoeff_lt_one)
    {D : Obj} (φ : ((Proc.F α β γ δ).interp.obj D).α → ((Proc.F α β γ δ).interp.obj D).α → D.α) :
      P.α → P.α → D.α :=
    -- TODO: check that this does what we actually want
    letI D' := Obj.mk (P.α → D.α)
    letI φ' : ((Proc.F α β γ δ).interp.obj D').α → D'.α := λ x y ↦
      Proc.cata₁ (D := D) h (φ (F.map (λ z : D'.α ↦ z y) x)) y
    Proc.cata₁ (D := D') h φ'

  -- noncomputable def Proc.recOn₁.{u, v, w} {α β γ δ : Type u} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ]
  --   {P fix fix_unique} (h : ⟨P, fix, fix_unique⟩ = Func.exists_iso_of_contracting (Proc.F α β γ δ) Proc.F.contractCoeff_lt_one) (x : P.α)
  --   {motive₁ : P.α → Sort v} {motive₂ : _ ⊕ _ ⊕ _ ⊕ _ ⊕ _ → Sort w}
  --   ----- Processes
  --   (leaf : ∀ (v : β), motive₁ (i fix.hom (Sum.inl v)))
  --   (abort : motive₁ (i fix.hom (Sum.inr (Sum.inl PUnit.unit))))
  --   (branch : ∀ f : _ → { s : Set _ // _}, (∀ σ, ∀ b ∈ (f σ).1, motive₂ b) → motive₁ (i fix.hom (Sum.inr (Sum.inr f))))
  --   ----- Branches
  --   (recv : ∀ (c : γ) (π : α × ULift Bool → P.α), (∀ v b, motive₁ (π ⟨v, b⟩)) → motive₂ (Sum.inl (c, π)))
  --   (send : ∀ (c : γ) (v : α) (p : P.α), motive₁ p → motive₂ (Sum.inr (Sum.inl (c, v, p))))
  --   (close : ∀ (c : γ) (p : P.α), motive₁ p → motive₂ (Sum.inr (Sum.inr (Sum.inl (c, p)))))
  --   (sync : ∀ (c : γ) (p : P.α), motive₁ p → motive₂ (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, p))))))
  --   (next : ∀ (σ : δ) (p : P.α), motive₁ p → motive₂ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (σ, p)))))) :
  --     motive₁ x :=
  --   i_hom_i_inv_eq_id fix x ▸ match h' : i fix.inv x with
  --     | .inl v => h'.symm ▸ leaf v
  --     | .inr (.inl .unit) => h'.symm ▸ abort
  --     | .inr (.inr f) => h'.symm ▸ branch f (λ y b _b_in ↦ match h'' : b with
  --       | Sum.inl ⟨c, π⟩ => recv c π (λ v ok ↦ Proc.recOn₁ h (π ⟨v, ok⟩) leaf abort branch recv send close sync next)
  --       | Sum.inr (Sum.inl ⟨c, v, p⟩) => send c v p (Proc.recOn₁ h p leaf abort branch recv send close sync next)
  --       | Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩)) => close c p (Proc.recOn₁ h p leaf abort branch recv send close sync next)
  --       | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩))) => sync c p (Proc.recOn₁ h p leaf abort branch recv send close sync next)
  --       | Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨σ, p⟩))) => next σ p (Proc.recOn₁ h p leaf abort branch recv send close sync next))
  -- termination_by Functor.Contracting.fixedPointMeasure h x
  -- decreasing_by
  --   -- TODO: let us assume this for now…
  --   all:
  --     apply_fun i fix.hom at h'
  --     rw [i_hom_i_inv_eq_id] at h'

  --     subst h'' h'

  --   · -- next
  --     admit
  --   · -- sync
  --     admit
  --   · -- close
  --     admit
  --   · -- send
  --     admit
  --   · -- recv
  --     admit

  -- attribute [-instance] instTopologicalSpaceSigma in
  -- noncomputable def Proc.recOn'.{u, v, w} {α β γ δ : Type u} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ]
  --   {P fix fix_unique} (h : ⟨P, fix, fix_unique⟩ = Func.exists_iso_of_contracting (Proc.F α β γ δ) Proc.F.contractCoeff_lt_one) (x : P.α)
  --   {motive₁ : _ ⊕ _ ⊕ _ → Sort v} {motive₂ : _ ⊕ _ ⊕ _ ⊕ _ ⊕ _ → Sort w}
  --   ----- Processes
  --   (leaf : ∀ (v : β), motive₁ (Sum.inl v))
  --   (abort : motive₁ (Sum.inr (Sum.inl PUnit.unit)))
  --   (branch : ∀ f, (∀ σ, ∀ b ∈ (f σ).1, motive₂ b) → motive₁ (Sum.inr (Sum.inr f)))
  --   ----- Branches
  --   (recv : ∀ (c : γ) (π : α × ULift Bool → P.α), (∀ v b, motive₁ (i fix.inv (π ⟨v, b⟩))) → motive₂ (Sum.inl (c, π)))
  --   (send : ∀ (c : γ) (v : α) (p : P.α), motive₁ (i fix.inv p) → motive₂ (Sum.inr (Sum.inl (c, v, p))))
  --   (close : ∀ (c : γ) (p : P.α), motive₁ (i fix.inv p) → motive₂ (Sum.inr (Sum.inr (Sum.inl (c, p)))))
  --   (sync : ∀ (c : γ) (p : P.α), motive₁ (i fix.inv p) → motive₂ (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, p))))))
  --   (next : ∀ (σ : δ) (p : P.α), motive₁ (i fix.inv p) → motive₂ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (σ, p)))))) :
  --     motive₁ (i fix.inv x) :=
  --   match h' : i fix.inv x with
  --     | .inl v => h' ▸ leaf v
  --     | .inr (.inl .unit) => h' ▸ abort
  --     | .inr (.inr f) =>
  --       h' ▸ branch f (λ y b _b_in ↦ match h' : b with
  --         | Sum.inl ⟨c, π⟩ => recv c π (λ v ok ↦ Proc.recOn' h (π ⟨v, ok⟩) leaf abort branch recv send close sync next)
  --         | Sum.inr (Sum.inl ⟨c, v, p⟩) => send c v p (Proc.recOn' h p leaf abort branch recv send close sync next)
  --         | Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩)) => close c p (Proc.recOn' h p leaf abort branch recv send close sync next)
  --         | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩))) => sync c p (Proc.recOn' h p leaf abort branch recv send close sync next)
  --         | Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨σ, p⟩))) => next σ p (Proc.recOn' h p leaf abort branch recv send close sync next))
  -- termination_by Functor.Contracting.fixedPointMeasure h x
  -- decreasing_by classical
  --   all:
  --     have : x = i fix.hom (Sum.inr (Sum.inr f)) := by rw [← ‹_ = Sum.inr (Sum.inr f)›, i_hom_i_inv_eq_id]

  --     subst h' ‹x = _›
  --     clear h'

  --     simp_wf

  --   · -- next
  --     admit
  --   · -- sync
  --     unfold Functor.Contracting.fixedPointMeasure

  --     split_ifs with h₁ h₂ h₃
  --     · have spec_h₁ := Classical.choose_spec h₁
  --       have spec_h₂ := Classical.choose_spec h₂

  --       simp [i_inv_i_hom_eq_id] at spec_h₂

  --       rw [ENat.coe_lt_coe]
  --       admit
  --     · apply ENat.coe_lt_top
  --     · -- ↯
  --       admit
  --     · -- ↯
  --       admit
  --   · -- close
  --     admit
  --   · -- send
  --     admit
  --   · -- recv
  --     admit

  -- -- noncomputable def Proc.recOn'.{u, v, w} {α β γ δ : Type u} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [CompleteMetricSpace α] [CompleteMetricSpace β] [CompleteMetricSpace γ] [CompleteMetricSpace δ]
  -- --   {P : Obj} (fix : (Proc.F α β γ δ).interp.obj P ≅ P)
  -- --   {motive₁ : _ ⊕ _ ⊕ _ → Sort v} {motive₂ : _ ⊕ _ ⊕ _ ⊕ _ ⊕ _ → Sort w}
  -- --   ----- Processes
  -- --   (leaf : ∀ (v : β), motive₁ (Sum.inl v))
  -- --   (close : ∀ (c : γ) (p : P.Type), motive₁ (i fix.inv p) → motive₂ (Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩))))
  -- --   (sync : ∀ (c : γ) (p : P.Type), motive₁ (i fix.inv p) → motive₂ (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩)))))
  -- --   (next : ∀ (σ : δ) (p : P.Type), motive₁ (i fix.inv p) → motive₂ (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨σ, p⟩)))))
  -- --   (x : P.Type) :
  -- --     motive₁ (i fix.inv x) :=
  -- --   match h : i fix.inv x with
  -- --     | .inl v => h ▸ leaf v
  -- --     | .inr (.inl .unit) => h ▸ abort
  -- --     | .inr (.inr f) =>
  -- --       h ▸ branch f (λ x b _b_in ↦ match h' : b with
  -- --         | Sum.inl ⟨c, π⟩ => recv c π (λ v b ↦ Proc.recOn' fix leaf abort branch recv send close sync next (π ⟨v, b⟩))
  -- --         | Sum.inr (Sum.inl ⟨c, v, p⟩) => send c v p (Proc.recOn' fix leaf abort branch recv send close sync next p)
  -- --         | Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩)) => close c p (Proc.recOn' fix leaf abort branch recv send close sync next p)
  -- --         | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩))) => sync c p (Proc.recOn' fix leaf abort branch recv send close sync next p)
  -- --         | Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨σ, p⟩))) => next σ p (Proc.recOn' fix leaf abort branch recv send close sync next p))

  --   --   by
  --   -- let (eq := h) ⟨P', fix', fix'_unique⟩ := Func.exists_iso_of_contracting (Proc.F α β γ δ) Proc.F.contractCoeff_lt_one
  --   -- let iso : P' ≅ P := fix'_unique _ fix
  --   -- -- let iso' := fix' ≪≫ iso ≪≫ fix.symm

  --   -- injection h with P'_eq _
  --   -- have converging := Functor.exists_unique_fixed_point_of_contracting_of_hom_contracting._proof_1.{u} (Proc.F α β γ δ).interp
  --   -- dsimp [directLimit, D, Tower.ι, Tower.D] at P'_eq
  --   -- dsimp [Tower.IsConverging, Tower.ι, _root_.δ] at converging

  --   -- let (eq := h') ⟨xn, xn_def⟩ := P'_eq ▸ i iso.inv x
  --   -- sorry
  -- -- decreasing_by
  -- --   all:  simp_wf
  -- --         admit

  protected noncomputable abbrev map.{u} {α β γ δ ε : Type u} [Inhabited α] [Inhabited β] [Inhabited γ] [Inhabited δ] [Inhabited ε] [CompleteEMetricSpace α] [CompleteEMetricSpace β] [CompleteEMetricSpace γ] [CompleteEMetricSpace δ] [CompleteEMetricSpace ε]
    {P P' fix fix' fix_unique fix_unique'}
    (h₁ : ⟨P, fix, fix_unique⟩ = Func.exists_iso_of_contracting (Proc.F α β γ δ) Proc.F.contractCoeff_lt_one)
    (h₂ : ⟨P', fix', fix_unique'⟩ = Func.exists_iso_of_contracting (Proc.F α ε γ δ) Proc.F.contractCoeff_lt_one)
    (f : β → ε) :
      P.α → P'.α :=
    cata₁ h₁ <| i fix'.hom ∘' λ
      | Sum.inl v => Sum.inl (f v)
      | Sum.inr (Sum.inl .unit) => Sum.inr (Sum.inl .unit)
      | Sum.inr (Sum.inr g) =>
        let f'
          | Sum.inl ⟨c, π⟩ => Sum.inl ⟨c, π⟩
          | Sum.inr (Sum.inl ⟨c, v, p⟩) => Sum.inr (Sum.inl ⟨c, v, p⟩)
          | Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩)) => Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩))
          | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩))) => Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, p⟩)))
          | Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨σ, p⟩))) => Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨σ, p⟩)))
        have embed_f' : Topology.IsClosedEmbedding f' := by
          constructor
          · -- YES
            admit
          · -- MAYBE?
            admit
        Sum.inr (Sum.inr λ σ ↦ ⟨f' '' (g σ).val, by
          rw [← Topology.IsClosedEmbedding.isClosed_iff_image_isClosed]
          · exact (g σ).property
          · assumption
        ⟩)
end Proc
