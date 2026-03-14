import Extra.List
import Mathlib.Data.Nat.Lattice
import CustomPrelude
import Extra.Nat
import Extra.AList
import Core.Go.Syntax
import Extra.Fin
import Extra.List
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Maps.Basic

-- open scoped unitInterval

namespace unitInterval
  @[simp] theorem top_eq : (⊤ : I) = 1 := rfl
  @[simp] theorem bot_eq : (⊥ : I) = 0 := rfl

  @[simp] theorem zero_eq : (0 : I) = ⟨0, by simp⟩ := rfl

  theorem le_iff_le_val (x y : I) : x ≤ y ↔ x.val ≤ y.val := by rfl

  class IMetricSpace (α : Type _) where
    idist : α → α → I
    idist_self : ∀ x : α, idist x x = 0
    idist_comm : ∀ x y : α, idist x y = idist y x
    idist_triangle : ∀ x y z : α, (idist x z : ℝ) ≤ idist x y + idist y z
    eq_of_idist_eq_zero : ∀ {x y : α}, idist x y = 0 → x = y
  export IMetricSpace (idist idist_self idist_comm idist_triangle eq_of_idist_eq_zero)

  attribute [simp] idist_self

  instance _root_.MetricSpace.ofIMetricSpace {α} [IMetricSpace α] : MetricSpace α where
    dist x y := idist x y
    dist_self x := by rewrite [idist_self]; rfl
    dist_comm x y := by rw [idist_comm]
    dist_triangle x y z := idist_triangle x y z
    eq_of_dist_eq_zero {x y} h := by
      apply eq_of_idist_eq_zero
      exact (SetCoe.ext h.symm).symm

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

  open scoped Real in
  @[instance_reducible]
  noncomputable def IMetricSpace.ofMetricSpace {α} [MetricSpace α] : IMetricSpace α where
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

  noncomputable def half : I where
    val := 1 / 2
    property := by bound
end unitInterval

open unitInterval (IMetricSpace idist idist_self idist_comm idist_triangle eq_of_idist_eq_zero)

-- namespace ENNReal
--   theorem iInf_eq_zero {ι : Sort _} {f : ι → ℝ≥0∞} : ⨅ (i : ι), f i = 0 ↔ ∀ b > 0, ∃ (i : ι), f i < b := iInf_eq_bot f

--   theorem iInf₂_eq_zero {ι : Sort _} {κ : ι → Sort _} {f : (i : ι) → κ i → ℝ≥0∞} : ⨅ (i : ι), ⨅ (j : κ i), f i j = 0 ↔ ∀ b > 0, ∃ (i : ι) (j : κ i), f i j < b := iInf₂_eq_bot f
-- end ENNReal

class abbrev CompleteIMetricSpace.{u} (α : Type u) := IMetricSpace α, UniformSpace α, CompleteSpace α

open TopologicalSpace (Closeds)

noncomputable instance {α β : Type _} [Nonempty α] [CompleteIMetricSpace β] : CompleteIMetricSpace (α → β) where
  idist f g := ⨆ x : α, idist (f x) (g x) -- uniform distance
  idist_self f := by
    conv_lhs => enter [1, x]; rw [idist_self]
    exact iSup_const
  idist_comm f g := by
    congr with x
    rw [idist_comm]
  idist_triangle f g h := by
    admit
    -- rw [iSup_le_iff]
    -- intros i
    -- trans ⨆ i, dist (f i) (g i) + dist (g i) (h i)
    -- · rw [le_iSup_iff]
    --   intros b h'
    --   specialize h' i
    --   trans dist (f i) (g i) + dist (g i) (h i)
    --   · apply dist_triangle
    --   · assumption
    -- · apply iSup_add_le
  eq_of_idist_eq_zero {f g} h := by
    -- apply funext
    -- change _ = ⊥ at h
    -- simp_rw [iSup_eq_bot] at h
    -- exact eq_of_edist_eq_zero ∘' h
    admit
  complete := by
    admit

noncomputable instance {α β : Type _} [CompleteIMetricSpace α] [CompleteIMetricSpace β] :
    CompleteIMetricSpace (α ⊕ β) where
  idist
    | .inl x, .inl y | .inr x, .inr y => idist x y
    | .inl x, .inr y | .inr x, .inl y => ⊤
  idist_self x := by cases x <;> simp
  idist_comm x y := by
    cases x <;> cases y <;> simp [idist_comm]
  idist_triangle x y z := by
    stop
    cases x <;> cases y <;> cases z <;> simp [idist_triangle]
  eq_of_idist_eq_zero {x y} h := by
    cases x <;> cases y <;> first
      | grind only [eq_of_idist_eq_zero]
      | grind only [unitInterval.coe_ne_one, unitInterval.coe_ne_zero, unitInterval.top_eq]
  complete := by
    admit


noncomputable instance {α : Type _} {β : _ → Type _} [DecidableEq α] [(x : α) → IMetricSpace (β x)] :
    IMetricSpace (Σ x, β x) where
  idist x y := if h : x.1 = y.1 then idist x.2 (h ▸ y.2) else ⊤
  idist_self x := by cases x; simp
  idist_comm x y := by
    cases x; cases y; simp [eq_comm]
    admit
  idist_triangle := sorry
  eq_of_idist_eq_zero := sorry
  -- uniformity := by sorry
  -- symm := by sorry
  -- comp := by sorry
  -- nhds_eq_comap_uniformity := by admit
  -- complete := by
  --   sorry

noncomputable instance {α : Type _} {β : _ → Type _} [DecidableEq α] [(x : α) → IMetricSpace (β x)] :
    UniformSpace ((x : α) × β x) :=
  MetricSpace.ofIMetricSpace.toUniformSpace

noncomputable instance {α : Type _} {β : _ → Type _} [DecidableEq α] [(x : α) → CompleteIMetricSpace (β x)] :
    CompleteSpace ((x : α) × β x) where
  complete := by admit

noncomputable instance (priority := high) {α} [IMetricSpace α] [TopologicalSpace α] : IMetricSpace (Closeds α) where
  idist := sorry
  idist_self := sorry
  idist_comm := sorry
  idist_triangle := sorry
  eq_of_idist_eq_zero := sorry
  -- __ := Closeds.instCompleteSpace
  -- complete := sorry -- Closeds.instCompleteSpace (α := α) |>.complete

-------------------

structure Object.{u} where
  carrier : Type u
  [instCompleteEMetricSpace : CompleteIMetricSpace carrier]

instance {o : Object} : CompleteIMetricSpace o.carrier := o.instCompleteEMetricSpace

section Domain
  universe u v w x y z
  variable («Σ» : Type u) (Γ : Type v) (α : Type w) (β : Type x) (γ : Type y) (δ : Type z)

  inductive Branch
    | recv : Γ → (α → Bool → γ) → Branch
    | send : Γ → α → γ → Branch
    | close : Γ → γ → Branch
    | sync : Γ → γ → Branch
    | next : «Σ» → γ → Branch

  variable [DecidableEq Γ] [DecidableEq «Σ»] [DecidableEq α] [Nonempty α]

  noncomputable instance Branch.instIMetricSpace [IMetricSpace γ] : IMetricSpace (Branch «Σ» Γ α γ) where
    idist
      | .recv γ π, .recv γ' π' => if γ = γ' then unitInterval.half * (⨆ v : α, ⨆ b : Bool, idist (π v b) (π' v b)) else ⊤
      | .recv _ _, .send _ _ _ | .recv _ _, .close _ _ | .recv _ _, .sync _ _ | .recv _ _, .next _ _ => ⊤
      | .send γ v p, .send γ' v' p' => if γ = γ' ∧ v = v' then unitInterval.half * idist p p' else ⊤
      | .send _ _ _, .recv _ _ | .send _ _ _, .close _ _ | .send _ _ _, .sync _ _ | .send _ _ _, .next _ _ => ⊤
      | .close γ p, .close γ' p' => if γ = γ' then unitInterval.half * idist p p' else ⊤
      | .close _ _, .recv _ _ | .close _ _, .send _ _ _ | .close _ _, .sync _ _ | .close _ _, .next _ _ => ⊤
      | .sync γ p, .sync γ' p' => if γ = γ' then unitInterval.half * idist p p' else ⊤
      | .sync _ _, .close _ _ | .sync _ _, .send _ _ _ | .sync _ _, .recv _ _ | .sync _ _, .next _ _ => ⊤
      | .next σ p, .next σ' p' => if σ = σ' then unitInterval.half * idist p p' else ⊤
      | .next _ _, .recv _ _ | .next _ _, .send _ _ _ | .next _ _, .close _ _ | .next _ _, .sync _ _ => ⊤
    idist_self b := by
      cases b
      · conv_lhs =>
          dsimp; rw [if_pos rfl]
          enter [2, 1, v, 1, b]; rw [idist_self]
        rw [iSup_const, iSup_const, MonoidWithZero.mul_zero]
      · conv_lhs =>
          dsimp; rw [if_pos ⟨rfl, rfl⟩, idist_self]
        rw [MonoidWithZero.mul_zero]
      · conv_lhs =>
          dsimp; rw [if_pos rfl, idist_self]
        rw [MonoidWithZero.mul_zero]
      · conv_lhs =>
          dsimp; rw [if_pos rfl, idist_self]
        rw [MonoidWithZero.mul_zero]
      · conv_lhs =>
          dsimp; rw [if_pos rfl, idist_self]
        rw [MonoidWithZero.mul_zero]
    idist_comm b b' := by
      cases b <;> cases b' <;> simp_all [idist_comm, eq_comm]
    idist_triangle b b' b'' := by
      -- cases b <;> cases b' <;> cases b'' <;> simp_all
      admit
    eq_of_idist_eq_zero {b b'} h := by
      admit
    -- complete := by
    --   admit

  noncomputable instance [IMetricSpace γ] : UniformSpace (Branch «Σ» Γ α γ) :=
    MetricSpace.ofIMetricSpace.toPseudoMetricSpace.toUniformSpace

  noncomputable instance [IMetricSpace γ] : CompleteSpace (Branch «Σ» Γ α γ) :=
    sorry



  variable [CompleteIMetricSpace β] [Nonempty «Σ»]

  instance : CompleteIMetricSpace PUnit.{u + 1} where
    idist x y := ⊥
    idist_self x := rfl
    idist_comm x y := rfl
    idist_triangle x y z := by bound
    eq_of_idist_eq_zero {x y} h := rfl

  private noncomputable def IterativeDomain : ℕ → Object.{max u v w x}
    | 0 => { carrier := β ⊕ PUnit.{max u v w + 1} }
    | n + 1 => { carrier := β ⊕ PUnit.{u + 1} ⊕ («Σ» → Closeds (Branch «Σ» Γ α (IterativeDomain n).carrier)) }

  noncomputable def DomainUnion : Object where
    carrier := Σ n, (IterativeDomain «Σ» Γ α β n).carrier

  noncomputable abbrev Domain := UniformSpace.Completion (DomainUnion «Σ» Γ α β).carrier

  noncomputable instance : MetricSpace (Domain «Σ» Γ α β) :=
    UniformSpace.Completion.instMetricSpace

  instance : CompleteSpace (Domain «Σ» Γ α β) :=
    UniformSpace.Completion.completeSpace _

    -- __ := inferInstanceAs (CompleteSpace _)
    -- __ := inferInstance
    -- __ := IMetricSpace.ofMetricSpace

  -- instance [PseudoEMetricSpace α] : PseudoEMetricSpace (UniformSpace.Completion α) :=
  --   .
  -- instance UniformSpace.Completion.instEMetricSpace {α} [EMetricSpace α] : EMetricSpace (UniformSpace.Completion α) :=
  --   @EMetricSpace.ofT0PseudoEMetricSpace _ {
  --     edist := _
  --     edist_self := _
  --     edist_comm := _
  --     edist_triangle := _
  --   }
  -- noncomputable instance : CompleteEMetricSpace (Domain «Σ» Γ α β) where
  --   __ := inferInstanceAs (EMetricSpace (UniformSpace.Completion (DomainUnion «Σ» Γ α β).carrier))
  --   __ := inferInstanceAs (CompleteSpace (UniformSpace.Completion (DomainUnion «Σ» Γ α β).carrier))


  variable {«Σ» Γ α β γ δ} [CompleteIMetricSpace γ]

  mutual
    def IterativeDomain.map {n} (f : β → γ) :
        { f : (IterativeDomain «Σ» Γ α β n).carrier → (IterativeDomain «Σ» Γ α γ n).carrier
          // Topology.IsClosedEmbedding f } := {
      val := λ t ↦ match n, t with
        | 0, .inl v | n + 1, .inl v => .inl (f v)
        | 0, .inr .unit => .inr .unit
        | n + 1, .inr (.inl .unit) => .inr (.inl .unit)
        | n + 1, .inr (.inr g) => .inr (.inr λ σ ↦ {
          carrier := Branch.map (n := n) f '' (g σ).carrier
          isClosed' := by
            rw [← Topology.IsClosedEmbedding.isClosed_iff_image_isClosed]
            · exact (g σ).isClosed'
            · exact (Branch.map (n := n) f).property
        })
      property := by
        constructor
        · constructor
          ·
            admit
          · intro x y fun_eq
            dsimp at fun_eq
            split at fun_eq
            · admit
            · admit
            · admit
            · admit
            · admit
            -- cases n with
            -- | zero =>
            --   cases x <;> cases y
            --   · dsimp at fun_eq
            --     injection fun_eq
            --     admit
            --   ·
            --     admit
            --   ·
            --     admit
            --   ·
            --     admit
            -- | succ n =>
            --   sorry
        · rw [← isOpen_compl_iff]

          admit
    }
    termination_by n

    def Branch.map {n} (f : β → γ) :
        { f : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier → Branch «Σ» Γ α (IterativeDomain «Σ» Γ α γ n).carrier
          // Topology.IsClosedEmbedding f } := {
      val
        | .recv γ π => .recv γ (λ v ok ↦ (IterativeDomain.map f).val (π v ok))
        | .send γ v p => .send γ v ((IterativeDomain.map f).val p)
        | .close γ p => .close γ ((IterativeDomain.map f).val p)
        | .sync γ p => .sync γ ((IterativeDomain.map f).val p)
        | .next σ p => .next σ ((IterativeDomain.map f).val p)
      property := by
        admit
    }
    termination_by n
  end

  def DomainUnion.map (f : β → γ) (t : (DomainUnion «Σ» Γ α β).carrier) : (DomainUnion «Σ» Γ α γ).carrier := sorry

  -- noncomputable abbrev Domain.equivSelf : Domain «Σ» Γ α β ≃ᵤ (DomainUnion «Σ» Γ α β).carrier :=
  --   UniformSpace.Completion.UniformCompletion.completeEquivSelf
end Domain
