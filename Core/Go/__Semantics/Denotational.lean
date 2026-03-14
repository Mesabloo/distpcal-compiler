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

namespace ENNReal
  theorem iInf_eq_zero {ι : Sort _} {f : ι → ℝ≥0∞} : ⨅ (i : ι), f i = 0 ↔ ∀ b > 0, ∃ (i : ι), f i < b := iInf_eq_bot f

  theorem iInf₂_eq_zero {ι : Sort _} {κ : ι → Sort _} {f : (i : ι) → κ i → ℝ≥0∞} : ⨅ (i : ι), ⨅ (j : κ i), f i j = 0 ↔ ∀ b > 0, ∃ (i : ι) (j : κ i), f i j < b := iInf₂_eq_bot f
end ENNReal

class abbrev CompleteMetricSpace.{u} (α : Type u) := MetricSpace α, CompleteSpace α
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


open scoped Function in
noncomputable instance {α} [CompleteMetricSpace α] : CompleteMetricSpace {s : Set α // IsClosed s} where
  -- TODO: find the proof somewhere
  dist := Metric.hausdorffDist on Subtype.val
  dist_self := λ ⟨s, _⟩ ↦ Metric.hausdorffDist_self_zero
  dist_comm := λ ⟨s, _⟩ ⟨t, _⟩ ↦ Metric.hausdorffDist_comm
  dist_triangle := λ ⟨s, _⟩ ⟨t, _⟩ ⟨u, _⟩ ↦ Metric.hausdorffDist_triangle (by admit)
  eq_of_dist_eq_zero := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    rw [IsClosed.hausdorffDist_zero_iff_eq hx hy] at h
    · simp [h]
    ·
      admit
  complete := by admit

def instDiscreteMetricSpace {α} [DecidableEq α] : MetricSpace α where
  dist x y := if x = y then 0 else 1
  dist_self x := by rw [if_pos rfl]
  dist_comm x y := by split_ifs <;> solve | rfl | subst_vars; contradiction
  dist_triangle x y z := by split_ifs <;> solve | norm_num | subst_vars; contradiction
  eq_of_dist_eq_zero {x y} h := by split_ifs at h <;> solve | assumption | simp at h

-- instance (priority := low) {α} [DecidableEq α] [CompleteSpace α] : CompleteMetricSpace α where
--   __ := inferInstanceAs (MetricSpace α)
--   __ := inferInstanceAs (CompleteSpace α)

section Domain
  universe u v w x y z
  variable («Σ» : Type u) (Γ : Type v) (α : Type w) (β : Type x) (γ : Type y) (δ : Type z)

  def Branch : Type (max u v w y) := (Γ × (α → Bool → γ)) ⊕ (Γ × α × γ) ⊕ (Γ × γ) ⊕ (Γ × γ) ⊕ («Σ» × γ)

  variable {«Σ» Γ α β γ δ} --- [DecidableEq α] [DecidableEq β] [DecidableEq Γ] [DecidableEq «Σ»]

  @[match_pattern]
  abbrev Branch.recv (ev : Γ) (π : α → Bool → γ) : Branch «Σ» Γ α γ := .inl ⟨ev, π⟩
  @[match_pattern]
  abbrev Branch.send (ev : Γ) (v : α) (p : γ) : Branch «Σ» Γ α γ := .inr (.inl ⟨ev, v, p⟩)
  @[match_pattern]
  abbrev Branch.close (ev : Γ) (p : γ) : Branch «Σ» Γ α γ := .inr (.inr (.inl ⟨ev, p⟩))
  @[match_pattern]
  abbrev Branch.sync (ev : Γ) (p : γ) : Branch «Σ» Γ α γ := .inr (.inr (.inr (.inl ⟨ev, p⟩)))
  @[match_pattern]
  abbrev Branch.next (σ : «Σ») (p : γ) : Branch «Σ» Γ α γ := .inr (.inr (.inr (.inr ⟨σ, p⟩)))

  variable
    [DecidableEq α] [DecidableEq β] [DecidableEq Γ] [DecidableEq «Σ»] [DecidableEq γ] [DecidableEq δ]
    -- [CompleteMetricSpace α] [CompleteMetricSpace β] [CompleteSpace Γ] [CompleteSpace «Σ»] [CompleteSpace γ] [CompleteSpace δ]

  attribute [local instance] Metric.metricSpaceSum in
  noncomputable instance [CompleteMetricSpace γ] : CompleteMetricSpace (Branch «Σ» Γ α γ) where
    dist
      | .recv γ π, .recv γ' π' => if γ = γ' then (1 / 2) * (⨆ v : α, ⨆ b : Bool, dist (π v b) (π' v b)) else 1
      | .recv _ _, .send _ _ _ | .recv _ _, .close _ _ | .recv _ _, .sync _ _ | .recv _ _, .next _ _ => 1
      | .send γ v p, .send γ' v' p' => if γ = γ' ∧ v = v' then (1 / 2) * dist p p' else 1
      | .send _ _ _, .recv _ _ => 1 | .send _ _ _, .close _ _ => 1 | .send _ _ _, .sync _ _ | .send _ _ _, .next _ _ => 1
      | .close γ p, .close γ' p' => if γ = γ' then (1 / 2) * dist p p' else 1
      | .close _ _, .recv _ _ | .close _ _, .send _ _ _ | .close _ _, .sync _ _ | .close _ _, .next _ _ => 1
      | .sync γ p, .sync γ' p' => if γ = γ' then (1 / 2) * dist p p' else 1
      | .sync _ _, .close _ _ | .sync _ _, .send _ _ _ | .sync _ _, .recv _ _ | .sync _ _, .next _ _ => 1
      | .next σ p, .next σ' p' => if σ = σ' then (1 / 2) * dist p p' else 1
      | .next _ _, .recv _ _ | .next _ _, .send _ _ _ | .next _ _, .close _ _ | .next _ _, .sync _ _ => 1
    dist_self := by admit
    dist_comm := by admit
    dist_triangle := by admit
    eq_of_dist_eq_zero := by admit
    complete := by admit

  noncomputable def Proc.dist_succ [CompleteMetricSpace γ] : β ⊕ PUnit ⊕ («Σ» → { s : Set (Branch «Σ» Γ α γ) // IsClosed s }) → β ⊕ PUnit ⊕ («Σ» → { s : Set (Branch «Σ» Γ α γ) // IsClosed s }) → ℝ
    | .inl x, .inl y => if x = y then 0 else 1
    | .inl _, .inr (.inl .unit) => 1
    | .inl _, .inr (.inr _) => 1
    | .inr (.inl .unit), .inl _ => 1
    | .inr (.inl .unit), .inr (.inl .unit) => 0
    | .inr (.inl .unit), .inr (.inr _) => 1
    | .inr (.inr _), .inl _ => 1
    | .inr (.inr _), .inr (.inl .unit) => 1
    | .inr (.inr f), .inr (.inr g) => 1 ⊓ ⨆ σ : «Σ», Metric.hausdorffDist (f σ).val (g σ).val

  variable («Σ» Γ α β γ δ)

  abbrev Obj := (α : Type v) × CompleteMetricSpace α
  abbrev Obj.Type (o : Obj) : Type u := o.1
  instance {o : Obj} : CompleteMetricSpace o.Type := o.2

  noncomputable def Proc : ℕ → Obj.{max u v w x}
    | 0 => ⟨β ⊕ PUnit.{max u v w + 1}, {
      dist
        | .inl x, .inl y => if x = y then 0 else 1
        | .inl x, .inr .unit => 1
        | .inr .unit, .inl y => 1
        | .inr .unit, .inr .unit => 0
      dist_self := by admit
      dist_comm := by admit
      dist_triangle := by admit
      eq_of_dist_eq_zero := by admit
      complete := by admit
    }⟩
    | n + 1 => ⟨β ⊕ PUnit ⊕ («Σ» → { s : Set (Branch «Σ» Γ α (Proc n).Type) // IsClosed s }), {
      dist := Proc.dist_succ
      dist_self := by admit
      dist_comm := by admit
      dist_triangle := by admit
      eq_of_dist_eq_zero := by admit
      complete := by admit
    }⟩
  abbrev ProcType (n : ℕ) := (Proc «Σ» Γ α β n).Type

  abbrev Procω := Σ n : ℕ, ProcType «Σ» Γ α β n

  instance : Nonempty (Procω «Σ» Γ α β) := ⟨⟨0, .inr .unit⟩⟩


  -- limit of sequence `u` in metric spaces is `Filter.lim u`/`Filter.limUnder f u`

  open scoped ENNReal

  variable {«Σ» Γ α β γ δ} --- [DecidableEq α] [DecidableEq β] [DecidableEq Γ] [DecidableEq «Σ»]

  @[match_pattern]
  abbrev ProcType.leaf (v : β) : {n : ℕ} → ProcType «Σ» Γ α β n
    | 0 | _ + 1 => .inl v
  @[match_pattern]
  abbrev ProcType.abort : {n : ℕ} → ProcType «Σ» Γ α β n
    | 0 => .inr .unit
    | _ + 1 => .inr (.inl .unit)
  @[match_pattern]
  abbrev ProcType.branch : {n : ℕ} → («Σ» → { s : Set (Branch «Σ» Γ α (ProcType «Σ» Γ α β n)) // IsClosed s }) → ProcType «Σ» Γ α β (n + 1)
    | _, f => .inr (.inr f)

  -- def Proc.casesOn.{v} {motive : {n : ℕ} → Proc «Σ» Γ α β n → Sort v}
  --   (leaf_zero : ∀ (v : β), motive (Proc.leaf (n := 0) v)) (leaf_succ : ∀ n (v : β), motive (Proc.leaf (n := n + 1) v))
  --   (abort_zero : motive (Proc.abort (n := 0))) (abort_succ : ∀ n, motive (Proc.abort (n := n + 1)))
  --   (branch : ∀ n (f : «Σ» → Set (Branch «Σ» Γ α (Proc «Σ» Γ α β n))), motive (Proc.branch f)) :
  --     ∀ {n} (p : Proc «Σ» Γ α β n), motive p
  --   | 0, .leaf v => leaf_zero v
  --   | _ + 1, .leaf v => leaf_succ _ v
  --   | 0, .abort => abort_zero
  --   | _ + 1, .abort => abort_succ _
  --   | _ + 1, .branch f => branch _ f

  -- omit [DecidableEq α] [DecidableEq β] [DecidableEq Γ] [DecidableEq «Σ»] in
  section
    theorem ProcType.leaf.injEq {v v' : β} : {n : ℕ} → v = v' ↔ ProcType.leaf («Σ» := «Σ») (Γ := Γ) (α := α) (n := n) v = ProcType.leaf v'
      | 0 | _ + 1 => by
        iff_rintro rfl h
        · rfl
        · injections

    theorem ProcType.branch.injEq {n : ℕ} {f f' : «Σ» → { s : Set (Branch «Σ» Γ α (ProcType «Σ» Γ α β n)) // IsClosed s }} : f = f' ↔ ProcType.branch f = ProcType.branch f' := by
      iff_rintro rfl h
      · rfl
      · injections

    theorem ProcType.leaf_ne_abort {v : β} : {n : ℕ} → ProcType.leaf («Σ» := «Σ») (Γ := Γ) (α := α) (n := n) v ≠ ProcType.abort
      | 0, eq => Sum.noConfusion eq

    theorem ProcType.leaf_ne_branch {v : β} {n : ℕ} {f : «Σ» → { s : Set (Branch «Σ» Γ α (ProcType «Σ» Γ α β n)) // IsClosed s }} : ProcType.leaf v ≠ ProcType.branch f
      | eq => Sum.noConfusion eq

    theorem ProcType.abort_ne_branch {n : ℕ} {f : «Σ» → { s : Set (Branch «Σ» Γ α (ProcType «Σ» Γ α β n)) // IsClosed s }} : ProcType.abort ≠ ProcType.branch f
      | eq => by injection eq; contradiction

    theorem Branch.recv.injEq {γ γ' : Γ} {n : ℕ} {π π' : α → Bool → ProcType «Σ» Γ α β n} : γ = γ' ∧ π = π' ↔ Branch.recv («Σ» := «Σ») γ π = Branch.recv γ' π' := by
      iff_rintro ⟨rfl, rfl⟩ h
      · rfl
      · injections
        subst_vars
        exact ⟨rfl, rfl⟩

    theorem Branch.send.injEq {γ γ' : Γ} {v v' : α} {n : ℕ} {p p' : ProcType «Σ» Γ α β n} : γ = γ' ∧ v = v' ∧ p = p' ↔ Branch.send («Σ» := «Σ») γ v p = Branch.send γ' v' p' := by
      iff_rintro ⟨rfl, rfl, rfl⟩ h
      · rfl
      · injections
        subst_vars
        exact ⟨rfl, rfl, rfl⟩

    theorem Branch.close.injEq {γ γ' : Γ} {n : ℕ} {p p' : ProcType «Σ» Γ α β n} : γ = γ' ∧ p = p' ↔ Branch.close («Σ» := «Σ») (α := α) γ p = Branch.close γ' p' := by
      iff_rintro ⟨rfl, rfl⟩ h
      · rfl
      · injections
        subst_vars
        exact ⟨rfl, rfl⟩

    theorem Branch.sync.injEq {γ γ' : Γ} {n : ℕ} {p p' : ProcType «Σ» Γ α β n} : γ = γ' ∧ p = p' ↔ Branch.sync («Σ» := «Σ») (α := α) γ p = Branch.sync γ' p' := by
      iff_rintro ⟨rfl, rfl⟩ h
      · rfl
      · -- NOTE: our term is too deep for `injections` to go through it all at once...
        injections _ _ _ h
        injection h
        subst_vars
        exact ⟨rfl, rfl⟩

    theorem Branch.next.injEq {σ σ' : «Σ»} {n : ℕ} {p p' : ProcType «Σ» Γ α β n} : σ = σ' ∧ p = p' ↔ Branch.next (Γ := Γ) (α := α) σ p = Branch.next σ' p' := by
      iff_rintro ⟨rfl, rfl⟩ h
      · rfl
      · -- NOTE: our term is too deep for `injections` to go through it all at once...
        injections _ _ _ h
        injections
        subst_vars
        exact ⟨rfl, rfl⟩

    theorem Branch.recv_ne_send {γ γ' : Γ} {n : ℕ} {π : α → Bool → ProcType «Σ» Γ α β n} {v' : α} {p' : ProcType «Σ» Γ α β n} : Branch.recv («Σ» := «Σ») γ π ≠ Branch.send γ' v' p' := by
      intro eq
      injections

    theorem Branch.recv_ne_close {γ γ' : Γ} {n : ℕ} {π : α → Bool → ProcType «Σ» Γ α β n} {p' : ProcType «Σ» Γ α β n} : Branch.recv («Σ» := «Σ») γ π ≠ Branch.close γ' p' := by
      intro eq
      injections

    theorem Branch.recv_ne_sync {γ γ' : Γ} {n : ℕ} {π : α → Bool → ProcType «Σ» Γ α β n} {p' : ProcType «Σ» Γ α β n} : Branch.recv («Σ» := «Σ») γ π ≠ Branch.sync γ' p' := by
      intro eq
      injections

    theorem Branch.recv_ne_next {γ : Γ} {n : ℕ} {π : α → Bool → ProcType «Σ» Γ α β n} {σ' : «Σ»} {p' : ProcType «Σ» Γ α β n} : Branch.recv γ π ≠ Branch.next σ' p' := by
      intro eq
      injections

    theorem Branch.send_ne_close {γ γ' : Γ} {v : α} {n : ℕ} {p p' : ProcType «Σ» Γ α β n} : Branch.send («Σ» := «Σ») γ v p ≠ Branch.close γ' p' := by
      intro eq
      injections

    theorem Branch.send_ne_sync {γ γ' : Γ} {v : α} {n : ℕ} {p p' : ProcType «Σ» Γ α β n} : Branch.send («Σ» := «Σ») γ v p ≠ Branch.sync γ' p' := by
      intro eq
      injections

    theorem Branch.send_ne_next {γ : Γ} {v : α} {σ' : «Σ»} {n : ℕ} {p p' : ProcType «Σ» Γ α β n} : Branch.send γ v p ≠ Branch.next σ' p' := by
      intro eq
      injections

    theorem Branch.close_ne_sync {γ γ' : Γ} {n : ℕ} {p p' : ProcType «Σ» Γ α β n} : Branch.close («Σ» := «Σ») (α := α) γ p ≠ Branch.sync γ' p' := by
      intro eq
      injections

    theorem Branch.close_ne_next {γ : Γ} {σ' : «Σ»} {n : ℕ} {p p' : ProcType «Σ» Γ α β n} : Branch.close (α := α) γ p ≠ Branch.next σ' p' := by
      intro eq
      injections

    theorem Branch.sync_ne_next {γ : Γ} {σ' : «Σ»} {n : ℕ} {p p' : ProcType «Σ» Γ α β n} : Branch.sync (α := α) γ p ≠ Branch.next σ' p' := by
      intro eq
      injections
  end

  -- open NNReal
  -- def NNRealOne := { x : ℝ≥0 // x ≤ 1 }
  --   deriving LE, LT, Preorder, PartialOrder
  -- notation "ℝ≥0≤1" => NNRealOne

  -- noncomputable section
  --   deriving instance LinearOrder for ℝ≥0≤1
  --   deriving instance SemilatticeInf for ℝ≥0≤1
  --   deriving instance SemilatticeSup for ℝ≥0≤1
  -- end

  -- instance : Zero ℝ≥0≤1 where zero := ⟨0, zero_le_one⟩
  -- instance : One ℝ≥0≤1 where one := ⟨1, le_refl _⟩
  -- instance : Mul ℝ≥0≤1 where mul := λ ⟨x, x_le⟩ ⟨y, y_le⟩ ↦ ⟨x * y, mul_le_of_le_of_le_one x_le y_le⟩

  -- theorem NNRealOne.exists_isLUB {s : Set ℝ≥0≤1} (hne : s.Nonempty) (hbdd : BddAbove s) : ∃ x, IsLUB s x := by
  --   admit

  -- open scoped Classical in
  -- noncomputable instance : SupSet ℝ≥0≤1 where
  --   sSup s := if h : s.Nonempty ∧ BddAbove s then Classical.choose (NNRealOne.exists_isLUB h.1 h.2) else 0

  -- noncomputable instance : CompleteLattice ℝ≥0≤1 where
  --   top := 1
  --   le_top x := x.property
  --   bot := 0
  --   bot_le x := x.val.property
  --   __ := completeLatticeOfSup ℝ≥0≤1 λ s ↦ by classical
  --     change IsLUB s (if h : s.Nonempty ∧ BddAbove s then Classical.choose (NNRealOne.exists_isLUB h.1 h.2) else 0)
  --     split_ifs with h
  --     · apply Classical.choose_spec
  --     · rw [not_and_or] at h
  --       obtain h|h := h
  --       · rw [Set.not_nonempty_iff_eq_empty] at h
  --         rw [h, isLUB_empty_iff]
  --         intro x
  --         exact x.val.property
  --       · rw [not_bddAbove_iff'] at h
  --         obtain ⟨⟨y, y_le⟩, y_in, y_gt_one⟩ := h 1
  --         contradiction

  -- noncomputable instance : CompleteLinearOrder ℝ≥0≤1 where
  --   __ := inferInstanceAs (LinearOrder ℝ≥0≤1)
  --   __ := LinearOrder.toBiheytingAlgebra ℝ≥0≤1
  --   __ := inferInstanceAs (CompleteLattice ℝ≥0≤1)

  -- noncomputable def NNRealOne.halfOf (x : ℝ≥0≤1) : ℝ≥0≤1 := ⟨x.val * (1 / 2), mul_le_of_le_of_le_one x.property (by simp)⟩
  -- def NNRealOne.toReal (x : ℝ≥0≤1) : ℝ := x.val.toReal

  -- theorem NNRealOne.halfOf_iSup {ι : Sort u} (f : ι → ℝ≥0≤1) : halfOf (⨆ i, f i) = ⨆ i, halfOf (f i) := by
  --   unfold halfOf

  --   admit

  -- nonrec theorem NNRealOne.iSup_eq_bot {ι : Sort u} (f : ι → ℝ≥0≤1) : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 := iSup_eq_bot

  -- nonrec theorem NNRealOne.iInf_eq_bot {ι : Sort u} (f : ι → ℝ≥0≤1) : ⨅ i, f i = 0 ↔ ∀ b > 0, ∃ i, f i < b := iInf_eq_bot _

  -- @[simp]
  -- theorem NNRealOne.coe_zero : (0 : ℝ≥0≤1).val = (0 : ℝ≥0) := rfl

  -- @[simp]
  -- theorem NNRealOne.coe_one : (1 : ℝ≥0≤1).val = (1 : ℝ≥0) := rfl

  -- @[simp]
  -- theorem NNRealOne.halfOf_zero : NNRealOne.halfOf 0 = 0 := by
  --   unfold NNRealOne.halfOf
  --   apply Subtype.ext
  --   norm_num

  -- theorem NNRealOne.zero_ne_one : (0 : ℝ≥0≤1) ≠ 1 := λ h ↦ by
  --   rw [Subtype.eq_iff] at h
  --   norm_num at h

  -- theorem NNRealOne.one_ne_zero : (1 : ℝ≥0≤1) ≠ 0 := Ne.symm NNRealOne.zero_ne_one

  -- theorem NNRealOne.toReal_eq_zero_iff {x : ℝ≥0≤1} : x.toReal = 0 ↔ x = 0 := by
  --   iff_rintro h rfl
  --   · unfold NNRealOne.toReal at h
  --     apply Subtype.ext
  --     apply Subtype.ext
  --     rwa [NNRealOne.coe_zero]
  --   · rfl

  -- @[simp]
  -- theorem NNRealOne.zero_toReal : (0 : ℝ≥0≤1).toReal = 0 := rfl

  -- @[simp]
  -- theorem NNRealOne.one_toReal : (1 : ℝ≥0≤1).toReal = 1 := rfl

  -- -- @[simp]
  -- theorem NNRealOne.iSup_toReal {ι : Sort u} (f : ι → ℝ≥0≤1) : (⨆ i, f i).toReal = (⨆ i, (f i).toReal) := by
  --   admit
  --   -- unfold iSup
  --   -- change NNRealOne.toReal (if h : (Set.range fun i ↦ f i).Nonempty ∧ BddAbove (Set.range fun i ↦ f i) then Classical.choose (NNRealOne.exists_isLUB h.1 h.2) else 0) = _
  --   -- split_ifs
  --   -- ·
  --   --   admit
  --   -- ·
  --   --   admit

  -- -- @[simp]
  -- theorem NNRealOne.iInf_toReal {ι : Sort u} (f : ι → ℝ≥0≤1) : (⨅ i, f i).toReal = ⨅ i, (f i).toReal := by
  --   admit

  -- -- @[simp]
  -- theorem NNRealOne.max_toReal {x y : ℝ≥0≤1} : (x ⊔ y).toReal = x.toReal ⊔ y.toReal := rfl

  -- theorem NNRealOne.toReal_nonneg {x : ℝ≥0≤1} : 0 ≤ x.toReal := x.val.property

  -- theorem NNRealOne.toReal_le_one {x : ℝ≥0≤1} : x.toReal ≤ 1 := x.property

  -- noncomputable def Proc.dist : {n : ℕ} → (Proc «Σ» Γ α β n).Type → (Proc «Σ» Γ α β n).Type → ℝ≥0≤1
  --   | 0, .leaf v₁, .leaf v₂ => if v₁ = v₂ then 0 else 1
  --   | 0, .abort, .abort => 0
  --   | 0, .leaf _, .abort | 0, .abort, .leaf _ => 1
  --   | _ + 1, .leaf v₁, .leaf v₂ => if v₁ = v₂ then 0 else 1
  --   | _ + 1, .abort, .abort => 0
  --   | _ + 1, .leaf _, .abort | _ + 1, .leaf _, .branch _
  --   | _ + 1, .abort, .leaf _ | _ + 1, .abort, .branch _
  --   | _ + 1, .branch _, .leaf _ | _ + 1, .branch _, .abort => 1
  --   | n + 1, .branch f₁, .branch f₂ =>
  --                     -- Standard Hausdorff distance between `f₁ σ` and `f₂ σ`
  --     ⨆ σ : «Σ», (⨆ x ∈ f₁ σ, ⨅ y ∈ f₂ σ, d' x y) ⊔ (⨆ y ∈ f₂ σ, ⨅ x ∈ f₁ σ, d' x y)
  -- where
  --   d' {n : ℕ} : Branch «Σ» Γ α (Proc «Σ» Γ α β n) → Branch «Σ» Γ α (Proc «Σ» Γ α β n) → ℝ≥0≤1
  --     | .recv γ π, .recv γ' π' => if γ = γ' then NNRealOne.halfOf (⨆ v : α, ⨆ b : Bool, Proc.dist (π v b) (π' v b)) else 1
  --     | .recv _ _, .send _ _ _ | .recv _ _, .close _ _ | .recv _ _, .sync _ _ | .recv _ _, .next _ _ => 1
  --     | .send γ v p, .send γ' v' p' => if γ = γ' ∧ v = v' then NNRealOne.halfOf (Proc.dist p p') else 1
  --     | .send _ _ _, .recv _ _ => 1 | .send _ _ _, .close _ _ => 1 | .send _ _ _, .sync _ _ | .send _ _ _, .next _ _ => 1
  --     | .close γ p, .close γ' p' => if γ = γ' then NNRealOne.halfOf (Proc.dist p p') else 1
  --     | .close _ _, .recv _ _ | .close _ _, .send _ _ _ | .close _ _, .sync _ _ | .close _ _, .next _ _ => 1
  --     | .sync γ p, .sync γ' p' => if γ = γ' then NNRealOne.halfOf (Proc.dist p p') else 1
  --     | .sync _ _, .close _ _ | .sync _ _, .send _ _ _ | .sync _ _, .recv _ _ | .sync _ _, .next _ _ => 1
  --     | .next σ p, .next σ' p' => if σ = σ' then NNRealOne.halfOf (Proc.dist p p') else 1
  --     | .next _ _, .recv _ _ | .next _ _, .send _ _ _ | .next _ _, .close _ _ | .next _ _, .sync _ _ => 1

  -- -- open Classical in
  -- -- theorem jsp {n : ℕ} {A B : Set (Branch «Σ» Γ α (Proc «Σ» Γ α β n))} (h : ¬B.Nonempty) :
  -- --     (⨆ x ∈ A, ⨅ y ∈ B, Proc.dist.d' x y) = if A.Nonempty then ⊤ else 0 := by
  -- --   split_ifs with h'
  -- --   · rw [Set.not_nonempty_iff_eq_empty] at h
  -- --     simp_rw [h, iInf_emptyset]
  -- --     exact biSup_const h'
  -- --   · rw [Set.not_nonempty_iff_eq_empty] at h h'
  -- --     simp [h, h']

  -- mutual
  --   theorem Proc.dist_le_one : {n : ℕ} → (p p' : Proc «Σ» Γ α β n) → p.dist p' ≤ 1 :=
  --     λ p p' ↦ (p.dist p').property
  --     -- | 0, .leaf v₁, .leaf v₂ | n + 1, .leaf v₁, .leaf v₂ => by
  --     --   unfold dist
  --     --   split_ifs <;> [ apply zero_le_one | rfl ]
  --     -- | 0, .abort, .abort | n + 1, .abort, .abort => by
  --     --   unfold dist
  --     --   apply zero_le_one
  --     -- | 0, .leaf _, .abort | 0, .abort, .leaf _
  --     -- | n + 1, .leaf _, .abort | n + 1, .abort, .leaf _
  --     -- | n + 1, .leaf _, .branch _ | n + 1, .abort, .branch _
  --     -- | n + 1, .branch _, .leaf _ | n + 1, .branch _, .abort => by
  --     --   unfold dist
  --     --   rfl
  --     -- | n + 1, .branch f₁, .branch f₂ => by
  --     --   unfold dist
  --     --   simp_rw [iSup_le_iff, max_le_iff]
  --     --   intro σ
  --     --   constructor
  --     --   · by_cases h : (f₂ σ).Nonempty
  --     --     ·
  --     --       admit
  --     --     · rw [jsp h]
  --     --       admit
  --     --   · admit

  --   theorem Proc.dist.d'_le_one {n : ℕ} : (b b' : Branch «Σ» Γ α (Proc «Σ» Γ α β n)) → Proc.dist.d' b b' ≤ 1 :=
  --     λ b b' ↦ (Proc.dist.d' b b').property
  --     -- | .recv γ π, .recv γ' π' => by
  --     --   unfold dist.d'
  --     --   split_ifs <;> norm_num
  --     --   apply mul_le_one' <;> norm_num
  --     --   intro i
  --     --   constructor <;> apply Proc.dist_le_one
  --     -- | .recv γ π, .send γ' v' p' | .recv γ π, .close γ' p'
  --     -- | .recv γ π, .sync γ' p' | .recv γ π, .next σ' p' => by unfold dist.d'; rfl
  --     -- | .send γ v p, .send γ' v' p' => by
  --     --   unfold dist.d'
  --     --   split_ifs <;> norm_num
  --     --   apply mul_le_one' <;> norm_num
  --     --   apply Proc.dist_le_one
  --     -- | .send γ v p, .recv γ' π'
  --     -- | .send γ v p, .close γ' p'
  --     -- | .send γ v p, .sync γ' p'
  --     -- | .send γ v p, .next σ' p' => by unfold dist.d'; rfl
  --     -- | .close γ p, .close γ' p' => by
  --     --   unfold dist.d'
  --     --   split_ifs <;> norm_num
  --     --   apply mul_le_one' <;> norm_num
  --     --   apply Proc.dist_le_one
  --     -- | .close γ p, .recv γ' π'
  --     -- | .close γ p, .send γ' v' p'
  --     -- | .close γ p, .sync γ' p'
  --     -- | .close γ p, .next σ' p' => by unfold dist.d'; rfl
  --     -- | .sync γ p, .sync γ' p' => by
  --     --   unfold dist.d'
  --     --   split_ifs <;> norm_num
  --     --   apply mul_le_one' <;> norm_num
  --     --   apply Proc.dist_le_one
  --     -- | .sync γ p, .recv γ' π'
  --     -- | .sync γ p, .send γ' v' p'
  --     -- | .sync γ p, .close γ' p'
  --     -- | .sync γ p, .next σ' p' => by unfold dist.d'; rfl
  --     -- | .next σ p, .next σ' p' => by
  --     --   unfold dist.d'
  --     --   split_ifs <;> norm_num
  --     --   apply mul_le_one' <;> norm_num
  --     --   apply Proc.dist_le_one
  --     -- | .next σ p, .recv γ' π'
  --     -- | .next σ p, .send γ' v' p'
  --     -- | .next σ p, .close γ' p'
  --     -- | .next σ p, .sync γ' p' => by unfold dist.d'; rfl
  -- end

  -- theorem Proc.dist_comm : {n : ℕ} → (p p' : Proc «Σ» Γ α β n) → p.dist p' = p'.dist p
  --   | 0, .leaf v₁, .leaf v₂ | n + 1, .leaf v₁, .leaf v₂ => by
  --     unfold Proc.dist
  --     by_cases h : v₁ = v₂
  --     · rw [if_pos h, if_pos h.symm]
  --     · rw [if_neg h, if_neg (Ne.symm h)]
  --   | 0, .abort, .abort | n + 1, .abort, .abort => by
  --     unfold Proc.dist
  --     rfl
  --   | 0, .leaf _, .abort | 0, .abort, .leaf _
  --   | n + 1, .leaf _, .abort | n + 1, .abort, .leaf _
  --   | n + 1, .branch _, .leaf _ | n + 1, .leaf _, .branch _
  --   | n + 1, .branch _, .abort | n + 1, .abort, .branch _ => by
  --     unfold Proc.dist
  --     rfl
  --   | n + 1, .branch f₁, .branch f₂ => by
  --     unfold dist
  --     congr with σ
  --     rw [max_comm]
  --     congr with x <;> {
  --       congr with h
  --       congr with y
  --       congr with h'
  --       apply d'_comm
  --     }
  -- where
  --   d'_comm {n : ℕ} : ∀ (x y : Branch «Σ» Γ α (Proc «Σ» Γ α β n)), dist.d' x y = dist.d' y x := by
  --     rintro (⟨γ, π⟩|⟨γ, v, p⟩|⟨γ, p⟩|⟨γ, p⟩|⟨σ, p⟩) (⟨γ', π'⟩|⟨γ', v', p'⟩|⟨γ', p'⟩|⟨γ', p'⟩|⟨σ', p'⟩)
  --       <;> (unfold dist.d'; try rfl)
  --     · by_cases h'' : γ = γ'
  --       · rw [if_pos h'', if_pos h''.symm]
  --         conv_lhs => enter [1, 1, v, 1, b]; apply Proc.dist_comm
  --       · rw [if_neg h'', if_neg (Ne.symm h'')]
  --     · by_cases h'' : γ = γ' ∧ v = v'
  --       · rw [if_pos h'', if_pos (h''.imp Eq.symm Eq.symm), Proc.dist_comm]
  --       · rw [if_neg h'', if_neg λ ⟨x, y⟩ ↦ h'' ⟨x.symm, y.symm⟩]
  --     3:
  --       by_cases h'' : σ = σ'
  --       · rw [if_pos h'', if_pos (Eq.symm h''), Proc.dist_comm]
  --       · rw [if_neg h'', if_neg λ x ↦ h'' x.symm]
  --     all:
  --       by_cases h'' : γ = γ'
  --       · rw [if_pos h'', if_pos (Eq.symm h''), Proc.dist_comm]
  --       · rw [if_neg h'', if_neg (Ne.symm h'')]

  -- theorem Proc.dist_self : {n : ℕ} → (p : Proc «Σ» Γ α β n) → p.dist p = 0
  --   | 0, .leaf v | n + 1, .leaf v => by unfold Proc.dist; rw [if_pos (rfl : v = v)]
  --   | 0, .abort | n + 1, .abort => by unfold Proc.dist; rfl
  --   | n + 1, .branch f => by
  --     unfold dist
  --     conv_lhs => enter [1, r, 1, 1, x, 1, h, 1, y, 1, h']; apply Proc.dist_comm.d'_comm
  --     conv_lhs => enter [1, r]; apply sup_idem
  --     conv => apply propext iSup_eq_bot
  --     conv => enter [i]; apply propext iSup₂_eq_bot
  --     conv => enter [i, j, j_in]; apply propext <| iInf₂_eq_bot (λ i _ ↦ dist.d' i j)
  --     rintro σ x h b b_pos
  --     exists x, h
  --     rwa [d'_self]
  -- where
  --   d'_self {n : ℕ} : (x : Branch «Σ» Γ α (Proc «Σ» Γ α β n)) → dist.d' x x = 0
  --     | .recv γ π => by
  --       unfold dist.d'
  --       simp_rw [ite_true, NNRealOne.halfOf_iSup, NNRealOne.iSup_eq_bot]
  --       intro v b
  --       rw [dist_self, NNRealOne.halfOf_zero]
  --     | .send γ v p => by
  --       unfold dist.d'
  --       rw [if_pos ⟨(rfl : γ = γ), (rfl : v = v)⟩, dist_self, NNRealOne.halfOf_zero]
  --     | .close γ p | .sync γ p => by
  --       unfold dist.d'
  --       rw [if_pos (rfl : γ = γ), dist_self, NNRealOne.halfOf_zero]
  --     | .next σ p => by
  --       unfold dist.d'
  --       rw [if_pos (rfl : σ = σ), dist_self, NNRealOne.halfOf_zero]

  -- -- theorem Proc.dist_branch_branch_le_of_le {k : ℝ≥0∞} {n : ℕ} {f₁ f₂ : «Σ» → Set (Branch «Σ» Γ α (Proc «Σ» Γ α β n))}
  -- --   (h₁ : (∀ σ : «Σ», ∀ x ∈ f₁ σ, ∃ y ∈ f₂ σ, Proc.dist.d' x y ≤ k) ∧ (∀ σ : «Σ», ∀ x ∈ f₂ σ, ∃ y ∈ f₁ σ, Proc.dist.d' x y ≤ k) ∨ 1 ≤ k) :
  -- --     Proc.dist (Proc.branch f₁) (Proc.branch f₂) ≤ k := by
  -- --   unfold dist
  -- --   rw [min_def]
  -- --   split_ifs with h
  -- --   · simp_rw [iSup_le_iff, sup_le_iff, iSup_le_iff, iInf_le_iff, le_iInf_iff] at h ⊢
  -- --     refine λ σ ↦ ⟨λ x x_in b b_le_dist ↦ ?_, λ x x_in b b_le_dist ↦ ?_⟩
  -- --     · obtain ⟨h₃, h₄⟩ := h σ
  -- --       specialize h₃ _ x_in b b_le_dist
  -- --       obtain ⟨h₁, h₂⟩|_ := h₁
  -- --       · obtain ⟨y, y_in, h⟩ := h₁ σ _ x_in
  -- --         trans dist.d' x y
  -- --         · exact b_le_dist _ y_in
  -- --         · assumption
  -- --       · trans 1 <;> assumption
  -- --     · obtain ⟨h₁, h₂⟩|_ := h₁
  -- --       · obtain ⟨y, y_in, dist_le_k⟩ := h₂ σ _ x_in
  -- --         trans dist.d' x y
  -- --         · rw [dist_comm.d'_comm]
  -- --           exact b_le_dist _ y_in
  -- --         · assumption
  -- --       · trans 1
  -- --         · exact (h σ).right _ x_in b b_le_dist
  -- --         · assumption
  -- --   · obtain ⟨h₁, h₂⟩|_ := h₁
  -- --     · simp_rw [iSup_le_iff, sup_le_iff, iSup_le_iff, iInf_le_iff, le_iInf_iff] at h
  -- --       push_neg at h
  -- --       obtain ⟨σ, h⟩ := h

  -- --       have h' : ∀ i ∈ f₁ σ, ∀ (b : ℝ≥0∞), (∀ j ∈ f₂ σ, b ≤ dist.d' i j) → b ≤ 1 := λ x x_in b h ↦ by
  -- --         obtain ⟨y, y_in, dist_le_⟩ := h₁ σ x x_in
  -- --         specialize h y y_in
  -- --         trans dist.d' x y
  -- --         · assumption
  -- --         · apply Proc.dist.d'_le_one

  -- --       obtain ⟨x, x_in, b, b_le, b_gt_one⟩ := h h'
  -- --       obtain ⟨y, y_in, dist_le_k⟩ := h₂ σ x x_in
  -- --       specialize b_le y y_in
  -- --       trans b
  -- --       · apply le_of_lt
  -- --         assumption
  -- --       · trans dist.d' y x
  -- --         · assumption
  -- --         · rwa [dist_comm.d'_comm]
  -- --     · assumption

  -- omit [DecidableEq α] in
  -- lemma jsp₅ {A B : Set α} (h : A ≠ B) : ∃ x, x ∈ A ∧ x ∉ B ∨ x ∉ A ∧ x ∈ B := by
  --   rw [ne_eq, Set.ext_iff] at h
  --   push_neg at h
  --   assumption

  -- -- theorem Proc.dist_ne_zero_of_ne : {n : ℕ} → (p p' : Proc «Σ» Γ α β n) → p ≠ p' → p.dist p' ≠ 0
  -- --   | 0, .leaf _, .leaf _, h | _ + 1, .leaf _, .leaf _, h => by
  -- --     erw [ne_eq, ← Proc.leaf.injEq] at h
  -- --     unfold dist
  -- --     rw [if_neg h]
  -- --     exact NNRealOne.one_ne_zero
  -- --   | 0, .leaf _, .abort, _ | 0, .abort, .leaf _, _ | _ + 1, .leaf _, .abort, _ | _ + 1, .abort, .leaf _, _
  -- --   | _ + 1, .abort, .branch _, _ | _ + 1, .leaf _, .branch _, _ | _ + 1, .branch _, .abort, _ | _ + 1, .branch _, .leaf _, _ => by
  -- --     unfold dist
  -- --     exact NNRealOne.one_ne_zero
  -- --   | _ + 1, .branch f, .branch g, h => by
  -- --     unfold dist
  -- --     erw [ne_eq, ← Proc.branch.injEq, funext_iff, not_forall] at h
  -- --     obtain ⟨σ, b, ⟨b_in, b_nin⟩|⟨⟨b_nin, b_in⟩⟩⟩ := Exists.imp (λ _ ↦ jsp₅) h <;> clear h
  -- --     · simp_rw [ne_eq, NNRealOne.iSup_eq_bot, max_eq_iff]
  -- --       push_neg
  -- --       refine ⟨σ, λ h ↦ h ▸ ?_, λ h ↦ h ▸ ?_⟩
  -- --       · simp_rw [lt_iSup_iff, lt_iInf_iff, le_iInf_iff]
  -- --         by_contra! h'

  -- --         admit
  -- --       ·
  -- --         admit
  -- --     ·
  -- --       admit




  --     -- unfold dist
  --     -- simp_rw [ne_eq, NNRealOne.iSup_eq_bot, max_eq_iff]
  --     -- push_neg at h ⊢
  --     -- apply jsp₅ at h
  --     -- obtain ⟨i, ⟨i_in, i_nin⟩|⟨i_nin, i_in⟩⟩ := h
  --     -- · refine ⟨σ, λ h ↦ ?_, λ h ↦ ?_⟩
  --     --   · simp_rw [NNRealOne.iSup_eq_bot, NNRealOne.iInf_eq_bot, iInf_lt_iff] at h
  --     --     specialize h _ i_in
  --     --     simp_rw [iSup_lt_iff, lt_iSup_iff, lt_iInf_iff, le_iInf_iff, iSup_le_iff, iInf_le_iff, le_iInf_iff]
  --     --     refine ⟨1, ?_, ?_⟩
  --     --     ·
  --     --       admit
  --     --     ·
  --     --       admit
  --     --   ·
  --     --     admit
  --     -- ·
  --     --   admit

  -- -- theorem Proc.eq_of_dist_eq_zero : {n : ℕ} → (p p' : Proc «Σ» Γ α β n) → p.dist p' = 0 → p = p' := λ p p' ↦ by
  -- --   contrapose
  -- --   apply Proc.dist_ne_zero_of_ne

  -- theorem NNRealOne.eq_of_le_of_ge {x y : ℝ≥0≤1} (h_le : x ≤ y) (h_ge : x ≥ y) : x = y := by
  --   apply eq_of_le_of_not_lt h_le
  --   rwa [ge_iff_le, ← not_lt] at h_ge












  -- theorem Proc.eq_of_dist_eq_zero : {n : ℕ} → (p p' : Proc «Σ» Γ α β n) → p.dist p' = 0 → p = p'
  --   | _ + 1, .branch f₁, .branch f₂, h => by
  --     unfold dist at h
  --     simp_rw [NNRealOne.iSup_eq_bot, max_eq_iff] at h

  --     replace h : ∀ σ, ⨆ x ∈ f₁ σ, ⨅ y ∈ f₂ σ, dist.d' x y = 0 ∧ ⨆ y ∈ f₂ σ, ⨅ x ∈ f₁ σ, dist.d' x y = 0 := λ σ ↦ by
  --       obtain ⟨h₁, h₂⟩|⟨h₁, h₂⟩ := h σ
  --       · rw [h₁] at h₂
  --         have h₃ : ⨆ y ∈ f₂ σ, ⨅ x ∈ f₁ σ, dist.d' x y ≥ 0 := (⨆ y ∈ f₂ σ, ⨅ x ∈ f₁ σ, dist.d' x y).val.property
  --         constructor
  --         · assumption
  --         · apply NNRealOne.eq_of_le_of_ge <;> assumption
  --       · rw [h₁] at h₂
  --         have h₃ : ⨆ x ∈ f₁ σ, ⨅ y ∈ f₂ σ, dist.d' x y ≥ 0 := (⨆ x ∈ f₁ σ, ⨅ y ∈ f₂ σ, dist.d' x y).val.property
  --         constructor
  --         · apply NNRealOne.eq_of_le_of_ge <;> assumption
  --         · assumption

  --     rcongr σ b

  --     obtain ⟨h₁, h₂⟩ := h σ
  --     simp_rw [NNRealOne.iSup_eq_bot, NNRealOne.iInf_eq_bot] at h₁ h₂

  --     admit
  --   | _, _, _, _ => by admit

  -- -- should be true...
  -- -- mutual
  -- --   theorem Proc.eq_of_dist_eq_zero : {n : ℕ} → (p p' : Proc «Σ» Γ α β n) → p.dist p' = 0 → p = p'
  -- --     | 0, .leaf v₁, .leaf v₂, h | _ + 1, .leaf v₁, .leaf v₂, h => by
  -- --       unfold Proc.dist at h
  -- --       split_ifs at h <;> solve
  -- --         | subst_vars; rfl
  -- --         | exfalso; exact NNRealOne.one_ne_zero h
  -- --           -- simp at h
  -- --     | 0, .abort, .abort, h | _ + 1, .abort, .abort, h => by rfl
  -- --     | 0, .leaf v₁, .abort, h | 0, .abort, .leaf v₂, h
  -- --     | _ + 1, .leaf v₁, .abort, h | _ + 1, .abort, .leaf v₂, h
  -- --     | _ + 1, .branch f₁, .leaf v₂, h | _ + 1, .leaf v₁, .branch f₂, h
  -- --     | _ + 1, .branch f₁, .abort, h | _ + 1, .abort, .branch f₂, h => by
  -- --       unfold Proc.dist at h
  -- --       exfalso
  -- --       exact NNRealOne.one_ne_zero h
  -- --     | n + 1, .branch f₁, .branch f₂, h => by
  -- --       unfold Proc.dist at h

  -- --       simp_rw [NNRealOne.iSup_eq_bot, max_eq_iff] at h
  -- --       rcongr σ b

  -- --       obtain ⟨h₁, h₂⟩|⟨h₁, h₂⟩ := h σ <;> (
  -- --         clear h
  -- --         simp_rw [NNRealOne.iSup_eq_bot, NNRealOne.iInf_eq_bot, iInf_lt_iff] at h₁
  -- --         simp_rw [iSup_le_iff, iInf_le_iff, le_iInf_iff, le_iSup_iff, iSup_le_iff, iInf_le_iff, le_iInf_iff] at h₂
  -- --       )
  -- --       ·
  -- --         admit
  -- --       ·
  -- --         admit

  -- --   theorem Branch.eq_of_dist_eq_zero {n : ℕ} : (b b' : Branch «Σ» Γ α (Proc «Σ» Γ α β n)) → Proc.dist.d' b b' = 0 → b = b'
  -- --     | .recv γ π, .recv γ' π', h => by admit
  -- --     | _, _, _ => by admit
  -- -- end

  -- set_option maxHeartbeats 10000000 in
  -- theorem Proc.dist_triangle : {n : ℕ} → (p p' p'' : Proc «Σ» Γ α β n) → (p.dist p'').toReal ≤ (p.dist p').toReal + (p'.dist p'').toReal
  --   | 0, .leaf v₁, .leaf v₂, .leaf v₃ | _ + 1, .leaf v₁, .leaf v₂, .leaf v₃ --=> by
  --   | 0, .abort, .leaf v₂, .leaf v₃ | 0, .leaf v₁, .abort, .leaf v₃ | 0, .leaf v₁, .leaf v₂, .abort
  --   | _ + 1, .abort, .leaf v₂, .leaf v₃ | _ + 1, .leaf v₁, .abort, .leaf v₃ | _ + 1, .leaf v₁, .leaf v₂, .abort
  --   | _ + 1, .branch f₁, .leaf v₂, .leaf v₃ | _ + 1, .leaf v₁, .branch f₂, .leaf v₃
  --   | _ + 1, .leaf v₁, .leaf v₂, .branch f₃ => by
  --     unfold dist
  --     split_ifs <;> solve
  --       | norm_num
  --       | subst_vars; contradiction
  --     -- unfold dist
  --     -- split_ifs <;> norm_num
  --   | 0, .abort, .abort, .abort | _ + 1, .abort, .abort, .abort
  --   | 0, .leaf v₁, .abort, .abort | 0, .abort, .abort, .leaf v₃ | 0, .abort, .leaf v₂, .abort
  --   | _ + 1, .leaf v₁, .abort, .abort | _ + 1, .abort, .abort, .leaf v₃ | _ + 1, .abort, .leaf v₂, .abort
  --   | _ + 1, .leaf v₁, .branch f₂, .abort
  --   | _ + 1, .branch f₁, .abort, .abort | _ + 1, .abort, .branch f₂, .abort
  --   | _ + 1, .abort, .abort, .branch f₃
  --   | _ + 1, .leaf v₁, .abort, .branch f₃ | _ + 1, .abort, .branch f₂, .leaf v₃
  --   | _ + 1, .abort, .leaf v₂, .branch f₃ | _ + 1, .branch f₁, .leaf v₂, .abort
  --   | _ + 1, .branch f₁, .abort, .leaf v₃
  --   | _ + 1, .leaf v₁, .branch f₂, .branch f₃ | _ + 1, .abort, .branch f₂, .branch f₃
  --   | _ + 1, .branch f₁, .branch f₂, .abort | _ + 1, .branch f₁, .branch f₂, .leaf v₃
  --   | _ + 1, .branch f₁, .leaf v₂, .branch f₃ | _ + 1, .branch f₁, .abort, .branch f₃ => by
  --     unfold dist
  --     norm_num [NNRealOne.toReal_nonneg]
  --     all: exact le_trans NNRealOne.toReal_le_one one_le_two
  --   | _ + 1, .branch f₁, .branch f₂, .branch f₃ => by
  --     admit

  -- theorem Proc.dist_self' {n : ℕ} (p : Proc «Σ» Γ α β n) : (Proc.dist p p).toReal = (0 : ℝ) := by
  --   rw [NNRealOne.toReal_eq_zero_iff]
  --   apply Proc.dist_self

  -- theorem Proc.eq_of_dist_eq_zero' {n : ℕ} (p p' : Proc «Σ» Γ α β n) : (p.dist p').toReal = (0 : ℝ) → p = p' := by
  --   rw [NNRealOne.toReal_eq_zero_iff]
  --   apply Proc.eq_of_dist_eq_zero

  -- -- theorem Proc.dist_triangle' {n : ℕ} (p p' p'' : Proc «Σ» Γ α β n) : (p.dist p'').toReal ≤ (p.dist p').toReal + (p'.dist p'').toReal := by
  -- --   apply ENNReal.toReal_le_add
  -- --   · apply Proc.dist_triangle
  -- --   · have h' : p.dist p' < ⊤ := lt_of_le_of_lt (Proc.dist_le_one _ _) ENNReal.one_lt_top
  -- --     apply LT.lt.ne_top
  -- --     assumption
  -- --   · have h' : p'.dist p'' < ⊤ := lt_of_le_of_lt (Proc.dist_le_one _ _) ENNReal.one_lt_top
  -- --     apply LT.lt.ne_top
  -- --     assumption

  -- /-- `(Procₙ, dₙ)` is a metric space for all `n ∈ ℕ` -/
  -- noncomputable instance instMetricSpaceProcOfNat (n : ℕ) : MetricSpace (Proc «Σ» Γ α β n) where
  --   dist p p' := Proc.dist p p' |>.toReal
  --   dist_self := Proc.dist_self'
  --   dist_comm p p' := by rw [Proc.dist_comm]
  --   dist_triangle := Proc.dist_triangle
  --   eq_of_dist_eq_zero {p p'} := Proc.eq_of_dist_eq_zero' p p'

  noncomputable instance {n : ℕ} : CompleteMetricSpace (ProcType «Σ» Γ α β n) :=
    inferInstance
  noncomputable instance instMetricSpaceProcω' : CompleteMetricSpace (Procω «Σ» Γ α β) where
    __ := @Metric.Sigma.metricSpace _ _ inferInstance
    complete := by admit

  mutual
    def ProcType.lift : {m : ℕ} → (n : ℕ) → m ≤ n → ProcType «Σ» Γ α β m → ProcType «Σ» Γ α β n
      | 0, _, _, .leaf v | _ + 1, _, _, .leaf v => .leaf v
      | 0, _, _, .abort | _ + 1, _, _, .abort => .abort
      | m + 1, n + 1, h, .branch f => .branch (λ σ ↦
        let ⟨s, closed_s⟩ := f σ
        ⟨Branch.lift n (Nat.add_one_le_add_one_iff.mp h) '' s, by
          rwa [← Topology.IsClosedEmbedding.isClosed_iff_image_isClosed]
          apply Isometry.isClosedEmbedding
          intros p p'
          repeat rw [edist_dist]
          congr 1
          -- TODO: yes, this is an isometry, just prove it
          admit⟩)

    def Branch.lift {m : ℕ} (n : ℕ) (h : m ≤ n) : Branch «Σ» Γ α (ProcType «Σ» Γ α β m) → Branch «Σ» Γ α (ProcType «Σ» Γ α β n)
      | .recv γ π => .recv γ (λ v ok ↦ ProcType.lift n h (π v ok))
      | .send γ v p => .send γ v (ProcType.lift n h p)
      | .close γ p => .close γ (ProcType.lift n h p)
      | .sync γ p => .sync γ (ProcType.lift n h p)
      | .next σ p => .next σ (ProcType.lift n h p)
  end

  section
    theorem ProcType.lift.leaf {v : β} : {m n : ℕ} → {h : m ≤ n} → ProcType.lift n h (ProcType.leaf («Σ» := «Σ») (Γ := Γ) (α := α) v) = ProcType.leaf v
      | 0, _, _ => by unfold ProcType.lift; rfl
      | _ + 1, _ + 1, _ => by unfold ProcType.lift; rfl

    theorem ProcType.lift.abort : {m n : ℕ} → {h : m ≤ n} → ProcType.lift n h (ProcType.abort («Σ» := «Σ») (Γ := Γ) (α := α) (β := β)) = ProcType.abort
      | 0, _, _ => by unfold ProcType.lift; rfl
      | _ + 1, _ + 1, _ => by unfold ProcType.lift; rfl

    alias ProcType.lift.branch := ProcType.lift.eq_5
    -- theorem Proc.lift.branch : {m n : ℕ} → {h : m + 1 ≤ n + 1} → {g : «Σ» → { s : Set (Branch «Σ» Γ α (ProcType «Σ» Γ α β n)) // IsClosed s }} →
    --     ProcType.lift (n + 1) h (ProcType.branch g) = ProcType.branch (λ σ ↦ ⟨Branch.lift n (Nat.add_one_le_add_one_iff.mp h) '' (g σ).val, (_ : IsClosed _)⟩)
    --   | _, _, _, _ => by unfold lift; rfl

    theorem Branch.lift.recv {γ : Γ} {m n : ℕ} {h : m ≤ n} {π : α → Bool → ProcType «Σ» Γ α β m} : Branch.lift n h (Branch.recv γ π) = Branch.recv γ (λ v ok ↦ ProcType.lift n h (π v ok)) := by
      unfold lift
      rfl

    theorem Branch.lift.send {γ : Γ} {m n : ℕ} {h : m ≤ n} {v : α} {p : ProcType «Σ» Γ α β m} : Branch.lift n h (Branch.send γ v p) = Branch.send γ v (ProcType.lift n h p) := by
      unfold lift
      rfl

    theorem Branch.lift.close {γ : Γ} {m n : ℕ} {h : m ≤ n} {p : ProcType «Σ» Γ α β m} : Branch.lift n h (Branch.close γ p) = Branch.close γ (ProcType.lift n h p) := by
      unfold lift
      rfl

    theorem Branch.lift.sync {γ : Γ} {m n : ℕ} {h : m ≤ n} {p : ProcType «Σ» Γ α β m} : Branch.lift n h (Branch.sync γ p) = Branch.sync γ (ProcType.lift n h p) := by
      unfold lift
      rfl

    theorem Branch.lift.next {σ : «Σ»} {m n : ℕ} {h : m ≤ n} {p : ProcType «Σ» Γ α β m} : Branch.lift n h (Branch.next σ p) = Branch.next σ (ProcType.lift n h p) := by
      unfold lift
      rfl

    mutual
      theorem ProcType.lift_lift : {m n o : ℕ} → {h : m ≤ n} → {h' : n ≤ o} → {p : ProcType «Σ» Γ α β m} → ProcType.lift o h' (ProcType.lift n h p) = ProcType.lift o (Nat.le_trans h h') p
        | 0, n, o, h, h', .leaf v | m + 1, n, o, h, h', .leaf v => by rw [ProcType.lift.leaf, ProcType.lift.leaf, ProcType.lift.leaf]
        | 0, n, o, h, h', .abort | m + 1, n, o, h, h', .abort => by rw [ProcType.lift.abort, ProcType.lift.abort, ProcType.lift.abort]
        | m + 1, n + 1, o + 1, h, h', .branch f => by
          rw [ProcType.lift.branch, ProcType.lift.branch, ProcType.lift.branch]
          congr 1
          ext σ b : 3
          simp [Branch.lift_lift (Nat.add_one_le_add_one_iff.mp h) (Nat.add_one_le_add_one_iff.mp h')]

      theorem Branch.lift_lift {m n o : ℕ} (h : m ≤ n) (h' : n ≤ o) : {b : Branch «Σ» Γ α (ProcType «Σ» Γ α β m)} → Branch.lift o h' (Branch.lift n h b) = Branch.lift o (Nat.le_trans h h') b
        | .recv γ π => by simp_rw [Branch.lift.recv, ProcType.lift_lift (h := h)]
        | .send γ v p => by simp_rw [Branch.lift.send, ProcType.lift_lift (h := h)]
        | .close γ p => by simp_rw [Branch.lift.close, ProcType.lift_lift (h := h)]
        | .sync γ p => by simp_rw [Branch.lift.sync, ProcType.lift_lift (h := h)]
        | .next σ p => by simp_rw [Branch.lift.next, ProcType.lift_lift (h := h)]
    end

    theorem Proc.eq_lift_of_eq : {m n : ℕ} → {h : m ≤ n} → {p p' : ProcType «Σ» Γ α β m} → p = p' → ProcType.lift n h p = ProcType.lift n h p' := by
      rintro _ _ _ _ _ rfl
      rfl

    mutual
      -- injectivity of Proc.lift...dumbass
      theorem ProcType.eq_of_eq_lift : {m n : ℕ} → {h : m ≤ n} → {p p' : ProcType «Σ» Γ α β m} → ProcType.lift n h p = ProcType.lift n h p' → p = p'
        | 0, _, _, .leaf _, .leaf _, eq | _ + 1, _, _, .leaf _, .leaf _, eq => by rw [ProcType.lift.leaf, ProcType.lift.leaf, ← ProcType.leaf.injEq] at eq; cases eq; rfl
        | 0, _, _, .leaf _, .abort, eq | _ + 1, _, _, .leaf _, .abort, eq => by rw [ProcType.lift.leaf, ProcType.lift.abort] at eq; exfalso; exact ProcType.leaf_ne_abort eq
        | 0, _, _, .abort, .leaf _, eq | _ + 1, _, _, .abort, .leaf _, eq => by rw [ProcType.lift.leaf, ProcType.lift.abort] at eq; exfalso; exact Ne.symm ProcType.leaf_ne_abort eq
        | 0, _, _, .abort, .abort, _ | _ + 1, _, _, .abort, .abort, _ => by rfl
        | _ + 1, _, h, .branch _, .leaf _, eq => by
          obtain ⟨_, rfl⟩ := Nat.succ_le_exists_succ h
          rw [ProcType.lift.leaf, ProcType.lift.branch] at eq
          exfalso
          exact Ne.symm ProcType.leaf_ne_branch eq
        | _ + 1, _, h, .leaf _, .branch _, eq => by
          obtain ⟨_, rfl⟩ := Nat.succ_le_exists_succ h
          rw [ProcType.lift.leaf, ProcType.lift.branch] at eq
          exfalso
          exact ProcType.leaf_ne_branch eq
        | _ + 1, _, h, .branch _, .abort, eq => by
          obtain ⟨_, rfl⟩ := Nat.succ_le_exists_succ h
          rw [ProcType.lift.abort, ProcType.lift.branch] at eq
          exfalso
          exact Ne.symm ProcType.abort_ne_branch eq
        | _ + 1, _, h, .abort, .branch _, eq => by
          obtain ⟨_, rfl⟩ := Nat.succ_le_exists_succ h
          rw [ProcType.lift.abort, ProcType.lift.branch] at eq
          exfalso
          exact ProcType.abort_ne_branch eq
        | _ + 1, _, h, .branch f, .branch f', eq => by
          obtain ⟨n, rfl⟩ := Nat.succ_le_exists_succ h
          rw [ProcType.lift.branch, ProcType.lift.branch, ← ProcType.branch.injEq] at eq

          change ?F = ?G at eq
          have ext : ∀ σ, ?F σ = ?G σ := by
            intro σ
            rw [eq]

          rw [← ProcType.branch.injEq]
          simp_rw [Subtype.ext_iff, Set.ext_iff] at ext ⊢
          ext σ b
          specialize ext σ (Branch.lift n (Nat.add_one_le_add_one_iff.mp h) b)
          rwa [Function.Injective.mem_set_image, Function.Injective.mem_set_image] at ext
          all:
            apply Branch.lift.injective

      theorem Branch.lift.injective {m n : ℕ} (h : m ≤ n) : Function.Injective (Branch.lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) n h)
        | .recv γ π, .recv γ' π', eq => by
          rw [Branch.lift.recv, Branch.lift.recv, ← Branch.recv.injEq] at eq
          obtain ⟨rfl, eq⟩ := eq

          change ?F₁ = ?G₁ at eq
          have ext : ∀ v ok, ?F₁ v ok = ?G₁ v ok := λ v ok ↦ by rw [eq]
          replace ext : ∀ v ok, π v ok = π' v ok := λ v ok ↦ ProcType.eq_of_eq_lift (ext v ok)
          obtain rfl : π = π' := by funext v ok; exact ext v ok
          rfl
        | .recv γ π, .send γ' v' p', eq => by
          rw [Branch.lift.recv, Branch.lift.send] at eq
          exfalso
          exact Branch.recv_ne_send eq
        | .recv γ π, .close γ' p', eq => by
          rw [Branch.lift.recv, Branch.lift.close] at eq
          exfalso
          exact Branch.recv_ne_close eq
        | .recv γ π, .sync γ' p', eq => by
          rw [Branch.lift.recv, Branch.lift.sync] at eq
          exfalso
          exact Branch.recv_ne_sync eq
        | .recv γ π, .next σ' p', eq => by
          rw [Branch.lift.recv, Branch.lift.next] at eq
          exfalso
          exact Branch.recv_ne_next eq
        | .send γ v p, .recv γ' π', eq => by
          rw [Branch.lift.send, Branch.lift.recv] at eq
          exfalso
          exact Ne.symm Branch.recv_ne_send eq
        | .send γ v p, .send γ' v' p', eq => by
          rw [Branch.lift.send, Branch.lift.send, ← Branch.send.injEq] at eq
          obtain ⟨rfl, rfl, eq⟩ := eq
          obtain rfl := ProcType.eq_of_eq_lift eq
          rfl
        | .send γ v p, .close γ' p', eq => by
          rw [Branch.lift.send, Branch.lift.close] at eq
          exfalso
          exact Branch.send_ne_close eq
        | .send γ v p, .sync γ' p', eq => by
          rw [Branch.lift.send, Branch.lift.sync] at eq
          exfalso
          exact Branch.send_ne_sync eq
        | .send γ v p, .next σ' p', eq => by
          rw [Branch.lift.send, Branch.lift.next] at eq
          exfalso
          exact Branch.send_ne_next eq
        | .close γ p, .recv γ' π', eq => by
          rw [Branch.lift.close, Branch.lift.recv] at eq
          exfalso
          exact Ne.symm Branch.recv_ne_close eq
        | .close γ p, .send γ' v' p', eq => by
          rw [Branch.lift.close, Branch.lift.send] at eq
          exfalso
          exact Ne.symm Branch.send_ne_close eq
        | .close γ p, .close γ' p', eq => by
          rw [Branch.lift.close, Branch.lift.close, ← Branch.close.injEq] at eq
          obtain ⟨rfl, eq⟩ := eq
          obtain rfl := ProcType.eq_of_eq_lift eq
          rfl
        | .close γ p, .sync γ' p', eq => by
          rw [Branch.lift.close, Branch.lift.sync] at eq
          exfalso
          exact Branch.close_ne_sync eq
        | .close γ p, .next σ' p', eq => by
          rw [Branch.lift.close, Branch.lift.next] at eq
          exfalso
          exact Branch.close_ne_next eq
        | .sync γ p, .recv γ' π', eq => by
          rw [Branch.lift.sync, Branch.lift.recv] at eq
          exfalso
          exact Ne.symm Branch.recv_ne_sync eq
        | .sync γ p, .send γ' v' p', eq => by
          rw [Branch.lift.sync, Branch.lift.send] at eq
          exfalso
          exact Ne.symm Branch.send_ne_sync eq
        | .sync γ p, .close γ' p', eq => by
          rw [Branch.lift.sync, Branch.lift.close] at eq
          exfalso
          exact Ne.symm Branch.close_ne_sync eq
        | .sync γ p, .sync γ' p', eq => by
          rw [Branch.lift.sync, Branch.lift.sync, ← Branch.sync.injEq] at eq
          obtain ⟨rfl, eq⟩ := eq
          obtain rfl := ProcType.eq_of_eq_lift eq
          rfl
        | .sync γ p, .next σ' p', eq => by
          rw [Branch.lift.sync, Branch.lift.next] at eq
          exfalso
          exact Branch.sync_ne_next eq
        | .next σ p, .recv γ' π', eq => by
          rw [Branch.lift.next, Branch.lift.recv] at eq
          exfalso
          exact Ne.symm Branch.recv_ne_next eq
        | .next σ p, .send γ' v' p', eq => by
          rw [Branch.lift.next, Branch.lift.send] at eq
          exfalso
          exact Ne.symm Branch.send_ne_next eq
        | .next σ p, .close γ' p', eq => by
          rw [Branch.lift.next, Branch.lift.close] at eq
          exfalso
          exact Ne.symm Branch.close_ne_next eq
        | .next σ p, .sync γ' p', eq => by
          rw [Branch.lift.next, Branch.lift.sync] at eq
          exfalso
          exact Ne.symm Branch.sync_ne_next eq
        | .next σ p, .next σ' p', eq => by
          rw [Branch.lift.next, Branch.lift.next, ← Branch.next.injEq] at eq
          obtain ⟨rfl, eq⟩ := eq
          obtain rfl := ProcType.eq_of_eq_lift eq
          rfl
    end

    theorem Proc.eq_iff_eq_lift : {m n : ℕ} → {h : m ≤ n} → {p p' : ProcType «Σ» Γ α β m} → p = p' ↔ ProcType.lift n h p = ProcType.lift n h p' where
      mp := Proc.eq_lift_of_eq
      mpr := ProcType.eq_of_eq_lift

    theorem Proc.lift_congr {m n o : ℕ} (h : n = o) {h' : m ≤ n} {p : ProcType «Σ» Γ α β m} : ProcType.lift n h' p = h ▸ ProcType.lift o (h ▸ h') p := by
      cases h
      rfl

    mutual
      theorem ProcType.lift_of_eq : (m : ℕ) → {p : ProcType «Σ» Γ α β m} → ProcType.lift m (Nat.le_refl m) p = p
        | 0, .leaf v | _ + 1, .leaf v => by rw [ProcType.lift.leaf]
        | 0, .abort | _ + 1, .abort => by rw [ProcType.lift.abort]
        | m + 1, .branch f => by rw [ProcType.lift.branch]; simp [Branch.lift_of_eq m]

      theorem Branch.lift_of_eq (m : ℕ) : {b : Branch «Σ» Γ α (ProcType «Σ» Γ α β m)} → Branch.lift m (Nat.le_refl m) b = b
        | .recv γ π => by simp [Branch.lift.recv, ProcType.lift_of_eq m]
        | .send γ v p => by simp [Branch.lift.send, ProcType.lift_of_eq m]
        | .close γ p => by simp [Branch.lift.close, ProcType.lift_of_eq m]
        | .sync γ p => by simp [Branch.lift.sync, ProcType.lift_of_eq m]
        | .next σ p => by simp [Branch.lift.next, ProcType.lift_of_eq m]
    end
  end

  def Procω.equiv : Procω «Σ» Γ α β → Procω «Σ» Γ α β → Prop
    | ⟨m, p⟩, ⟨n, p'⟩ =>
      if h : m = n then
        dist p (h ▸ p') = 0
      else if h : m > n then
        dist p (ProcType.lift m (Nat.le_of_lt h) p') = 0
      else
        dist (ProcType.lift n (Nat.le_of_not_gt h) p) p' = 0

  -- omit [DecidableEq α] [DecidableEq β] [DecidableEq Γ] [DecidableEq «Σ»] in
  section
    theorem Procω.equiv_refl (p : Procω «Σ» Γ α β) : Procω.equiv p p := by
      obtain ⟨m, p⟩ := p
      simp [Procω.equiv, dist_self]

    theorem Procω.equiv_symm (p p' : Procω «Σ» Γ α β) (eqv : Procω.equiv p p') : Procω.equiv p' p := by
      rcases p, p' with ⟨⟨m, p⟩, ⟨n, p'⟩⟩
      unfold equiv at eqv ⊢
      dsimp at eqv ⊢
      split_ifs at eqv with h₁ h₂
      . cases h₁
        rwa [dite_cond_eq_true (eq_true (rfl : m = m)), dist_comm]
      . rwa [dite_cond_eq_false (eq_false (Ne.symm h₁)), dite_cond_eq_false (eq_false (Lean.Grind.Preorder.not_gt_of_lt h₂)), dist_comm]
      . rwa [dite_cond_eq_false (eq_false (Ne.symm h₁)), dite_cond_eq_true (eq_true _), dist_comm]
        · apply Nat.gt_of_not_le
          rw [Nat.le_iff_lt_or_eq, not_or]
          exact ⟨h₂, Ne.symm h₁⟩

    lemma jsp₄ {m n o : ℕ} {h : m = n} {h' : n = o} {p : ProcType «Σ» Γ α β m} : h' ▸ h ▸ p = Eq.trans h h' ▸ p := by
      cases h
      cases h'
      rfl

  theorem Procω.equiv_trans (x y z : Procω «Σ» Γ α β) (eqv_x_y : x.equiv y) (eqv_y_z : y.equiv z) : x.equiv z := by
    rcases x, y, z with ⟨⟨m, px⟩, ⟨n, py⟩, ⟨o, pz⟩⟩
    unfold equiv at eqv_x_y eqv_y_z ⊢
    dsimp at eqv_x_y eqv_y_z ⊢

    split_ifs at eqv_x_y eqv_y_z with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
      <;> (apply eq_of_dist_eq_zero at eqv_x_y
           apply eq_of_dist_eq_zero at eqv_y_z
           subst_eqs)
    · rw [dif_pos rfl, dist_self]
    · rw [dif_neg h₂, dif_pos h₃, dist_self]
    · rw [dif_neg h₂, dif_neg h₃, dist_self]
    · rw [dif_neg h₁, dif_pos h₄, dist_self]
    · have : m > o := Nat.lt_trans h₆ h₄
      have : m ≠ o := Nat.ne_of_gt ‹m > o›

      rw [dif_neg ‹m ≠ o›, dif_pos ‹m > o›, ProcType.lift_lift, dist_self]
    · by_cases h₂ : m = o
      · subst m
        rw [dif_pos rfl, dist_self]
      · by_cases h₃ : m > o
        · rw [dif_neg h₂, dif_pos h₃, ProcType.lift_lift, dist_self]
        · rw [dif_neg h₂, dif_neg h₃, ProcType.lift_lift, dist_self]
    · rw [dif_neg h₁, dif_neg h₄, dist_self]
    · by_cases h₂ : m = o
      · subst m
        rw [← Proc.eq_iff_eq_lift] at eqv_y_z
        cases eqv_y_z
        rw [dif_pos rfl, dist_self]
      · by_cases h₃ : m > o
        · have : m ⊔ o ≤ n := by rwa [Nat.max_def, if_neg (Nat.not_le_of_gt h₃), ← Nat.not_gt_eq]
          have : m ≤ m ⊔ o := by simp
          have : o ≤ m ⊔ o := by simp
          have : m ⊔ o = m := by rw [Nat.max_def, if_neg (Nat.not_le_of_gt h₃)]
          rw [← ProcType.lift_lift (h := ‹m ≤ m ⊔ o›) (h' := ‹m ⊔ o ≤ n›), ← ProcType.lift_lift (h := ‹o ≤ m ⊔ o›) (h' := ‹m ⊔ o ≤ n›), ← Proc.eq_iff_eq_lift] at eqv_y_z
          rw [dif_neg h₂, dif_pos h₃, Proc.lift_congr (Eq.symm ‹m ⊔ o = m›), ← eqv_y_z, Proc.lift_congr ‹m ⊔ o = m›, ProcType.lift_of_eq, jsp₄, dist_self]
        · have : m ⊔ o ≤ n := by rw [Nat.max_def, if_pos (Nat.le_of_not_gt h₃)]; exact Nat.le_of_lt h₈
          have : m ≤ m ⊔ o := by simp
          have : o ≤ m ⊔ o := by simp
          have : m ⊔ o = o := by rw [Nat.max_def, if_pos (Nat.le_of_not_gt h₃)]
          rw [← ProcType.lift_lift (h := ‹m ≤ m ⊔ o›) (h' := ‹m ⊔ o ≤ n›), ← ProcType.lift_lift (h := ‹o ≤ m ⊔ o›) (h' := ‹m ⊔ o ≤ n›), ← Proc.eq_iff_eq_lift] at eqv_y_z
          rw [dif_neg h₂, dif_neg h₃, Proc.lift_congr (Eq.symm ‹m ⊔ o = o›), eqv_y_z, Proc.lift_congr ‹m ⊔ o = o›, ProcType.lift_of_eq, jsp₄, dist_self]
    · apply Nat.le_of_not_gt at h₄
      replace h₄ := Nat.lt_iff_le_and_ne.mpr ⟨h₄, h₁⟩
      apply Nat.le_of_not_gt at h₈
      replace h₈ := Nat.lt_iff_le_and_ne.mpr ⟨h₈, h₇⟩

      have : m < o := Nat.lt_trans h₄ h₈
      have : m ≠ o := Nat.ne_of_lt ‹m < o›
      have : ¬ m > o := Nat.not_lt_of_gt ‹m < o›

      rw [dif_neg ‹m ≠ o›, dif_neg ‹¬ m > o›, ProcType.lift_lift, dist_self]
  end

  variable («Σ» Γ α β)

  instance Procω.setoid : Setoid (Procω «Σ» Γ α β) where
    r := Procω.equiv
    iseqv := by
      refine { refl := ?_, symm := ?_, trans := ?_ }
      · exact Procω.equiv_refl
      · apply Procω.equiv_symm
      · apply Procω.equiv_trans

  abbrev Procω' := Quotient (Procω.setoid «Σ» Γ α β)

  variable {«Σ» Γ α β} -- [CompleteMetricSpace γ] [CompleteMetricSpace δ]

  --  noncomputable instance instMetricSpaceProcω : MetricSpace (Procω «Σ» Γ α β) := inferInstanceAs (MetricSpace (Quotient _))

  --! ## Functor

  def Branch.map (f : β → γ) : Branch «Σ» Γ α β → Branch «Σ» Γ α γ
    | .recv γ π => .recv γ (λ v ok ↦ f (π v ok))
    | .send γ v p => .send γ v (f p)
    | .close γ p => .close γ (f p)
    | .sync γ p => .sync γ (f p)
    | .next σ p => .next σ (f p)

  def ProcType.map (f : β → γ) : {n : ℕ} → ProcType «Σ» Γ α β n → ProcType «Σ» Γ α γ n
    | 0, .leaf v | n + 1, .leaf v => .leaf (f v)
    | 0, .abort | n + 1, .abort => .abort
    | n + 1, .branch g => .branch λ σ ↦
      let ⟨s, closed_s⟩ := g σ
      ⟨Branch.map (ProcType.map f) '' s, by
        rwa [← Topology.IsClosedEmbedding.isClosed_iff_image_isClosed]
        apply Isometry.isClosedEmbedding
        -- yes, mapping is an isometry
        admit⟩

  -- omit [DecidableEq α] [DecidableEq β] [DecidableEq Γ] [DecidableEq «Σ»] in
  section
    theorem ProcType.map.abort {f : β → γ} : {m : ℕ} → ProcType.map f (ProcType.abort («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (n := m)) = ProcType.abort
      | 0 => by unfold ProcType.map; rfl
      | _ + 1 => by unfold ProcType.map; rfl

    theorem ProcType.map.leaf {f : β → γ} {v : β} : {m : ℕ} → ProcType.map f (ProcType.leaf («Σ» := «Σ») (Γ := Γ) (α := α) (n := m) v) = ProcType.leaf (f v)
      | 0 => by unfold ProcType.map; rfl
      | _ + 1 => by unfold ProcType.map; rfl

    alias ProcType.map.branch := ProcType.map.eq_5
    -- theorem ProcType.map.branch {f : β → γ} : {n : ℕ} → {g : «Σ» → Set (Branch «Σ» Γ α (ProcType «Σ» Γ α β n))} → ProcType.map f (ProcType.branch g) = ProcType.branch (λ σ ↦ Branch.map f '' g σ)
    --   | _, _ => by unfold ProcType.map; rfl

    omit [DecidableEq α] [DecidableEq β] [DecidableEq Γ] [DecidableEq «Σ»] [DecidableEq γ] in
    section
      theorem Branch.map.recv {f : β → γ} {γ : Γ} {π : α → Bool → β} : Branch.map f (Branch.recv («Σ» := «Σ») (α := α) γ π) = Branch.recv γ (λ v ok ↦ f (π v ok)) := by
        unfold map; rfl

      theorem Branch.map.send {f : β → γ} {γ : Γ} {v : α} {p : β} : Branch.map f (Branch.send («Σ» := «Σ») (α := α) γ v p) = Branch.send γ v (f p) := by
        unfold map; rfl

      theorem Branch.map.close {f : β → γ} {γ : Γ} {p : β} : Branch.map f (Branch.close («Σ» := «Σ») (α := α) γ p) = Branch.close γ (f p) := by
        unfold map; rfl

      theorem Branch.map.sync {f : β → γ} {γ : Γ} {p : β} : Branch.map f (Branch.sync («Σ» := «Σ») (α := α) γ p) = Branch.sync γ (f p) := by
        unfold map; rfl

      theorem Branch.map.next {f : β → γ} {σ : «Σ»} {p : β} : Branch.map f (Branch.next (Γ := Γ) (α := α) σ p) = Branch.next σ (f p) := by
        unfold map; rfl
    end

    mutual
      theorem ProcType.map_comp {g : β → γ} {f : γ → δ} : {m : ℕ} → {p : ProcType «Σ» Γ α β m} → ProcType.map f (ProcType.map g p) = ProcType.map (f ∘ g) p
        | 0, .leaf v | _ + 1, .leaf v => by rw [ProcType.map.leaf, ProcType.map.leaf, ProcType.map.leaf]; rfl
        | 0, .abort | _ + 1, .abort => by rw [ProcType.map.abort, ProcType.map.abort, ProcType.map.abort]
        | m + 1, .branch h => by
          rw [ProcType.map.branch, ProcType.map.branch, ProcType.map.branch]
          congr 1
          ext σ b : 3
          simp [Branch.map_comp (m := m)]

      theorem Branch.map_comp {g : β → γ} {f : γ → δ} {m : ℕ} : {p : Branch «Σ» Γ α (ProcType «Σ» Γ α β m)} → Branch.map f (Branch.map g p) = Branch.map (f ∘ g) p
        | .recv γ π => by simp_rw [Branch.map.recv, ProcType.map_comp (m := m)]
        | .send γ v p => by rw [Branch.map.send, Branch.map.send, Branch.map.send, ProcType.map_comp]
        | .close γ p => by rw [Branch.map.close, Branch.map.close, Branch.map.close, ProcType.map_comp]
        | .sync γ p => by rw [Branch.map.sync, Branch.map.sync, Branch.map.sync, ProcType.map_comp]
        | .next σ p => by rw [Branch.map.next, Branch.map.next, Branch.map.next, ProcType.map_comp]
    end

    -- theorem Proc.map.heq_of_heq {f : β → γ} {m n : ℕ} {p : Proc «Σ» Γ α β m} {p' : Proc «Σ» Γ α β n} (h : p ≍ p') : Proc.map f p ≍ Proc.map f p' := by
    --   -- NOTE: cannot be proven within Lean

    @[push_cast]
    theorem ProcType.map.push_cast {f : β → γ} {m n : ℕ} {p : ProcType «Σ» Γ α β m} {h : m = n} : h ▸ ProcType.map f p = ProcType.map f (h ▸ p) := by
      cases h
      rfl

    mutual
      theorem ProcType.lift_map {f : β → γ} : {m n : ℕ} → (h : m ≤ n) → {p : ProcType «Σ» Γ α β m} → ProcType.lift n h (ProcType.map f p) = ProcType.map f (ProcType.lift n h p)
        | 0, 0, _, .leaf v | 0, _ + 1, _, .leaf v | _ + 1, _ + 1, _, .leaf v => by unfold ProcType.lift ProcType.map; rfl
        | 0, 0, _, .abort | 0, _ + 1, _, .abort | _ + 1, _ + 1, _, .abort => by unfold ProcType.lift ProcType.map; rfl
        | m + 1, n + 1, h, .branch g => by
          rw [ProcType.map.branch, ProcType.lift.branch, ProcType.lift.branch, ProcType.map.branch]
          congr 1
          ext σ b : 3
          simp [Branch.lift_map (Nat.add_one_le_add_one_iff.mp h)]

      theorem Branch.lift_map {f : β → γ} {m n : ℕ} (h : m ≤ n) : {b : Branch «Σ» Γ α (ProcType «Σ» Γ α β m)} → Branch.lift n h (Branch.map f b) = Branch.map f (Branch.lift n h b)
        | .recv γ π => by
          rw [Branch.map.recv, Branch.lift.recv, Branch.lift.recv, Branch.map.recv]
          congr 1
          ext v ok : 2
          rw [ProcType.lift_map h]
        | .send γ v p => by
          rw [Branch.map.send, Branch.lift.send, Branch.lift.send, Branch.map.send, ProcType.lift_map h]
        | .close γ p => by
          rw [Branch.map.close, Branch.lift.close, Branch.lift.close, Branch.map.close, ProcType.lift_map h]
        | .sync γ p => by
          rw [Branch.map.sync, Branch.lift.sync, Branch.lift.sync, Branch.map.sync, ProcType.lift_map h]
        | .next σ p => by
          rw [Branch.map.next, Branch.lift.next, Branch.lift.next, Branch.map.next, ProcType.lift_map h]
    end
  end

  --! ## Definition of `P`

  variable («Σ» Γ α β)
  abbrev P := UniformSpace.Completion (Procω «Σ» Γ α β)
  variable {«Σ» Γ α β}
  noncomputable instance : CompleteMetricSpace (P «Σ» Γ α β) where
    __ := inferInstanceAs (MetricSpace (UniformSpace.Completion _))
    __ := inferInstanceAs (CompleteSpace (UniformSpace.Completion _))

  private noncomputable def Sum.discreteMetric : MetricSpace (β ⊕ PUnit ⊕ («Σ» → { s : Set (Branch «Σ» Γ α (P «Σ» Γ α β)) // IsClosed s })) where
    dist := Proc.dist_succ
    dist_self := by admit
    dist_comm := by admit
    dist_triangle := by admit
    eq_of_dist_eq_zero := by admit

  def Procω.inj : Procω «Σ» Γ α β → β ⊕ PUnit ⊕ («Σ» → { s : Set (Branch «Σ» Γ α (Procω «Σ» Γ α β)) // IsClosed s })
    | ⟨0, .leaf x⟩ | ⟨_ + 1, .leaf x⟩ => .inl x
    | ⟨_, .abort⟩ => .inr (.inl .unit)
    | ⟨_ + 1, .branch f⟩ => .inr (.inr λ σ ↦ ⟨Branch.map sorry '' (f σ).val, by admit⟩)

  def Procω.toP : Procω «Σ» Γ α β → P «Σ» Γ α β := sorry
  def P.toProcω : P «Σ» Γ α β → Procω «Σ» Γ α β := sorry

  -- noncomputable def Procω.approx : Procω «Σ» Γ α β ≃ ℕ × (β ⊕ PUnit ⊕ («Σ» → { s : Set (Branch «Σ» Γ α (Procω «Σ» Γ α β)) // IsClosed s })) where
  --   toFun
  --     | ⟨0, .leaf x⟩ => ⟨0, .inl x⟩
  --     | ⟨0, .abort⟩ => ⟨0, .inr (.inl .unit)⟩
  --     | ⟨n + 1, .leaf x⟩ => ⟨n + 1, .inl x⟩
  --     | ⟨n + 1, .abort⟩ => ⟨n + 1, .inr (.inl .unit)⟩
  --     | ⟨n + 1, .branch f⟩ => ⟨n + 1, .inr (.inr λ σ ↦ ⟨sorry, by admit⟩)⟩
  --   invFun := sorry
  --   left_inv := sorry
  --   right_inv := sorry

  -- TODO: show that `P` is indeed a solution to our domain equation
  attribute [local instance] Sum.discreteMetric in
  noncomputable def P_is_solution : P «Σ» Γ α β ≃ᵢ (β ⊕ PUnit ⊕ («Σ» → { s : Set (Branch «Σ» Γ α (P «Σ» Γ α β)) // IsClosed s })) where
    toFun := λ pn ↦ pn.lift (λ ⟨f, _⟩ ↦ (lim f).inj) (λ f g ↦ by admit)
    invFun := sorry
    left_inv := by admit
    right_inv := by admit
    isometry_toFun := by admit

  mutual
    -- TODO: transfer into the sum, then back into `P`
    def P.recOn
      {motive₁ : P «Σ» Γ α β → Sort _} {motive₂ : Branch «Σ» Γ α (P «Σ» Γ α β) → Sort _}
      (leaf : ∀ (v : β) (n : ℕ), motive₁ ⟦CauchyFilter.pureCauchy ⟨n, ProcType.leaf v⟩⟧)
      (abort : ∀ (n : ℕ), motive₁ ⟦CauchyFilter.pureCauchy ⟨n, ProcType.abort⟩⟧)
      (p : P «Σ» Γ α β) :
        motive₁ p :=
      p.lift _ _
  end

  --! ## Applicative functor

  --! ## Monad

  --! ## Other operations

  private lemma jsp (m n : ℕ) : (m + 1).add n = m + (n + 1) := by rw [Nat.add_eq]; omega

  mutual
    variable (zero : Γ → α)

    def ProcType.parallel : {m n : ℕ} → ProcType «Σ» Γ α β m → ProcType «Σ» Γ α γ n → ProcType «Σ» Γ α (β × γ) (m + n)
      | 0, n, .leaf v, p' => (Nat.zero_add n).symm ▸ ProcType.map (λ v' : γ ↦ Prod.mk v v') p'
      | m, 0, p, .leaf v' => ProcType.map (λ v : β ↦ Prod.mk v v') p
      | 0, n, .abort, p' => .abort
      | m, 0, p, .abort => .abort
      | m + 1, n, .leaf v, p' => ProcType.map (λ v' : γ ↦ Prod.mk v v') (ProcType.lift (m + 1 + n) (by simp) p')
      | m, n + 1, p, .leaf v' => ProcType.map (λ v : β ↦ Prod.mk v v') (ProcType.lift (m + (n + 1)) (by simp) p)
      | m + 1, n, .abort, p' => .abort
      | m, n + 1, p, .abort => .abort
      | m + 1, n + 1, .branch f, .branch f' => .branch λ σ ↦ {
        val :=
          -- Interleavings
            {jsp m n ▸ Branch.lparallel x (.branch f') | x ∈ (f σ).val}
          ∪ {Branch.rparallel (.branch f) y | y ∈ (f' σ).val}
          -- Synchronizations
          ∪ {p | ∃ v γ p' π', .send γ v p' ∈ (f σ).val ∧ .recv γ π' ∈ (f' σ).val ∧ p = .sync γ (ProcType.lift ((m + 1) + n) (by simp) (ProcType.parallel p' (π' v true)))}
          ∪ {p | ∃ v γ p' π', .send γ v p' ∈ (f' σ).val ∧ .recv γ π' ∈ (f σ).val ∧ p = .sync γ (ProcType.lift ((m + 1) + n) (by simp) (ProcType.parallel (π' v true) p'))}
          ∪ {p | ∃ v γ p' p'', .send γ v p' ∈ (f σ).val ∧ .close γ p'' ∈ (f' σ).val ∧ p = .next σ .abort}
          ∪ {p | ∃ v γ p' p'', .send γ v p' ∈ (f' σ).val ∧ .close γ p'' ∈ (f σ).val ∧ p = .next σ .abort}
          ∪ {p | ∃ γ π' p', .recv γ π' ∈ (f σ).val ∧ .close γ p' ∈ (f' σ).val ∧ p = .close γ (ProcType.lift ((m + 1) + n) (by simp) (ProcType.parallel (π' (zero γ) false) p'))}
          ∪ {p | ∃ γ π' p', .recv γ π' ∈ (f' σ).val ∧ .close γ p' ∈ (f σ).val ∧ p = .close γ (ProcType.lift ((m + 1) + n) (by simp) (ProcType.parallel p' (π' (zero γ) false)))}
        property := by
          have f_σ_closed := (f σ).property
          have f'_σ_closed := (f' σ).property
          admit
      }

    def Branch.lparallel {m n : ℕ} : Branch «Σ» Γ α (ProcType «Σ» Γ α β n) → ProcType «Σ» Γ α γ m → Branch «Σ» Γ α (ProcType «Σ» Γ α (β × γ) (n + m))
      | .recv γ π, p' => .recv γ (λ v ok ↦ ProcType.parallel (π v ok) p')
      | .send γ v p, p' => .send γ v (ProcType.parallel p p')
      | .close γ p, p' => .close γ (ProcType.parallel p p')
      | .sync γ p, p' => .sync γ (ProcType.parallel p p')
      | .next σ p, p' => .next σ (ProcType.parallel p p')

    def Branch.rparallel {m n : ℕ} : ProcType «Σ» Γ α β m → Branch «Σ» Γ α (ProcType «Σ» Γ α γ n) → Branch «Σ» Γ α (ProcType «Σ» Γ α (β × γ) (m + n))
      | p, .recv γ π' => .recv γ (λ v ok ↦ ProcType.parallel p (π' v ok))
      | p, .send γ v p' => .send γ v (ProcType.parallel p p')
      | p, .close γ p' => .close γ (ProcType.parallel p p')
      | p, .sync γ p' => .sync γ (ProcType.parallel p p')
      | p, .next σ p' => .next σ (ProcType.parallel p p')
  end

  abbrev Prod.assoc : (α × β) × γ → α × β × γ
    | ⟨⟨x, y⟩, z⟩ => ⟨x, y, z⟩

  -- omit [DecidableEq α] [DecidableEq β] [DecidableEq Γ] [DecidableEq «Σ»] in
  section
    theorem Prod.assoc_def {x : α} {y : β} {z : γ} : Prod.assoc ((x, y), z) = (x, y, z) := by
      rfl

    lemma jsp₂ {m n : ℕ} {h : m = n} {p : ProcType «Σ» Γ α β m} : (h ▸ p) ≍ p := by
      cases h
      rfl

    @[push_cast]
    lemma ProcType.leaf.push_cast {m n : ℕ} {h : m = n} {v : β} : h ▸ ProcType.leaf («Σ» := «Σ») (Γ := Γ) (α := α) (n := m) v = ProcType.leaf v := by
      cases h
      rfl

    @[push_cast]
    lemma ProcType.abort.push_cast {m n : ℕ} {h : m = n} : h ▸ ProcType.abort («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (n := m) = ProcType.abort := by
      cases h
      rfl

    @[push_cast]
    lemma ProcType.branch.push_cast {m n : ℕ} {h : m + 1 = n + 1} {g : «Σ» → Set (Branch «Σ» Γ α (ProcType «Σ» Γ α β m))} :
        h ▸ ProcType.branch g = ProcType.branch λ σ ↦ (Nat.succ.injEq _ _ ▸ h) ▸ g σ := by
      cases h
      rfl
  end

  -- omit [DecidableEq α] [DecidableEq β] [DecidableEq Γ] [DecidableEq «Σ»] in
  section
    variable (zero : Γ → α)

    theorem ProcType.parallel_abort_p_eq : {m n : ℕ} → {p : ProcType «Σ» Γ α β n} → ProcType.parallel zero (ProcType.abort (n := m) (β := γ)) p = .abort
      | 0, 0, .leaf v => by unfold parallel map; rfl
      | 0, n + 1, .leaf v => by unfold parallel; rfl
      | 0, 0, .abort | 0, n + 1, .abort => by unfold parallel; rfl
      | 0, n + 1, .branch f => by unfold parallel; rfl
      | m + 1, 0, .leaf v => by unfold parallel map; rfl
      | m + 1, n + 1, .leaf v => by unfold parallel lift map; rfl
      | m + 1, 0, .abort => by unfold parallel; rfl
      | m + 1, n + 1, .abort => by unfold parallel; rfl
      | m + 1, n + 1, .branch f => by unfold parallel; rfl

    theorem ProcType.parallel_p_abort_eq : {m n : ℕ} → {p : ProcType «Σ» Γ α β n} → ProcType.parallel zero p (ProcType.abort (n := m) (β := γ)) = .abort
      | 0, 0, .leaf v => by unfold parallel map; rfl
      | 0, n + 1, .leaf v => by unfold parallel; rfl
      | 0, 0, .abort | 0, n + 1, .abort => by unfold parallel; rfl
      | 0, n + 1, .branch f => by unfold parallel; rfl
      | m + 1, 0, .leaf v => by
        unfold parallel map
        apply eq_of_heq
        have h : m + 1 = 0 + (m + 1) := by simp +arith
        erw [eqRec_heq_iff_heq, ← h]
      | m + 1, n + 1, .leaf v => by unfold parallel lift map; rfl
      | m + 1, 0, .abort | m + 1, n + 1, .abort => by unfold parallel; rfl
      | m + 1, n + 1, .branch f => by unfold parallel; rfl

    theorem ProcType.parallel_leaf_p_eq {v : β} : {m n : ℕ} → {p : ProcType «Σ» Γ α γ n} →
        ProcType.parallel zero (ProcType.leaf (n := m) v) p = ProcType.lift (m + n) (by simp) (ProcType.map (λ v' ↦ (v, v')) p)
      | 0, 0, .leaf v | m + 1, 0, .leaf v | m + 1, n + 1, .leaf v => by unfold parallel lift map; rfl
      | 0, n + 1, .leaf v => by unfold parallel map lift; push_cast; rfl
      | 0, 0, .abort | m + 1, 0, .abort | m + 1, n + 1, .abort => by unfold parallel lift map; rfl
      | 0, n + 1, .abort => by unfold parallel map lift; push_cast; rfl
      | 0, n + 1, .branch f => by
        unfold parallel
        push_cast
        rw [ProcType.lift_map, ProcType.lift_congr (Nat.zero_add _), ProcType.lift_of_eq (n + 1)]
      | m + 1, n + 1, .branch f => by unfold parallel; rw [ProcType.lift_map]

    theorem ProcType.parallel_p_leaf_eq {v : γ} : {m n : ℕ} → {p : ProcType «Σ» Γ α β m} →
        ProcType.parallel zero p (ProcType.leaf (n := n) v) = ProcType.lift (m + n) (by simp) (ProcType.map (λ v' ↦ (v', v)) p)
      | 0, 0, .leaf v | m + 1, 0, .leaf v | m + 1, n + 1, .leaf v => by unfold parallel lift map; rfl
      | 0, n + 1, .leaf v => by unfold parallel map lift; push_cast; rfl
      | 0, 0, .abort | m + 1, 0, .abort | m + 1, n + 1, .abort => by unfold parallel lift map; rfl
      | 0, n + 1, .abort => by unfold parallel map lift; rfl
      | m + 1, 0, .branch f => by
        unfold parallel
        rw [ProcType.lift_map, ProcType.lift_congr (Nat.add_zero _), ProcType.lift_of_eq (m + 1)]
      | m + 1, n + 1, .branch f => by unfold parallel; rw [ProcType.lift_map]

    -- set_option trace.Meta.isDefEq true in
    set_option maxHeartbeats 600000 in
    mutual
      theorem ProcType.parallel_assoc : {m n o : ℕ} → {p : ProcType «Σ» Γ α β m} → {q : ProcType «Σ» Γ α β n} → {r : ProcType «Σ» Γ α β o} →
          ProcType.parallel zero p (ProcType.parallel zero q r) ≍ ProcType.map Prod.assoc (ProcType.parallel zero (ProcType.parallel zero p q) r)
        | 0, 0, o, .leaf vp, .leaf vq, r | 0, n + 1, o, .leaf vp, .leaf vq, r
        | m + 1, n + 1, o, .leaf vp, .leaf vq, r | m + 1, 0, o, .leaf vp, .leaf vq, r => by
          rw [ProcType.parallel_leaf_p_eq, ProcType.parallel_leaf_p_eq, ProcType.parallel_leaf_p_eq, ProcType.map.leaf, ProcType.lift.leaf, ProcType.parallel_leaf_p_eq,
              ProcType.lift_map, ProcType.lift_lift, ProcType.lift_map, ProcType.lift_map, ProcType.map_comp, ProcType.map_comp, Function.comp_def, Function.comp_def]
          congr 1
          · simp +arith
          · have h : ∀ ⦃x y⦄, x + (y + o) = x + y + o := by simp +arith
            rw [ProcType.lift_congr (@h _ _), eqRec_heq_iff_heq]
        | 0, n + 1, 0, .leaf vp, .branch fq, .leaf vr
        | 0, n + 1, o + 1, .leaf vp, .branch fq, .leaf vr
        | m + 1, n + 1, 0, .leaf vp, .branch fq, .leaf vr
        | m + 1, n + 1, o + 1, .leaf vp, .branch fq, .leaf vr => by
          have h : ∀ ⦃x y⦄, y + (n + 1 + x) = y + (n + 1) + x := by simp +arith
          rw [ProcType.parallel_leaf_p_eq, ProcType.parallel_leaf_p_eq, ProcType.lift_map, ProcType.lift_map, ProcType.parallel_p_leaf_eq, ProcType.lift_lift, ProcType.lift_map,
              ProcType.map_comp, ProcType.parallel_p_leaf_eq, ProcType.map_comp, ProcType.lift_map, ProcType.map_comp, ProcType.lift_lift, Function.comp_def, Function.comp_def,
              ProcType.lift_congr (@h _ _), Function.comp_def]
          -- NOTE: some alternatives need it
          try rw [← ProcType.map.push_cast, eqRec_heq_iff_heq]
        | 0, n + 1, o, .leaf vp, .branch fq, .abort
        | m + 1, n + 1, o, .leaf vp, .branch fq, .abort
        | m + 1, 0, o, .branch fp, .leaf vq, .abort
        | m + 1, n + 1, o, .branch fp, .leaf vq, .abort
        | m + 1, n + 1, o, .branch fp, .branch fq, .abort => by
          have h : ∀ ⦃x y z : ℕ⦄, y + (z + x) = y + z + x := by simp +arith
          rw [ProcType.parallel_p_abort_eq, ProcType.parallel_p_abort_eq, ProcType.parallel_p_abort_eq, ProcType.map.abort, h]
        | m + 1, 0, 0, .branch fp, .leaf vq, .leaf vr
        | m + 1, 0, o + 1, .branch fp, .leaf vq, .leaf vr
        | m + 1, n + 1, 0, .branch fp, .leaf vq, .leaf vr
        | m + 1, n + 1, o + 1, .branch fp, .leaf vq, .leaf vr => by
          have h : ∀ ⦃x y z : ℕ⦄, z + (y + x) = z + y + x := by simp +arith
          rw [ProcType.parallel_p_leaf_eq, ProcType.parallel_p_leaf_eq, ProcType.parallel_p_leaf_eq, ProcType.lift_map, ProcType.lift_map, ProcType.lift_lift, ProcType.lift_map,
              ProcType.map_comp, ProcType.map_comp, ProcType.lift.leaf, ProcType.map.leaf, ProcType.parallel_p_leaf_eq, ProcType.lift_map, ProcType.lift_congr (@h _ _ _)]
          -- NOTE: some alternatives need it
          try rw [← ProcType.map.push_cast, eqRec_heq_iff_heq]
          rfl
        | 0, 0, o, .leaf vp, .abort, r | 0, n + 1, o, .leaf vp, .abort, r
        | m + 1, 0, o, .leaf vp, .abort, r | m + 1, n + 1, o, .leaf vp, .abort, r
        | m + 1, 0, o, .branch fp, .abort, r | m + 1, n + 1, o, .branch fp, .abort, r => by
          have h : ∀ ⦃x y⦄, y + (x + o) = y + x + o := by simp +arith
          rw [ProcType.parallel_abort_p_eq, ProcType.parallel_p_abort_eq, ProcType.parallel_p_abort_eq, ProcType.parallel_abort_p_eq, ProcType.map.abort, h]
        | 0, n, o, .abort, q, r | m + 1, n, o, .abort, q, r => by
          have h : ∀ ⦃x⦄, x + (n + o) = x + n + o := by simp +arith
          rw [ProcType.parallel_abort_p_eq, ProcType.parallel_abort_p_eq, ProcType.parallel_abort_p_eq, ProcType.map.abort, h]
        | 0, n + 1, o + 1, .leaf vp, .branch fq, .branch fr => by
          have h : 0 + (n + 1) = n + 1 := Nat.zero_add _
          have h₂ : 0 + (n + 1 + (o + 1)) = 0 + (n + 1) + o + 1 := by simp +arith
          rw [ProcType.parallel_leaf_p_eq, ProcType.parallel_leaf_p_eq, ProcType.lift_map, ProcType.lift_map, ProcType.lift_congr h, ProcType.lift.branch,
              ProcType.lift_congr h₂]
          admit
        | m + 1, n + 1, o + 1, .leaf vp, .branch fq, .branch fr => by
          have h : m + 1 + (n + 1) = m + 1 + n + 1 := by simp +arith
          rw [ProcType.parallel_leaf_p_eq, ProcType.parallel_leaf_p_eq, ProcType.lift_map, ProcType.lift_map, ProcType.lift_congr h, ProcType.lift.branch]
          push_cast
          rw [ProcType.map.branch, ← ProcType.lift_map]
          unfold parallel

          have h' : m + 1 + (n + 1 + (o + 1)) = m + 1 + n + 1 + o + 1 := by simp +arith
          rw [ProcType.map.branch, ProcType.map.branch, ProcType.lift_congr h', ProcType.lift.branch, ProcType.branch.push_cast]
          congr 1
          · simp +arith
          · refine Function.hfunext rfl (λ σ σ' σ_eq ↦ ?_)
            cases σ_eq
            rw [eqRec_heq_iff_heq]
            simp_rw [Set.image_union]
            refine Function.hfunext rfl (λ b b' b_eq ↦ ?_)
            cases b_eq
            unfold Set.image
            simp
            admit
        | m + 1, 0, o + 1, .branch fp, .leaf vq, .branch fr => by
          have h₁ : 0 + (o + 1) = o + 1 := Nat.zero_add _
          have h₂ : m + 1 + 0 = m + 1 := Nat.add_zero _
          rw [ProcType.parallel_leaf_p_eq, ProcType.parallel_p_leaf_eq, ProcType.lift_map, ProcType.lift_map, ProcType.lift_congr h₁, ProcType.lift_congr h₂]
          push_cast
          rw [ProcType.lift.branch, ProcType.lift.branch, ProcType.map.branch]
          admit
        | m + 1, n + 1, o + 1, .branch fp, .leaf vq, .branch fr => by
          have h₁ : n + 1 + (o + 1) = n + 1 + o + 1 := by simp +arith
          have h₂ : m + 1 + (n + 1) = m + 1 + n + 1 := Nat.add_zero _
          rw [ProcType.parallel_leaf_p_eq, ProcType.parallel_p_leaf_eq, ProcType.lift_map, ProcType.lift_map, ProcType.lift_congr h₁, ProcType.lift_congr h₂]
          push_cast
          rw [ProcType.lift.branch, ProcType.map.branch, ProcType.lift.branch, ProcType.map.branch]
          admit
        | m + 1, n + 1, 0, .branch fp, .branch fq, .leaf v => by
          admit
        | m + 1, n + 1, o + 1, .branch fp, .branch fq, .leaf v => by
          admit
        | m + 1, n + 1, o + 1, .branch fp, .branch fq, .branch fr => by
          admit
    end
  end
end Domain


























--------------------------------------------------------------------------------------

namespace GoCal.Semantics
  inductive Value : Type

  abbrev Store := AList λ _ : ℕ ↦ Value
  abbrev Channels := AList λ _ : ℕ ↦ WithBot Value

  --------------------------------------------------------------------------------------

  universe u
  variable {Expr Typ : Type u} {init : Expr → Type u}

  -- def M : List (Statement Expr Typ init) → P Store Channels ℕ Value PUnit
  --   | [] => pure .unit
  --   | _ :: _ => sorry
