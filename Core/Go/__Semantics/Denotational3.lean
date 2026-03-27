import CustomPrelude
import Core.Go.Syntax
import Extra.Nat
import Extra.AList
import Extra.Fin
import Extra.List
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Maps.Basic
import Extra.Topology.Constructions.SumProd
import Extra.Topology.Constructions.Maps
import Extra.Topology.IMetricSpace.Constructions
import Extra.Topology.ClosedEmbedding
import Extra.Topology.IsometricEmbedding
import Extra.Topology.UniformContinuousMap
import Mathlib.Data.Part

lemma max_succ {m n} : (m + 1) ⊔ (n + 1) = (m ⊔ n) + 1 := by
  grind only [= max_def]

structure Object.{u} where
  carrier : Type u
  [MetricSpace : IMetricSpace carrier]

instance {o : Object} : IMetricSpace o.carrier := o.MetricSpace

noncomputable section Domain
  /-! # The semantics domains
  -/
  universe u v w x y z
  variable («Σ» : Type u) (Γ : Type v) (α : Type w) (β : Type x) (γ : Type y) (δ : Type z)

  def Branch :=
      (Γ × (α → Bool → Restriction γ unitInterval.half))
    ⊕ (Γ × α × Restriction γ unitInterval.half)
    ⊕ (Γ × Restriction γ unitInterval.half)
    ⊕ (Γ × Restriction γ unitInterval.half)
    ⊕ («Σ» × Restriction γ unitInterval.half)

  section Branch
    variable {«Σ» Γ α β γ δ}

    @[match_pattern]
    protected abbrev Branch.recv (c : Γ) (π : α → Bool → γ) : Branch «Σ» Γ α γ := .inl (c, π)
    @[match_pattern]
    protected abbrev Branch.send (c : Γ) (v : α) (p : γ) : Branch «Σ» Γ α γ := .inr (.inl (c, v, p))
    @[match_pattern]
    protected abbrev Branch.close (c : Γ) (p : γ) : Branch «Σ» Γ α γ := .inr (.inr (.inl (c, p)))
    @[match_pattern]
    protected abbrev Branch.sync (c : Γ) (p : γ) : Branch «Σ» Γ α γ := .inr (.inr (.inr (.inl (c, p))))
    @[match_pattern]
    protected abbrev Branch.next (σ : «Σ») (p : γ) : Branch «Σ» Γ α γ := .inr (.inr (.inr (.inr (σ, p))))

    @[cases_eliminator]
    def Branch.casesOn {motive : Branch «Σ» Γ α γ → Sort _}
      (recv : ∀ c π, motive (.recv c π))
      (send : ∀ c v p, motive (.send c v p))
      (close : ∀ c p, motive (.close c p))
      (sync : ∀ c p, motive (.sync c p))
      (next : ∀ σ p, motive (.next σ p)) :
        ∀ b, motive b
      | .recv c π => recv c π
      | .send c v p => send c v p
      | .close c p => close c p
      | .sync c p => sync c p
      | .next σ p => next σ p

    instance Branch.instIMetricSpace [Nonempty α] [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α] [IMetricSpace γ] :
        IMetricSpace (Branch «Σ» Γ α γ) :=
      Sum.instIMetricSpace

    instance Branch.instCompleteSpace [Nonempty α] [IMetricSpace «Σ»] [CompleteSpace «Σ»] [IMetricSpace Γ] [CompleteSpace Γ] [IMetricSpace α] [CompleteSpace α] [IMetricSpace γ] [CompleteSpace γ] :
        CompleteSpace (Branch «Σ» Γ α γ) :=
      inferInstanceAs (CompleteSpace (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _))
  end Branch

  variable [Nonempty «Σ»] [Nonempty α] [IMetricSpace β] [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α]

  open TopologicalSpace (Closeds)

  instance : IMetricSpace PUnit := .of_metric_space_of_dist_le_one
  instance (priority := high) : CompleteSpace PUnit := inferInstance

  private def IterativeDomain : ℕ → Object.{max u v w x}
    | 0 => { carrier := β ⊕ PUnit.{max u v w + 1} }
    | n + 1 => { carrier := β ⊕ PUnit.{u + 1} ⊕ («Σ» → Set (Branch «Σ» Γ α (IterativeDomain n).carrier)) }

  -- section
  --   variable {«Σ» Γ α β γ δ} [IMetricSpace γ]

  --   theorem LipschitzWith.isClosedEmbedding {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β] {f : α → β} {K}
  --     (hf : LipschitzWith K f) (inj_f : Function.Injective f) (closed_range : IsClosedMap f) :
  --       Topology.IsClosedEmbedding f := by
  --     rw [Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap]
  --     and_intros
  --     · exact LipschitzWith.continuous hf
  --     · exact inj_f
  --     · exact closed_range
  -- end

  section
    variable {«Σ» Γ α β γ δ} [IMetricSpace γ]

    theorem IterativeDomain.idist_cast {m n} (h : m = n) (p q : (IterativeDomain «Σ» Γ α β m).carrier) :
        idist p q = idist (h ▸ p) (h ▸ q) := by
      cases h
      rfl

    @[match_pattern]
    def IterativeDomain.leaf {n} (v : β) : (IterativeDomain «Σ» Γ α β n).carrier := match n with
      | 0 | _ + 1 => .inl v

    @[simp]
    theorem IterativeDomain.idist_leaf_leaf {v v' : β} {n} :
        idist (IterativeDomain.leaf («Σ» := «Σ») (Γ := Γ) (α := α) (n := n) v) (IterativeDomain.leaf v') = idist v v' := by
      cases n <;> rfl

    @[push_cast]
    theorem IterativeDomain.leaf_cast {v : β} {m n} {h : m = n} :
        h ▸ IterativeDomain.leaf («Σ» := «Σ») (Γ := Γ) (α := α) (n := m) v = IterativeDomain.leaf v := by
      cases h
      rfl

    @[match_pattern]
    def IterativeDomain.abort {n} : (IterativeDomain «Σ» Γ α β n).carrier := match n with
      | 0 => .inr .unit
      | _ + 1 => .inr (.inl .unit)

    @[push_cast]
    theorem IterativeDomain.abort_cast {m n} {h : m = n} :
        h ▸ IterativeDomain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (n := m) (β := β) = IterativeDomain.abort := by
      cases h
      rfl

    @[simp]
    theorem IterativeDomain.idist_abort_abort {n} :
        idist (IterativeDomain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (n := n)) IterativeDomain.abort = ⊥ := by
      cases n <;> rfl

    @[simp]
    theorem IterativeDomain.idist_abort_leaf {n} {v : β} :
        idist (IterativeDomain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (n := n)) (IterativeDomain.leaf v) = ⊤ := by
      cases n <;> rfl

    @[simp]
    theorem IterativeDomain.idist_leaf_abort {n} {v : β} :
        idist (IterativeDomain.leaf v) (IterativeDomain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (n := n)) = ⊤ := by
      cases n <;> rfl

    @[match_pattern]
    def IterativeDomain.branch {n} (f : «Σ» → Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)) :
        (IterativeDomain «Σ» Γ α β (n + 1)).carrier :=
      .inr <| .inr f

    @[simp]
    def IterativeDomain.idist_leaf_branch {n} {v : β} {f : «Σ» → Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist (IterativeDomain.leaf v) (IterativeDomain.branch f) = ⊤ := by
      rfl

    @[simp]
    def IterativeDomain.idist_branch_leaf {n} {v : β} {f : «Σ» → Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist (IterativeDomain.branch f) (IterativeDomain.leaf v) = ⊤ := by
      rfl

    @[simp]
    def IterativeDomain.idist_abort_branch {n} {f : «Σ» → Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist IterativeDomain.abort (IterativeDomain.branch f) = ⊤ := by
      rfl

    @[simp]
    def IterativeDomain.idist_branch_abort {n} {f : «Σ» → Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist (IterativeDomain.branch f) IterativeDomain.abort = ⊤ := by
      rfl

    section Lift
      /-! ## Lifting depth of trees -/

      def Branch.map {γ'} [IMetricSpace γ'] (g : γ → γ') :
          (Branch «Σ» Γ α γ) → (Branch «Σ» Γ α γ') :=
        Sum.map (Prod.map id (Pi.map λ _ ↦ Pi.map λ _ ↦ Restriction.map g)) <|
        Sum.map (Prod.map id (Prod.map id (Restriction.map g))) <|
        Sum.map (Prod.map id (Restriction.map g)) <|
        Sum.map (Prod.map id (Restriction.map g)) <|
                (Prod.map id (Restriction.map g))

      -- omit [Nonempty «Σ»] in
      -- theorem Branch.map_closedEmbedding_of_closedEmbedding {γ'} [IMetricSpace γ'] {g : γ → γ'} (hg : Topology.IsClosedEmbedding g) :
      --     Topology.IsClosedEmbedding (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) g) := by
      --   is_closed_embedding <;> {
      --     apply Restriction.map.isClosedEmbedding
      --     assumption
      --   }

      omit [Nonempty «Σ»] in
      theorem Branch.map_isometry' {γ' : Type y} [IMetricSpace γ'] {g : γ → γ'} (hg : ∀ x y : γ, idist (g x) (g y) = idist x y) :
          ∀ (x y : Branch «Σ» Γ α γ), idist (Branch.map g x) (Branch.map g y) = idist x y := by
        rintro (_|_|_|_|_) (_|_|_|_|_) <;> first | rfl | dsimp [map]
        · apply Isometry.prodMap'
          · exact λ _ _ ↦ rfl
          · intros _ _
            apply Isometry.piMap''
            intros _ _ _
            apply Isometry.piMap''
            intros _ _ _
            apply Restriction.map_isometry'
            exact hg
        · apply Isometry.prodMap'
          · exact λ _ _ ↦ rfl
          · intros _ _
            apply Isometry.prodMap'
            · exact λ _ _ ↦ rfl
            · intros _ _
              apply Restriction.map_isometry'
              exact hg
        · apply Isometry.prodMap'
          · exact λ _ _ ↦ rfl
          · intros _ _
            apply Restriction.map_isometry'
            exact hg
        · apply Isometry.prodMap'
          · exact λ _ _ ↦ rfl
          · intros _ _
            apply Restriction.map_isometry'
            exact hg
        · apply Isometry.prodMap'
          · exact λ _ _ ↦ rfl
          · intros _ _
            apply Restriction.map_isometry'
            exact hg

      omit [Nonempty «Σ»] in
      theorem Branch.map_isometry {γ' : Type y} [IMetricSpace γ'] {g : γ → γ'} (hg : Isometry g) :
          Isometry (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) g) := by
        apply Isometry.of_idist_eq
        apply Branch.map_isometry'
        apply Isometry.to_idist_eq
        assumption

      omit [Nonempty «Σ»] in
      theorem Branch.map_uniform_continuous {γ'} [IMetricSpace γ'] {g : γ → γ'} (hg : UniformContinuous g) :
          UniformContinuous (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) g) := by
        apply Topology.UniformContinuous.sumMap
        · apply UniformContinuous.prodMap
          · exact uniformContinuous_id
          · apply Pi.uniformContinuous_map_const
            apply Pi.uniformContinuous_map_const
            apply Restriction.uniformContinuous_map
            exact hg
        · apply Topology.UniformContinuous.sumMap
          · apply UniformContinuous.prodMap
            · exact uniformContinuous_id
            · apply UniformContinuous.prodMap
              · exact uniformContinuous_id
              · apply Restriction.uniformContinuous_map
                exact hg
          · apply Topology.UniformContinuous.sumMap
            · apply UniformContinuous.prodMap
              · exact uniformContinuous_id
              · apply Restriction.uniformContinuous_map
                exact hg
            · apply Topology.UniformContinuous.sumMap
              · apply UniformContinuous.prodMap
                · exact uniformContinuous_id
                · apply Restriction.uniformContinuous_map
                  exact hg
              · apply UniformContinuous.prodMap
                · exact uniformContinuous_id
                · apply Restriction.uniformContinuous_map
                  exact hg

      omit [Nonempty «Σ»] [Nonempty α] [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α] [IMetricSpace γ] in
      theorem Branch.map_comp {γ' γ''} [IMetricSpace γ'] [IMetricSpace γ''] (f : γ → γ') (g : γ' → γ'') :
          (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) g) ∘ (Branch.map f) = (Branch.map (g ∘ f)) := by
        funext b
        cases b <;> simp [Branch.map, Sum.map, Prod.map, Function.comp]
        rfl

      omit [Nonempty «Σ»] [Nonempty α] [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α] in
      theorem Branch.map_id : (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) (γ := γ) id) = id := by
        funext b
        simp [Branch.map]

      def IterativeDomain.lift {m n} (h : m ≤ n := by linarith) :
          (IterativeDomain «Σ» Γ α β m).carrier → (IterativeDomain «Σ» Γ α β n).carrier := match _hm : m, n with
        | 0, 0 => id
        | 0, n + 1 => Sum.elim (λ v ↦ .inl v) (λ .unit ↦ IterativeDomain.abort)
        | m + 1, n + 1 =>
          Sum.map id <|
            Sum.map id <|
            Pi.map λ _ ↦ Set.image (Branch.map (IterativeDomain.lift (m := m)))

      @[simp]
      def IterativeDomain.lift_leaf {m n} (h : m ≤ n) {v : β} :
          (IterativeDomain.lift h (IterativeDomain.leaf («Σ» := «Σ») (Γ := Γ) (α := α) v)) = IterativeDomain.leaf v := by
        cases m <;> fun_induction IterativeDomain <;> first
          | rfl
          | grind

      @[simp]
      def IterativeDomain.lift_abort {m n} (h : m ≤ n) :
          (IterativeDomain.lift h (IterativeDomain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (β := β))) = IterativeDomain.abort := by
        cases m <;> fun_induction IterativeDomain <;> first
          | rfl
          | grind

      @[simp]
      def IterativeDomain.lift_branch {m n} (h : m + 1 ≤ n + 1) {f : «Σ» → Set (Branch «Σ» Γ α _)} :
          IterativeDomain.lift h (IterativeDomain.branch (β := β) f) = IterativeDomain.branch λ σ ↦ Branch.map (IterativeDomain.lift (m := m)) '' f σ :=
        rfl

      @[push_cast]
      def IterativeDomain.lift_cast_right {m n o} {h : m ≤ n} {h' : n = o} {p : (IterativeDomain «Σ» Γ α β m).carrier} :
          h' ▸ IterativeDomain.lift h p = IterativeDomain.lift (h' ▸ h) p := by
        cases h'
        rfl

      -- theorem IterativeDomain.lift.isClosedEmbedding

      -- theorem IterativeDomain.lift_injective {m n} (h : m ≤ n := by linarith) :
      --     Function.Injective (lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) h) :=
      --   (lift h).isClosedEmbedding.injective

      theorem IterativeDomain.lift_refl {m} :
          lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (n := m) (Nat.le_of_eq rfl) = id := by
        cases m with
        | zero => rfl
        | succ m =>
          ext x : 2
          match x with
          | .inl _ | .inr (.inl _) => rfl
          | .inr (.inr f) =>
            dsimp [lift]
            congr 2
            funext b
            rw [Pi.map_apply]
            convert Set.image_id _
            convert Branch.map_id
            rw [lift_refl]

      theorem IterativeDomain.lifl_refl_of_eq {k k' m n} (h : m = n) (h' : k = k') {h'' : m ≤ k} :
          lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) h'' = h ▸ h' ▸ lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (m := n) (n := k') (h ▸ h' ▸ h'') := by
        cases h
        cases h'
        rfl

      theorem IterativeDomain.lift_isometry {m n} (h : m ≤ n) :
          Isometry (lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) h) := by
        match m, n with
        | 0, 0 => exact isometry_id
        | 0, n + 1 => rintro (_|_) (_|_) <;> rfl
        | m + 1, n + 1 =>
          apply Isometry.sumMap
          · exact isometry_id
          · apply Isometry.sumMap
            · exact isometry_id
            · apply Isometry.piMap'
              intros _
              apply Set.image_isometry
              apply Branch.map_isometry
              apply lift_isometry

      theorem IterativeDomain.lift_isometry' {m n} (h : m ≤ n) {x y : (IterativeDomain «Σ» Γ α β m).carrier} :
          idist (lift h x) (lift h y) = idist x y := by
        apply Isometry.to_idist_eq
        exact lift_isometry h

      theorem IterativeDomain.lift_lift {m n o} (h₁ : m ≤ n) (h₂ : n ≤ o) :
          (lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) h₂) ∘ (lift h₁) = (lift (le_trans h₁ h₂)) := by
        funext x
        match m, n, o with
        | 0, 0, 0 | 0, 0, o + 1 => rfl
        | 0, n + 1, o + 1 => cases x <;> rfl
        | m + 1, n + 1, o + 1 =>
          match x with
          | .inl b | .inr (.inl _) => rfl
          | .inr (.inr f) =>
            dsimp [lift]
            congr 2; funext σ
            rw [Pi.map_apply, Pi.map_apply, Pi.map_apply, Set.image_image]
            change (Branch.map _ ∘ Branch.map _) '' (f σ) = _
            rw! [Branch.map_comp, lift_lift]
            rfl
    end Lift
  end

  def DomainUnion := Σ n, (IterativeDomain «Σ» Γ α β n).carrier


  section
    variable {«Σ» Γ α β γ δ} [IMetricSpace γ]

    abbrev DomainUnion.mk {n : ℕ} (x : (IterativeDomain «Σ» Γ α β n).carrier) : DomainUnion «Σ» Γ α β :=
      ⟨n, x⟩

    nonrec abbrev DomainUnion.idist : DomainUnion «Σ» Γ α β → DomainUnion «Σ» Γ α β → unitInterval
      | ⟨m, p⟩, ⟨n, q⟩ => idist (IterativeDomain.lift (le_max_left m n) p) (IterativeDomain.lift (le_max_right m n) q)

    theorem DomainUnion.idist_self (x : DomainUnion «Σ» Γ α β) : DomainUnion.idist x x = 0 := by
      let ⟨m, p⟩ := x
      grind only [PseudoIMetricSpace.idist_self, unitInterval.coe_ne_zero]

    theorem DomainUnion.idist_comm (x y : DomainUnion «Σ» Γ α β) : DomainUnion.idist x y = DomainUnion.idist y x := by
      let ⟨m, p⟩ := x; let ⟨n, q⟩ := y
      grind only [PseudoIMetricSpace.idist_comm]

    nonrec theorem DomainUnion.idist_triangle (x y z : DomainUnion «Σ» Γ α β) : (DomainUnion.idist x z : ℝ) ≤ (DomainUnion.idist x y) + (DomainUnion.idist y z) := by
      let ⟨m, p⟩ := x; let ⟨n, q⟩ := y; let ⟨o, r⟩ := z

      let k := max m (max n o)

      dsimp only [DomainUnion.idist]
      rw [← IterativeDomain.lift_isometry' (by grind only [= max_def] : max m o ≤ k),
          ← IterativeDomain.lift_isometry' (by grind only [= max_def] : max m n ≤ k),
          ← IterativeDomain.lift_isometry' (by grind only [= max_def] : max n o ≤ k)]
      change (IDist.idist ((_ ∘ _) p) ((_ ∘ _) r) : ℝ) ≤ IDist.idist ((_ ∘ _) p) ((_ ∘ _) q) + IDist.idist ((_ ∘ _) q) ((_ ∘ _) r)
      repeat rw [IterativeDomain.lift_lift]
      apply idist_triangle _ _ _

    instance : PseudoIMetricSpace (DomainUnion «Σ» Γ α β) where
      idist := DomainUnion.idist
      idist_self := DomainUnion.idist_self
      idist_comm := DomainUnion.idist_comm
      idist_triangle := DomainUnion.idist_triangle

    theorem DomainUnion.mk_isometry {n} : Isometry (DomainUnion.mk («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (n := n)) := by
      apply Isometry.of_idist_eq λ x y ↦ ?_

      change IDist.idist (IterativeDomain.lift (le_max_left n n) x) (IterativeDomain.lift (le_max_right n n) y) = _
      rw [IterativeDomain.lift_isometry']
  end

  abbrev Domain := UniformSpace.Completion (DomainUnion «Σ» Γ α β)

  example : MetricSpace (Domain «Σ» Γ α β) := inferInstance
  example : CompleteSpace (Domain «Σ» Γ α β) := inferInstance

  theorem _root_.UniformSpace.Completion.dist_le_iff {α} [PseudoMetricSpace α] {ε}
    (h : ∀ x y : α, dist x y ≤ ε) :
      ∀ x y : UniformSpace.Completion α, dist x y ≤ ε := by
    intros x y
    apply UniformSpace.Completion.induction_on₂ (p := (dist · · ≤ ε)) x y
    · exact isClosed_le continuous_dist continuous_const
    · intro a b
      simp only [UniformSpace.Completion.dist_eq, h]

  instance {α} [PseudoIMetricSpace α] : IMetricSpace (UniformSpace.Completion α) :=
    .of_metric_space_of_dist_le_one <| UniformSpace.Completion.dist_le_iff λ x y ↦ unitInterval.le_one (idist x y)

  example : IMetricSpace (Domain «Σ» Γ α β) := inferInstance

  theorem UniformSpace.Completion.idist_eq {α : Type u} [PseudoIMetricSpace α] (x y : α) : idist (x : Completion α) y = idist x y := by
    change (⟨dist (x : Completion α) y, dist_nonneg, UniformSpace.Completion.dist_le_iff (λ x y ↦ unitInterval.le_one (idist x y)) _ _⟩ : unitInterval) = ⟨dist x y, dist_nonneg, unitInterval.le_one (idist x y)⟩
    congr 1
    rw [UniformSpace.Completion.dist_eq]

  variable {«Σ» Γ α β γ δ} [IMetricSpace γ]

  section
    private abbrev embedAt (n : ℕ) (x : (IterativeDomain «Σ» Γ α β n).carrier) : Domain «Σ» Γ α β :=
      ↑(DomainUnion.mk x)

    theorem embedAt_lift_eq {m n : ℕ} (h : m ≤ n) (p : (IterativeDomain «Σ» Γ α β m).carrier) :
        embedAt m p = embedAt n (IterativeDomain.lift h p) := by
      unfold embedAt
      apply eq_of_idist_eq_zero
      rw [UniformSpace.Completion.idist_eq]

      change idist (IterativeDomain.lift (le_max_left m n) p) ((IterativeDomain.lift (le_max_right m n) ∘ IterativeDomain.lift h) p) = 0

      rw [IterativeDomain.lift_lift, IterativeDomain.lift_isometry', idist_self]

    theorem embedAt_comp_lift_eq {m n : ℕ} (h : m ≤ n) :
        embedAt m = (embedAt n ∘ IterativeDomain.lift h : (IterativeDomain «Σ» Γ α β m).carrier → _) := by
      funext p
      exact embedAt_lift_eq h p

    theorem embedAt_isometry {m} :
        Isometry (embedAt («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) m) := by
      unfold embedAt

      change Isometry (UniformSpace.Completion.coe' ∘ DomainUnion.mk)

      apply Isometry.comp
      · exact UniformSpace.Completion.coe_isometry
      · exact DomainUnion.mk_isometry

    private def φ : DomainUnion «Σ» Γ α β → β ⊕ PUnit ⊕ («Σ» → Closeds (Branch «Σ» Γ α (Domain «Σ» Γ α β)))
      | ⟨0, IterativeDomain.leaf v⟩ | ⟨_ + 1, IterativeDomain.leaf v⟩ => .inl v
      | ⟨0, IterativeDomain.abort⟩ | ⟨_ + 1, IterativeDomain.abort⟩ => .inr (.inl .unit)
      | ⟨_ + 1, IterativeDomain.branch f⟩ =>
        .inr <| .inr λ σ ↦ {
          carrier := closure <| Branch.map (embedAt _) '' f σ
          isClosed' := isClosed_closure
        }

    lemma Branch.approx_at_depth
      (b : Branch «Σ» Γ α (Domain «Σ» Γ α β)) {ε : ℝ} (hε : 0 < ε) :
        ∃ (n : _) (b_n : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier),
          idist b (Branch.map (embedAt n) b_n) < ε := by
      sorry

    lemma Closeds.Branch.approx_uniform
      (h : «Σ» → TopologicalSpace.Closeds (Branch «Σ» Γ α (Domain «Σ» Γ α β))) {ε : ℝ} (hε : 0 < ε) :
        ∃ n : ℕ, ∀ σ, ∃ T : Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier),
          IMetric.hausdorffIDist (closure (Branch.map (embedAt n) '' T)) (h σ) ≤ ε / 2 := by
      sorry

    theorem φ_isometry : Isometry (φ («Σ» := «Σ») (Γ := Γ) (α := α) (β := β)) := by
      rintro ⟨m, p⟩ ⟨n, q⟩

      rw [edist_dist, edist_dist]
      change
        ENNReal.ofReal (idist (φ ⟨m, p⟩) (φ ⟨n, q⟩) : ℝ) =
        ENNReal.ofReal (idist (IterativeDomain.lift (le_max_left m n) p) (IterativeDomain.lift (le_max_right m n) q) : ℝ)
      congr 2

      cases m <;> cases n

      case zero.zero =>
        match p, q with
        | IterativeDomain.leaf v, IterativeDomain.leaf v' => rfl
        | IterativeDomain.abort, IterativeDomain.leaf v' => rfl
        | IterativeDomain.leaf v, IterativeDomain.abort => rfl
        | IterativeDomain.abort, IterativeDomain.abort => rfl

      case zero.succ =>
        match p, q with
        | IterativeDomain.leaf v, IterativeDomain.leaf v' => rfl
        | IterativeDomain.abort, IterativeDomain.leaf v' => rfl
        | IterativeDomain.leaf v, IterativeDomain.abort => rfl
        | IterativeDomain.abort, IterativeDomain.abort => rfl
        | IterativeDomain.leaf v, IterativeDomain.branch f => rfl
        | IterativeDomain.abort, IterativeDomain.branch f => rfl

      case succ.zero =>
        match q, p with
        | IterativeDomain.leaf v, IterativeDomain.leaf v' => rfl
        | IterativeDomain.abort, IterativeDomain.leaf v' => rfl
        | IterativeDomain.leaf v, IterativeDomain.abort => rfl
        | IterativeDomain.abort, IterativeDomain.abort => rfl
        | IterativeDomain.leaf v, IterativeDomain.branch f => rfl
        | IterativeDomain.abort, IterativeDomain.branch f => rfl

      case succ.succ m n =>
        match p, q with
        | IterativeDomain.leaf v, IterativeDomain.leaf v'
        | IterativeDomain.abort, IterativeDomain.leaf v'
        | IterativeDomain.leaf v, IterativeDomain.abort
        | IterativeDomain.abort, IterativeDomain.abort =>
          simp; rfl
        | IterativeDomain.branch f, IterativeDomain.leaf v'
        | IterativeDomain.leaf v, IterativeDomain.branch g =>
          simp only [IterativeDomain.lift_leaf, IterativeDomain.idist_cast max_succ]
          push_cast
          rfl
        | IterativeDomain.branch f, IterativeDomain.abort
        | IterativeDomain.abort, IterativeDomain.branch g =>
          simp only [IterativeDomain.lift_abort, IterativeDomain.idist_cast max_succ]
          push_cast
          rfl
        | IterativeDomain.branch f, IterativeDomain.branch g =>
          simp only [IterativeDomain.idist_cast max_succ]
          push_cast
          repeat rw [IterativeDomain.lift_branch]

          change
            ⨆ σ, IMetric.hausdorffIDist (closure (Branch.map (embedAt m) '' f σ)) (closure (Branch.map (embedAt n) '' g σ)) =
            ⨆ σ, IMetric.hausdorffIDist _ _

          set N := max m n

          congr 1; funext σ
          rw [IMetric.hausdorffIDist_closure]

          have h₁ :
              Branch.map (embedAt m : (IterativeDomain «Σ» Γ α β m).carrier → Domain «Σ» Γ α β) =
              Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) (embedAt N) ∘ Branch.map (IterativeDomain.lift (le_max_left m n)) := by
            rw [Branch.map_comp, embedAt_comp_lift_eq (le_max_left m n)]

          have h₂ :
              Branch.map (embedAt n : (IterativeDomain «Σ» Γ α β n).carrier → Domain «Σ» Γ α β) =
              Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) (embedAt N) ∘ Branch.map (IterativeDomain.lift (le_max_right m n)) := by
            rw [Branch.map_comp, embedAt_comp_lift_eq (le_max_right m n)]

          erw [h₁, h₂, Function.comp_def, ← Set.image_image, Function.comp_def, ← Set.image_image (s := g σ)]
          conv_lhs =>
            apply IMetric.hausdorffIDist_image (Φ := Branch.map (embedAt N)) (Branch.map_isometry embedAt_isometry)

    theorem φ_uniform_continuous : UniformContinuous (φ («Σ» := «Σ») (Γ := Γ) (α := α) (β := β)) :=
      φ_isometry.uniformContinuous

    theorem φ_dense : DenseRange (φ («Σ» := «Σ») (Γ := Γ) (α := α) (β := β)) := by
      rw [IMetric.denseRange_iff]
      intro y ε hε
      rcases y with v|_|h
      · exists ⟨0, .inl v⟩
        erwa [idist_self]
      · exists ⟨0, .inr .unit⟩
      · obtain ⟨n, hn⟩ := Closeds.Branch.approx_uniform h hε
        choose T hT using hn
        exists ⟨n + 1, .inr (.inr T)⟩

        change ⨆ σ, IMetric.hausdorffIDist ↑(h σ) (closure (Branch.map (embedAt n) '' T σ)) < ε

        apply LE.le.trans_lt (b := unitInterval.half * ε)
        · apply iSup_le

          convert hT
          change (_ : ℝ) ≤ ↑(unitInterval.half * ε) ↔ _
          rw [IMetric.hausdorffIDist_comm, unitInterval.half_mul_toReal_eq_div_two]
        · exact unitInterval.half_mul_lt_self_of_pos hε

    /--
      We establish the equivalence in order to prove that our defined domain is a solution
      to the original equation.
    -/
    private def Domain.isSolution [CompleteSpace «Σ»] [CompleteSpace Γ] [CompleteSpace α] [CompleteSpace β] :
        Domain «Σ» Γ α β ≃ᵢ β ⊕ PUnit ⊕ («Σ» → Closeds (Branch «Σ» Γ α (Domain «Σ» Γ α β))) :=
      let h := UniformSpace.Completion.extension φ

      have h_iso : Isometry h := Isometry.completion_extension φ_isometry

      have h_antilipschitz := h_iso.antilipschitz

      have h_uniform_continuous := h_iso.uniformContinuous

      have h_complete_range := h_antilipschitz.isComplete_range h_uniform_continuous

      have h_closed_range := h_complete_range.isClosed

      have h_dense : DenseRange h := by
        apply Dense.mono
        · exact Set.range_comp_subset_range ((↑) : DomainUnion «Σ» Γ α β → UniformSpace.Completion _) h
        · unfold h
          rw [Function.comp_def]
          conv => enter [1, 1, x]; rw [UniformSpace.Completion.extension_coe φ_uniform_continuous]
          apply φ_dense

      have h_surj : Function.Surjective h := λ x ↦ by
        have h : x ∈ closure (Set.range h) := h_dense x
        rwa [h_closed_range.closure_eq] at h

      IsometryEquiv.mk
        (Equiv.ofBijective h ⟨h_iso.injective, h_surj⟩)
        h_iso
  end

  section Operators
    section Functor
      /-! ## Functor -/

      def IterativeDomain.map {β'} [IMetricSpace β'] (f : β → β') {n} :
          (IterativeDomain «Σ» Γ α β n).carrier → (IterativeDomain «Σ» Γ α β' n).carrier := match n with
        | 0 => Sum.map f id
        | _ + 1 =>
          Sum.map f <|
          Sum.map id <|
          Pi.map λ _ ↦ Set.image (Branch.map (IterativeDomain.map f))

      theorem IterativeDomain.map_lift {β'} [IMetricSpace β'] (f : β → β')
        {m n} (h : m ≤ n) (x : (IterativeDomain «Σ» Γ α β m).carrier) :
          lift h (map f x) = map f (lift h x) := by
        match m, n with
        | 0, 0 => rfl
        | 0, n + 1 =>
          rcases x with (_|_) <;> rfl
        | m + 1, n + 1 =>
          rcases x with (_|_|_)
          · rfl
          · rfl
          · dsimp [lift, map]
            congr 2
            funext σ
            rw [Pi.map_apply, Pi.map_apply, Pi.map_apply, Pi.map_apply,
                Set.image_image, Set.image_image]
            congr 1
            change Branch.map _ ∘ Branch.map _ = Branch.map _ ∘ Branch.map _
            rw [Branch.map_comp, Branch.map_comp]
            congr 1 with x
            change lift _ (map f x) = map f (lift _ x)
            erw [map_lift]

      def IterativeDomain.map_uniformContinuous {β'} [IMetricSpace β'] {n} (f : β → β') (hf : UniformContinuous f) :
          UniformContinuous (IterativeDomain.map («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (n := n) f) := by
        cases n with
        | zero =>
          apply Topology.UniformContinuous.sumMap
          · exact hf
          · exact uniformContinuous_id
        | succ n =>
          apply Topology.UniformContinuous.sumMap
          · exact hf
          · apply Topology.UniformContinuous.sumMap
            · exact uniformContinuous_id
            · apply Pi.uniformContinuous_map_const
              apply UniformContinuous.image_hausdorff
              apply Branch.map_uniform_continuous
              apply IterativeDomain.map_uniformContinuous
              exact hf

      def DomainUnion.map {β'} [IMetricSpace β'] (f : β → β') :
          DomainUnion «Σ» Γ α β → DomainUnion «Σ» Γ α β' :=
        Sigma.map id λ _ ↦ IterativeDomain.map f

      def DomainUnion.map_uniformContinuous {β'} [IMetricSpace β'] (f : β → β') (hf : UniformContinuous f) :
          UniformContinuous (DomainUnion.map («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) f) := by
        -- TODO: Should be true
        admit

      def Domain.map {β'} [IMetricSpace β'] (f : β → β') :
          Domain «Σ» Γ α β → Domain «Σ» Γ α β' :=
        UniformSpace.Completion.map <| DomainUnion.map f
    end Functor

    -- Default initialisation depending on the given synchronous channel
    variable (zero : Γ → α)

    section Close
      /-! ## Channel closure -/

      mutual
        def Branch.syncClose {n} [DecidableEq Γ] (c : Γ) (σ : «Σ») :
            (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier) → (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier) :=
            Sum.elim (λ (c', π) ↦ if c = c' then .next σ ((IterativeDomain.syncClose c (π (zero c) false)))
                                  else .recv c' (λ v ok ↦ (IterativeDomain.syncClose c (π v ok)))) <|
            Sum.elim (λ (c', v, p) ↦ if c = c' then .next σ IterativeDomain.abort else .send c' v (IterativeDomain.syncClose c p)) <|
            Sum.elim (λ (c', p) ↦ if c = c' then .next σ IterativeDomain.abort else .close c' (IterativeDomain.syncClose c p)) <|
            Sum.elim (λ (c', p) ↦ if c = c' then .next σ IterativeDomain.abort else .sync c' (IterativeDomain.syncClose c p)) <|
                     (λ (σ, p) ↦ .next σ (IterativeDomain.syncClose c p))

        def IterativeDomain.syncClose {n} [DecidableEq Γ] (c : Γ) :
            (IterativeDomain «Σ» Γ α β n).carrier → (IterativeDomain «Σ» Γ α β n).carrier := match n with
          | 0 => id
          | n + 1 => Sum.map id (Sum.map id (Pi.map λ σ ↦ Set.image (Branch.syncClose c σ)))
      end

      theorem IterativeDomain.syncClose.uniform_continuous [DecidableEq Γ] {c : Γ} {n} :
          UniformContinuous (IterativeDomain.syncClose («Σ» := «Σ») (β := β) (n := n) zero c) := by
        admit

      def DomainUnion.syncClose [DecidableEq Γ] (c : Γ) : DomainUnion «Σ» Γ α β → DomainUnion «Σ» Γ α β :=
        Sigma.map id λ _ ↦ IterativeDomain.syncClose zero c

      theorem DomainUnion.syncClose.uniform_continuous [DecidableEq Γ] {c : Γ} :
          UniformContinuous (DomainUnion.syncClose («Σ» := «Σ») (β := β) zero c) := by
        admit

      def Domain.syncClose [DecidableEq Γ] (c : Γ) : Domain «Σ» Γ α β → Domain «Σ» Γ α β :=
        UniformSpace.Completion.map <| DomainUnion.syncClose zero c
    end Close

    section Applicative
      /-! ## Applicative functor -/

      variable (zero : Γ → α)

      private lemma reorder {m n : ℕ} : m + 1 + n = m + n + 1 := by
        simp +arith only

      def IterativeDomain.pure {n} (v : β) : (IterativeDomain «Σ» Γ α β n).carrier := match n with
        | 0 | _ + 1 => .inl v

      def Domain.pure (v : β) : Domain «Σ» Γ α β :=
        (DomainUnion.mk (n := 0) (IterativeDomain.pure («Σ» := «Σ») (Γ := Γ) (α := α) v) : UniformSpace.Completion _)

      mutual
        def Branch.ap {m n} [DecidableEq Γ] [Nonempty β] (p' : (IterativeDomain «Σ» Γ α β n).carrier) :
            Branch «Σ» Γ α (IterativeDomain «Σ» Γ α (β → γ) m).carrier → Branch «Σ» Γ α (IterativeDomain «Σ» Γ α γ (m + n)).carrier :=
          Sum.map (Prod.map id (Pi.map λ _ ↦ Pi.map λ _ ↦ Restriction.map (IterativeDomain.ap · p'))) <|
          Sum.map (Prod.map id <| Prod.map id <| Restriction.map (IterativeDomain.ap · p')) <|
          Sum.map (λ (c, p) ↦ (c, Restriction.map (IterativeDomain.syncClose zero c <| IterativeDomain.ap · p') p)) <|
          Sum.map (Prod.map id <| Restriction.map (IterativeDomain.ap · p')) <|
                  (Prod.map id <| Restriction.map (IterativeDomain.ap · p'))

        def IterativeDomain.ap {m n} [DecidableEq Γ] [Nonempty β] :
            (IterativeDomain «Σ» Γ α (β → γ) m).carrier → (IterativeDomain «Σ» Γ α β n).carrier → (IterativeDomain «Σ» Γ α γ (m + n)).carrier := match m with
          | 0 => Sum.elim
              (λ f t ↦ IterativeDomain.map f ((Nat.zero_add n).symm ▸ t))
              (λ _ _ ↦ IterativeDomain.abort)
          | m + 1 => Sum.elim
              (λ f t ↦ IterativeDomain.map f ((IterativeDomain.lift) t))
              (reorder ▸ Sum.elim
                (λ _ _ ↦ IterativeDomain.abort)
                (λ g t ↦ IterativeDomain.branch λ σ ↦ Branch.ap t '' g σ))
      end

      theorem IterativeDomain.ap.uniform_continuous₂ [DecidableEq Γ] [Nonempty β] {m n} :
          UniformContinuous₂ (IterativeDomain.ap zero («Σ» := «Σ») (β := β) (γ := γ) (m := m) (n := n)) := by
        admit

      def DomainUnion.ap [DecidableEq Γ] [Nonempty β] :
          DomainUnion «Σ» Γ α (β → γ) → DomainUnion «Σ» Γ α β → DomainUnion «Σ» Γ α γ :=
        λ ⟨_, p⟩ ⟨_, q⟩ ↦ DomainUnion.mk (IterativeDomain.ap zero p q)

      theorem DomainUnion.ap.uniform_continuous₂ [DecidableEq Γ] [Nonempty β] :
          UniformContinuous₂ (DomainUnion.ap zero («Σ» := «Σ») (β := β) (γ := γ)) := by
        admit

      def Domain.ap [DecidableEq Γ] [Nonempty β] :
          Domain «Σ» Γ α (β → γ) → Domain «Σ» Γ α β → Domain «Σ» Γ α γ :=
        UniformSpace.Completion.extension₂ (λ x y ↦ DomainUnion.ap zero x y)
    end Applicative

    section Monad
      /-! ## Monad -/

      /-!
        Unfortunately, this operator is inexpressible within Lean.

        Here's the problem.
        Assume that we want to define the operator on `IterativeDomain`, then lift it
        on `Domain` by extension.
        Our signature would look like
        ```lean
        def IterativeDomain.bind {m n} (x : IterativeDomain «Σ» Γ α β m).carrier)
          (f : β → IterativeDomain «Σ» Γ α γ n).carrier) :
            IterativeDomain «Σ» Γ α γ (m + n)).carrier
        ```
        Yet, this signature assumes that `f` maps all leaves of `x` to trees that are of
        depth at most `n`.
        Unfortunately, if `f` performs infinitely many choices, mapping each leaf to trees
        that are bigger and bigger, the actual depth becomes unbounded!
      -/

      axiom Domain.bind : Domain «Σ» Γ α β → (β → Domain «Σ» Γ α γ) → Domain «Σ» Γ α γ
    end Monad

    section Sequence
      mutual
        def Branch.seq {m n} (q : (IterativeDomain «Σ» Γ α PUnit n).carrier) : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α PUnit m).carrier → Branch «Σ» Γ α (IterativeDomain «Σ» Γ α PUnit (m + n)).carrier :=
          Sum.map (Prod.map id (Pi.map λ _ ↦ Pi.map λ _ ↦ Restriction.map (IterativeDomain.seq · q))) <|
          Sum.map (Prod.map id (Prod.map id (Restriction.map (IterativeDomain.seq · q)))) <|
          Sum.map (Prod.map id (Restriction.map (IterativeDomain.seq · q))) <|
          Sum.map (Prod.map id (Restriction.map (IterativeDomain.seq · q))) <|
          Prod.map id (Restriction.map (IterativeDomain.seq · q))

        def IterativeDomain.seq {m n} : (IterativeDomain «Σ» Γ α PUnit m).carrier → (IterativeDomain «Σ» Γ α PUnit n).carrier → (IterativeDomain «Σ» Γ α PUnit (m + n)).carrier :=
          match m with
          | 0 => Sum.elim (λ _ t ↦ Nat.zero_add _ ▸ t) (λ _ _ ↦ IterativeDomain.abort)
          | m + 1 =>
            Sum.elim (λ _ t ↦ IterativeDomain.lift (by grind only) t) <|
            Sum.elim (λ _ _ ↦ IterativeDomain.abort) <|
            λ g t ↦ reorder ▸ IterativeDomain.branch λ σ ↦ Branch.seq t '' g σ
      end

      theorem IterativeDomain.seq_uniform_continuous {m n} :
          UniformContinuous₂ (IterativeDomain.seq («Σ» := «Σ») (Γ := Γ) (α := α) (m := m) (n := n)) := by
        admit

      def DomainUnion.seq : DomainUnion «Σ» Γ α PUnit → DomainUnion «Σ» Γ α PUnit → DomainUnion «Σ» Γ α PUnit :=
        λ ⟨_, p⟩ ⟨_, q⟩ ↦ DomainUnion.mk (IterativeDomain.seq p q)

      theorem DomainUnion.seq_uniform_continuous :
          UniformContinuous₂ (DomainUnion.seq («Σ» := «Σ») (Γ := Γ) (α := α)) := by
        admit

      def Domain.seq : Domain «Σ» Γ α PUnit → Domain «Σ» Γ α PUnit → Domain «Σ» Γ α PUnit :=
        UniformSpace.Completion.extension₂ (λ x y ↦ DomainUnion.seq x y)
    end Sequence

    section Choice
      def IterativeDomain.choice {m n} (p : (IterativeDomain «Σ» Γ α PUnit m).carrier) (q : (IterativeDomain «Σ» Γ α PUnit n).carrier) :
          (IterativeDomain «Σ» Γ α PUnit (m ⊔ n)).carrier :=
        match m, n, p, q with
        | 0, _, .inl _, q | _ + 1, _, .inl _, q => IterativeDomain.lift (by grind only [= max_def]) q
        | _, 0, p, .inl _ | _, _ + 1, p, .inl _ => IterativeDomain.lift (by grind only [= max_def]) p
        | 0, _, IterativeDomain.abort, q | _ + 1, _, IterativeDomain.abort, q => IterativeDomain.abort
        | _, 0, p, IterativeDomain.abort | _, _ + 1, p, IterativeDomain.abort => IterativeDomain.abort
        | m + 1, n + 1, IterativeDomain.branch g, IterativeDomain.branch g' =>
          max_succ ▸ IterativeDomain.branch λ σ ↦
            (Branch.map (IterativeDomain.lift (m := m) (n := max m n) (le_max_left m n)) '' g σ) ∪
            (Branch.map (IterativeDomain.lift (m := n) (n := max m n) (le_max_right m n)) '' g' σ)

      theorem IterativeDomain.choice_uniform_continuous {m n} :
          UniformContinuous₂ (IterativeDomain.choice («Σ» := «Σ») (Γ := Γ) (α := α) (m := m) (n := n)) := by
        admit

      def DomainUnion.choice : DomainUnion «Σ» Γ α PUnit → DomainUnion «Σ» Γ α PUnit → DomainUnion «Σ» Γ α PUnit :=
        λ ⟨_, p⟩ ⟨_, q⟩ ↦ DomainUnion.mk (IterativeDomain.choice p q)

      theorem DomainUnion.choice_uniform_continuous :
          UniformContinuous₂ (DomainUnion.choice («Σ» := «Σ») (Γ := Γ) (α := α)) := by
        admit

      def Domain.choice : Domain «Σ» Γ α PUnit → Domain «Σ» Γ α PUnit → Domain «Σ» Γ α PUnit :=
        UniformSpace.Completion.extension₂ (λ x y ↦ DomainUnion.choice x y)
    end Choice

    section EventHiding
      /-! ## Event hiding -/

      open Classical in
      mutual
        def Branch.hide [DecidableEq Γ] (σ : «Σ») (c : Γ) (Ω : Set Γ) {n} : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier → Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier) :=
          Sum.elim (λ (c', π) ↦ if c = c' then ∅ else if c' ∈ Ω then {Branch.next σ (π (zero c') false)} else {Branch.recv c' λ v ok ↦ Restriction.map (IterativeDomain.hide c Ω) (π v ok)}) <|
          Sum.elim (λ (c', v, p) ↦ if c = c' then ∅ else {Branch.send c' v (Restriction.map (IterativeDomain.hide c Ω) p)}) <|
          Sum.elim (λ (c', p) ↦ if c = c' then {Branch.next σ (Restriction.map (IterativeDomain.hide c Ω) p)} else {Branch.close c' (Restriction.map (IterativeDomain.hide c (Ω ∪ {c'})) p)}) <|
          Sum.elim (λ (c', p) ↦ if c = c' then ∅ else {Branch.sync c' (Restriction.map (IterativeDomain.hide c Ω) p)}) <|
          λ (σ, p) ↦ {Branch.next σ (IterativeDomain.hide c Ω p)}

        def IterativeDomain.hide [DecidableEq Γ] (c : Γ) (Ω : Set Γ) {n} : (IterativeDomain «Σ» Γ α β n).carrier → (IterativeDomain «Σ» Γ α β n).carrier :=
          match n with
          | 0 => id
          | n + 1 =>
            Sum.map id <|
            Sum.map id <|
            Pi.map λ σ X ↦
              let Y := ⋃ b ∈ X, Branch.hide σ c Ω b
              Y ∪ if Y = ∅ ∧ X ≠ ∅ then {Branch.next σ IterativeDomain.abort} else ∅
      end

      theorem IterativeDomain.hide_uniform_continuous [DecidableEq Γ] {c : Γ} {Ω : Set Γ} {n} :
          UniformContinuous (IterativeDomain.hide («Σ» := «Σ») (α := α) (β := β) (n := n) zero c Ω) := by
        admit

      def DomainUnion.hide [DecidableEq Γ] (c : Γ) (Ω : Set Γ) : DomainUnion «Σ» Γ α β → DomainUnion «Σ» Γ α β :=
        Sigma.map id λ _ ↦ IterativeDomain.hide zero c Ω

      theorem DomainUnion.hide_uniform_continuous [DecidableEq Γ] {c : Γ} {Ω : Set Γ} :
          UniformContinuous (DomainUnion.hide («Σ» := «Σ») (α := α) (β := β) zero c Ω) := by
        admit

      def Domain.hide [DecidableEq Γ] (c : Γ) (Ω : Set Γ) : Domain «Σ» Γ α β → Domain «Σ» Γ α β :=
        UniformSpace.Completion.map (DomainUnion.hide zero c Ω)
    end EventHiding

    section Parallel
      /-! ## Parallel composition -/

      private lemma jsp {m n} : (m + 1).add n = m + (n + 1) := Nat.succ_add_eq_add_succ m n

      mutual
        def Branch.parallel_left {m n} (p' : (IterativeDomain «Σ» Γ α γ n).carrier) :
            Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β m).carrier → Branch «Σ» Γ α (IterativeDomain «Σ» Γ α (β × γ) (m + n)).carrier :=
          Sum.map (Prod.map id (Pi.map λ _ ↦ Pi.map λ _ ↦ Restriction.map (IterativeDomain.parallel · p'))) <|
          Sum.map (Prod.map id (Prod.map id (Restriction.map (IterativeDomain.parallel · p')))) <|
          Sum.map (Prod.map id (Restriction.map (IterativeDomain.parallel · p'))) <|
          Sum.map (Prod.map id (Restriction.map (IterativeDomain.parallel · p'))) <|
                  (Prod.map id (Restriction.map (IterativeDomain.parallel · p')))

        def Branch.parallel_right {m n} (p : (IterativeDomain «Σ» Γ α β m).carrier) :
            Branch «Σ» Γ α (IterativeDomain «Σ» Γ α γ n).carrier → Branch «Σ» Γ α (IterativeDomain «Σ» Γ α (β × γ) (m + n)).carrier :=
          Sum.map (Prod.map id (Pi.map λ _ ↦ Pi.map λ _ ↦ Restriction.map (IterativeDomain.parallel p))) <|
          Sum.map (Prod.map id (Prod.map id (Restriction.map (IterativeDomain.parallel p)))) <|
          Sum.map (Prod.map id (Restriction.map (IterativeDomain.parallel p))) <|
          Sum.map (Prod.map id (Restriction.map (IterativeDomain.parallel p))) <|
                  (Prod.map id (Restriction.map (IterativeDomain.parallel p)))

        def IterativeDomain.parallel {m n} (p : (IterativeDomain «Σ» Γ α β m).carrier) (p' : (IterativeDomain «Σ» Γ α γ n).carrier) : (IterativeDomain «Σ» Γ α (β × γ) (m + n)).carrier :=
          match m, n, p, p' with
          | 0, _, IterativeDomain.leaf v, p' | m + 1, _, IterativeDomain.leaf v, p' =>
            IterativeDomain.lift (by grind only) <| IterativeDomain.map (v, ·) p'
          | _, 0, p, IterativeDomain.leaf v | _, n + 1, p, IterativeDomain.leaf v =>
            IterativeDomain.lift (by grind only) <| IterativeDomain.map (·, v) p
          | 0, _, IterativeDomain.abort, _ | m + 1, _, IterativeDomain.abort, _
          | _, 0, _, IterativeDomain.abort | _, n + 1, _, IterativeDomain.abort =>
            IterativeDomain.abort
          | m + 1, n + 1, IterativeDomain.branch g, IterativeDomain.branch g' => IterativeDomain.branch λ σ ↦
            -- Interleavings
              {jsp.symm ▸ Branch.parallel_left (IterativeDomain.branch (n := n) g') b | b ∈ g σ}
            ∪ {Branch.parallel_right (IterativeDomain.branch g) b' | b' ∈ g' σ}
            -- Synchronisations
            ∪ {p | ∃ v γ p' π', .send γ v p' ∈ g σ ∧ .recv γ π' ∈ g' σ ∧ p = .sync γ (IterativeDomain.lift (by grind only) (IterativeDomain.parallel p' (π' v true)))}
            ∪ {p | ∃ v γ p' π', .send γ v p' ∈ g' σ ∧ .recv γ π' ∈ g σ ∧ p = .sync γ (IterativeDomain.lift (by grind only) (IterativeDomain.parallel (π' v true) p'))}
            -- Channel closure
            ∪ {p | ∃ v γ p' p'', .send γ v p' ∈ g σ ∧ .close γ p'' ∈ g' σ ∧ p = .next σ IterativeDomain.abort}
            ∪ {p | ∃ v γ p' p'', .send γ v p' ∈ g' σ ∧ .close γ p'' ∈ g σ ∧ p = .next σ IterativeDomain.abort}
            ∪ {p | ∃ γ π' p', .recv γ π' ∈ g σ ∧ .close γ p' ∈ g' σ ∧ p = .close γ (IterativeDomain.lift (by grind only) (IterativeDomain.parallel (π' (zero γ) false) p'))}
            ∪ {p | ∃ γ π' p', .recv γ π' ∈ g' σ ∧ .close γ p' ∈ g σ ∧ p = .close γ (IterativeDomain.lift (by grind only) (IterativeDomain.parallel p' (π' (zero γ) false)))}
      end

      theorem IterativeDomain.parallel_uniform_continuous {m n} :
          UniformContinuous₂ (IterativeDomain.parallel zero («Σ» := «Σ») (β := β) (γ := γ) (m := m) (n := n)) := by
        admit

      def DomainUnion.parallel : DomainUnion «Σ» Γ α β → DomainUnion «Σ» Γ α γ → DomainUnion «Σ» Γ α (β × γ) :=
        λ ⟨_, p⟩ ⟨_, q⟩ ↦ DomainUnion.mk (IterativeDomain.parallel zero p q)

      theorem DomainUnion.parallel_uniform_continuous :
          UniformContinuous₂ (DomainUnion.parallel zero («Σ» := «Σ») (β := β) (γ := γ)) := by
        admit

      def Domain.parallel : Domain «Σ» Γ α β → Domain «Σ» Γ α γ → Domain «Σ» Γ α (β × γ) :=
        UniformSpace.Completion.extension₂ (λ x y ↦ DomainUnion.parallel zero x y)
    end Parallel
  end Operators




  namespace Value
    variable (Γ «Σ»)
    variable (ℍ : Type v) (Typ : Type w) [IMetricSpace ℍ] [IMetricSpace Typ]

    protected abbrev F (𝕍 : Type u) [Nonempty 𝕍] [IMetricSpace 𝕍] : Type _ :=
      -- bool
        Bool
      -- int
      ⊕ ℤ
      -- str
      ⊕ String
      -- slice
      ⊕ ℕ × ℕ × ℕ × ℕ
      -- chan
      ⊕ ℕ × Typ × ℍ × ℍ
      -- struct
      ⊕ (String → Option ℍ)
      -- array
      ⊕ ℕ × (ℕ → Option ℍ)
      -- map
      ⊕ (Restriction 𝕍 unitInterval.half → Option ℍ) × Bool
      -- func
      ⊕ (String → Option ℍ) × (List (Restriction 𝕍 unitInterval.half) × List Γ × (String → Option Γ) → Domain «Σ» Γ 𝕍 (Restriction 𝕍 unitInterval.half))

    -- TODO: transport the metric spaces into I

    instance : IMetricSpace ℕ where
      idist := sorry
      idist_self := sorry
      idist_comm := sorry
      idist_triangle := sorry
      eq_of_idist_eq_zero := sorry

    instance : IMetricSpace ℤ where
      idist := sorry
      idist_self := sorry
      idist_comm := sorry
      idist_triangle := sorry
      eq_of_idist_eq_zero := sorry

    instance : IMetricSpace String where
      idist := sorry
      idist_self := sorry
      idist_comm := sorry
      idist_triangle := sorry
      eq_of_idist_eq_zero := sorry

    instance {α} [IMetricSpace α] : IMetricSpace (List α) where
      idist := sorry
      idist_self := sorry
      idist_comm := sorry
      idist_triangle := sorry
      eq_of_idist_eq_zero := sorry

    open Filter in
    instance : IMetricSpace Bool where
      idist x y := if x = y then ⊥ else ⊤
      idist_self x := by rw [if_pos rfl]; rfl
      idist_comm x y := by grind only
      idist_triangle x y z := by
        grind only [= Set.mem_Icc, usr Subtype.property, unitInterval.bot_eq,
          unitInterval.coe_ne_one, unitInterval.coe_ne_zero, unitInterval.top_eq,
          unitInterval.zero_eq]
      eq_of_idist_eq_zero {x y} h := by
        split at h
        · assumption
        · grind only [unitInterval.coe_ne_one, unitInterval.coe_ne_zero, unitInterval.top_eq]

      toUniformSpace := inferInstance
      uniformity_idist := by
        change 𝓟 SetRel.id = _
        admit

    instance {𝕍 : Type u} [Nonempty 𝕍] [IMetricSpace 𝕍] : IMetricSpace (Value.F «Σ» Γ ℍ Typ 𝕍) :=
      inferInstance

    /-!
      How do we define the domain of values, obtained from the following equation:
      ```
      𝕍 = ((𝒱 ⇀ ℍ) → 𝕍)                                       -- struct
        ⊎ (ℕ × (ℕ ⇀ ℍ) → 𝕍)                                   -- array
        ⊎ (ℕ × ℕ × ℕ × ℍ → 𝕍)                                 -- slice
        ⊎ ((𝕍 ⇀ ℍ) × 𝔹 → 𝕍)                                   -- map
        ⊎ (ℕ × Type × ℍ × ℍ → 𝕍)                              -- chan
        ⊎ (𝔹 → 𝕍)                                             -- bool
        ⊎ (ℤ → 𝕍)                                             -- int
        ⊎ (String → 𝕍)                                        -- str
        ⊎ ((𝒱 ⇀ ℍ) × (𝕍* × 𝔽 × Γ* × (𝒱 ⇀ Γ) → P(𝕍, ⊤)) → 𝕍) -- func
      ```
      ?

      For now, let's just axiomatize them. We know they exist (from various results
      of domain theory), we just don't construct them yet.
      `𝕍` is just very cumbersome to define and construct. We'll leave this as
      future work for now.
    -/
    axiom 𝕍 : NonemptyType

    instance : Nonempty 𝕍.type := 𝕍.property

    @[instance]
    axiom 𝕍_metricSpace : IMetricSpace 𝕍.type

    /--
      Axiomatize the fact that `𝕍` is a solution to the recursive domain
      equation `𝕍 = F(𝕍)`.
    -/
    axiom 𝕍_iso : 𝕍.type ≃ᵢ Value.F «Σ» Γ ℍ Typ 𝕍.type
  end Value
end Domain

/-!
  Now that we have finished defining our domains…we can finally define the semantics of
  Go.
-/
