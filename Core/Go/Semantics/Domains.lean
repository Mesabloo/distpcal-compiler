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
import Extra.Sigma
-- import Mathlib.Data.Part

open scoped UniformConvergence
attribute [-instance] UniformFun.instPseudoEMetricSpace UniformFun.instEMetricSpace

lemma max_succ {m n} : (m + 1) ⊔ (n + 1) = (m ⊔ n) + 1 := by
  grind only [= max_def]

structure Object.{u} where
  carrier : Type u
  [MetricSpace : PseudoIMetricSpace carrier]

instance {o : Object} : PseudoIMetricSpace o.carrier := o.MetricSpace

noncomputable section Domain
  /-! # The semantics domains
  -/
  universe u v w x y z
  variable («Σ» : Type u) (Γ : Type v) (α : Type w) (β : Type x) (γ : Type y) (δ : Type z)

  def Branch :=
      (Γ × (α →ᵤ Bool →ᵤ Restriction γ unitInterval.half))
    ⊕ (Γ × α × Restriction γ unitInterval.half)
    ⊕ (Γ × Restriction γ unitInterval.half)
    ⊕ (Γ × Restriction γ unitInterval.half)
    ⊕ («Σ» × Restriction γ unitInterval.half)

  section Branch
    variable {«Σ» Γ α β γ δ}

    @[match_pattern]
    protected abbrev Branch.recv (c : Γ) (π : α →ᵤ Bool →ᵤ Restriction γ unitInterval.half) : Branch «Σ» Γ α γ := .inl (c, π)
    @[match_pattern]
    protected abbrev Branch.send (c : Γ) (v : α) (p : Restriction γ unitInterval.half) : Branch «Σ» Γ α γ := .inr (.inl (c, v, p))
    @[match_pattern]
    protected abbrev Branch.close (c : Γ) (p : Restriction γ unitInterval.half) : Branch «Σ» Γ α γ := .inr (.inr (.inl (c, p)))
    @[match_pattern]
    protected abbrev Branch.sync (c : Γ) (p : Restriction γ unitInterval.half) : Branch «Σ» Γ α γ := .inr (.inr (.inr (.inl (c, p))))
    @[match_pattern]
    protected abbrev Branch.next (σ : «Σ») (p : Restriction γ unitInterval.half) : Branch «Σ» Γ α γ := .inr (.inr (.inr (.inr (σ, p))))

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

    instance Branch.instPseudoIMetricSpace [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] :
        PseudoIMetricSpace (Branch «Σ» Γ α γ) :=
      inferInstanceAs (PseudoIMetricSpace (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _))

    instance Branch.instIMetricSpace [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α] [IMetricSpace γ] :
        IMetricSpace (Branch «Σ» Γ α γ) :=
      inferInstanceAs (IMetricSpace (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _))

    instance Branch.instCompleteSpace [IMetricSpace «Σ»] [CompleteSpace «Σ»] [IMetricSpace Γ] [CompleteSpace Γ] [IMetricSpace α] [CompleteSpace α] [IMetricSpace γ] [CompleteSpace γ] :
        CompleteSpace (Branch «Σ» Γ α γ) :=
      inferInstanceAs (CompleteSpace (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _))
  end Branch

  variable [PseudoIMetricSpace β] [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α]

  open TopologicalSpace (Closeds)

  instance : IMetricSpace PUnit := .of_metric_space_of_dist_le_one
  instance (priority := high) : CompleteSpace PUnit := inferInstance

  private def IterativeDomain : ℕ → Object.{max u v w x}
    | 0 => { carrier := β ⊕ PUnit.{max u v w + 1} }
    | n + 1 => { carrier := β ⊕ PUnit.{u + 1} ⊕ («Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain n).carrier)) }

  section
    variable {«Σ» Γ α β γ δ} [PseudoIMetricSpace γ]

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
    def IterativeDomain.branch {n} (f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)) :
        (IterativeDomain «Σ» Γ α β (n + 1)).carrier :=
      .inr <| .inr f

    @[simp]
    def IterativeDomain.idist_leaf_branch {n} {v : β} {f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist (IterativeDomain.leaf v) (IterativeDomain.branch f) = ⊤ := by
      rfl

    @[simp]
    def IterativeDomain.idist_branch_leaf {n} {v : β} {f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist (IterativeDomain.branch f) (IterativeDomain.leaf v) = ⊤ := by
      rfl

    @[simp]
    def IterativeDomain.idist_abort_branch {n} {f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist IterativeDomain.abort (IterativeDomain.branch f) = ⊤ := by
      rfl

    @[simp]
    def IterativeDomain.idist_branch_abort {n} {f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist (IterativeDomain.branch f) IterativeDomain.abort = ⊤ := by
      rfl

    @[simp]
    def IterativeDomain.idist_branch_branch {n} {f g : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist (IterativeDomain.branch f) (IterativeDomain.branch g) = ⨆ σ, IMetric.hausdorffIDist (f σ) (g σ) := by
      erw [UniformFun.idist_eq_iSup]
      rfl

    section Lift
      /-! ## Lifting depth of trees -/

      def Branch.map {γ'} [PseudoIMetricSpace γ'] (g : γ → γ') :
          (Branch «Σ» Γ α γ) → (Branch «Σ» Γ α γ') :=
        Sum.map (Prod.map id (UniformFun.map (UniformFun.map (Restriction.map g)))) <|
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

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] [PseudoIMetricSpace Γ] in
      theorem Branch.map_recv {γ'} [PseudoIMetricSpace γ'] {f : γ → γ'} {c : Γ} {π : α →ᵤ Bool →ᵤ Restriction γ unitInterval.half} :
          Branch.map f (Branch.recv («Σ» := «Σ») c π) = Branch.recv c λ v ok ↦ Restriction.map f (π v ok) := by
        rfl

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] [PseudoIMetricSpace Γ] in
      theorem Branch.map_send {γ'} [PseudoIMetricSpace γ'] {f : γ → γ'} {c : Γ} {v : α} {x : Restriction γ unitInterval.half} :
          Branch.map f (Branch.send («Σ» := «Σ») c v x) = Branch.send c v (Restriction.map f x) := by
        rfl

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] [PseudoIMetricSpace Γ] in
      theorem Branch.map_close {γ'} [PseudoIMetricSpace γ'] {f : γ → γ'} {c : Γ} {x : Restriction γ unitInterval.half} :
          Branch.map f (Branch.close («Σ» := «Σ») (α := α) c x) = Branch.close c (Restriction.map f x) := by
        rfl

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] [PseudoIMetricSpace Γ] in
      theorem Branch.map_sync {γ'} [PseudoIMetricSpace γ'] {f : γ → γ'} {c : Γ} {x : Restriction γ unitInterval.half} :
          Branch.map f (Branch.sync («Σ» := «Σ») (α := α) c x) = Branch.sync c (Restriction.map f x) := by
        rfl

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] [PseudoIMetricSpace Γ] in
      theorem Branch.map_next {γ'} [PseudoIMetricSpace γ'] {f : γ → γ'} {σ : «Σ»} {x : Restriction γ unitInterval.half} :
          Branch.map f (Branch.next (Γ := Γ) (α := α) σ x) = Branch.next σ (Restriction.map f x) := by
        rfl

      theorem Branch.map_isometry' {γ' : Type y} [PseudoIMetricSpace γ'] {g : γ → γ'} (hg : ∀ x y : γ, idist (g x) (g y) = idist x y) :
          ∀ (x y : Branch «Σ» Γ α γ), idist (Branch.map g x) (Branch.map g y) = idist x y := by
        rintro (_|_|_|_|_) (_|_|_|_|_) <;> first | rfl | dsimp [map]
        · apply Isometry.prodMap'
          · exact λ _ _ ↦ rfl
          · intros _ _
            apply UniformFun.map_isometry'
            intros _ _
            apply UniformFun.map_isometry'
            intros _ _
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

      theorem Branch.map_isometry {γ' : Type y} [PseudoIMetricSpace γ'] {g : γ → γ'} (hg : Isometry g) :
          Isometry (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) g) := by
        apply Isometry.of_idist_eq
        apply Branch.map_isometry'
        apply Isometry.to_idist_eq
        assumption

      theorem Branch.map_uniform_continuous {γ'} [PseudoIMetricSpace γ'] {g : γ → γ'} (hg : UniformContinuous g) :
          UniformContinuous (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) g) := by
        apply Topology.UniformContinuous.sumMap
        · apply UniformContinuous.prodMap
          · exact uniformContinuous_id
          · apply UniformFun.uniformContinuous_map
            apply UniformFun.uniformContinuous_map
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

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] in
      theorem Branch.map_comp {γ' γ''} [PseudoIMetricSpace γ'] [PseudoIMetricSpace γ''] (f : γ → γ') (g : γ' → γ'') :
          (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) g) ∘ (Branch.map f) = (Branch.map (g ∘ f)) := by
        funext b
        cases b <;> simp [Branch.map, Sum.map, Prod.map, Restriction.map, Function.comp]
        rfl

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] in
      theorem Branch.map_id : (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) (γ := γ) id) = id := by
        funext b
        apply b.casesOn <;> solve_by_elim

      private lemma Branch.map_idist_le
        {γ γ' : Type _} [PseudoIMetricSpace γ] [PseudoIMetricSpace γ']
        {g g' : γ → γ'} {r : unitInterval}
        (hr : ∀ x : γ, unitInterval.half * idist (g x) (g' x) ≤ r)
        (b : Branch «Σ» Γ α γ) :
          idist (Branch.map g b) (Branch.map g' b) ≤ r := by
        cases b with
        | recv c f =>
          dsimp [Branch.recv, Branch.map]
          change max (idist c c) (idist (UniformFun.map (UniformFun.map (Restriction.map g)) f) (UniformFun.map (UniformFun.map (Restriction.map g')) f)) ≤ _
          simp_rw [UniformFun.idist_eq_iSup]
          change max (idist c c) (⨆ v, ⨆ ok, unitInterval.half * idist (g (f v ok).val) (g' (f v ok).val)) ≤ _
          rw [idist_self, ← unitInterval.bot_eq, bot_sup_eq]
          apply iSup₂_le
          intros v ok
          apply hr
        | send c v p =>
          change max (idist c c) (max (idist v v) (unitInterval.half * idist (g p.val) (g' p.val))) ≤ r

          repeat erw [idist_self, bot_sup_eq]
          apply hr
        | close c p =>
          change max (idist c c) (unitInterval.half * idist (g p.val) (g' p.val)) ≤ r

          repeat erw [idist_self, bot_sup_eq]
          apply hr
        | sync c p =>
          change max (idist c c) (unitInterval.half * idist (g p.val) (g' p.val)) ≤ r

          repeat erw [idist_self, bot_sup_eq]
          apply hr
        | next σ p =>
          change max (idist σ σ) (unitInterval.half * idist (g p.val) (g' p.val)) ≤ r

          repeat erw [idist_self, bot_sup_eq]
          apply hr

      def IterativeDomain.lift {m n} (h : m ≤ n := by linarith) :
          (IterativeDomain «Σ» Γ α β m).carrier → (IterativeDomain «Σ» Γ α β n).carrier := match _hm : m, n with
        | 0, 0 => id
        | 0, n + 1 => Sum.elim (λ v ↦ .inl v) (λ .unit ↦ IterativeDomain.abort)
        | m + 1, n + 1 =>
          Sum.map id <|
            Sum.map id <|
              UniformFun.map <| Set.image (Branch.map (IterativeDomain.lift (m := m)))

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
      def IterativeDomain.lift_branch {m n} (h : m + 1 ≤ n + 1) {f : «Σ» →ᵤ Set (Branch «Σ» Γ α _)} :
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
            rw [UniformFun.map_apply]
            convert Set.image_id _
            convert Branch.map_id
            rw [lift_refl]

      theorem IterativeDomain.lift_refl_of_eq {k k' m n} (h : m = n) (h' : k = k') {h'' : m ≤ k} :
          lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) h'' = h ▸ h' ▸ lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (m := n) (n := k') (h ▸ h' ▸ h'') := by
        cases h
        cases h'
        rfl

      theorem IterativeDomain.lift_refl_of_eq' {k k' m n} (h : m = n) (h' : k = k') {h'' : m ≤ k} {x} :
          lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) h'' x = h' ▸ lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (m := n) (n := k') (h ▸ h' ▸ h'') (h ▸ x) := by
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
            · apply UniformFun.map_isometry
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
            rw [UniformFun.map_apply, UniformFun.map_apply, UniformFun.map_apply, Set.image_image]
            change (Branch.map _ ∘ Branch.map _) '' (f σ) = _
            rw! [Branch.map_comp, lift_lift]
            rfl
    end Lift

    section Truncation
      def IterativeDomain.trunc : ∀ {n m : ℕ}, n ≤ m → (IterativeDomain «Σ» Γ α β m).carrier → (IterativeDomain «Σ» Γ α β n).carrier
        | 0, 0,     _, x => x
        | 0, _ + 1, _, x => Sum.elim Sum.inl (fun _ => .inr .unit) x
        | _ + 1, _ + 1, h, x =>
          Sum.elim Sum.inl
            (Sum.elim (Sum.inr ∘ Sum.inl) fun f =>
              .inr <| .inr fun σ =>
                Branch.map (IterativeDomain.trunc (Nat.le_of_succ_le_succ h)) '' f σ)
            x
    end Truncation
  end

  def DomainUnion := Σ n, (IterativeDomain «Σ» Γ α β n).carrier

  section
    variable {«Σ» Γ α β γ δ} [PseudoIMetricSpace γ]

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

    lemma DomainUnion.lift_idist_zero {n m : ℕ} (h : n ≤ m)
        (x : (IterativeDomain «Σ» Γ α β n).carrier) :
        DomainUnion.idist ⟨n, x⟩ ⟨m, IterativeDomain.lift h x⟩ = 0 := by
      change IDist.idist (IterativeDomain.lift _ x) ((IterativeDomain.lift _ ∘ IterativeDomain.lift _) x) = 0
      rw [IterativeDomain.lift_lift, Isometry.to_idist_eq (IterativeDomain.lift_isometry _), PseudoIMetricSpace.idist_self]

    lemma IterativeDomain.trunc_idist {n m} (h : n ≤ m) (x : (IterativeDomain «Σ» Γ α β m).carrier) :
        (DomainUnion.idist ⟨m, x⟩ ⟨n, IterativeDomain.trunc h x⟩ : ℝ) ≤ (1/2 : ℝ) ^ n := by
      match n, m, h, x with
      | 0, _, _, _ => exact unitInterval.le_one _
      | n + 1, m + 1, h, IterativeDomain.leaf v =>
          change idist (IterativeDomain.lift _ _) _ ≤ unitInterval.half ^ (n + 1)
          erw [IterativeDomain.lift_leaf, IterativeDomain.lift_leaf, idist_self]
          bound
      | n + 1, m + 1, h, IterativeDomain.abort =>
          change idist (IterativeDomain.lift _ _) _ ≤ unitInterval.half ^ (n + 1)
          erw [IterativeDomain.lift_abort, IterativeDomain.lift_abort, idist_self]
          bound
      | n + 1, m + 1, h, IterativeDomain.branch f =>
          have max_eq : max (m + 1) (n + 1) = m + 1 := by grind only [= max_def]

          change idist (IterativeDomain.lift _ _) (IterativeDomain.lift _ (IterativeDomain.branch _)) ≤ unitInterval.half ^ (n + 1)

          repeat rw [IterativeDomain.lift_refl_of_eq' rfl max_eq]
          rw [← IterativeDomain.idist_cast, IterativeDomain.lift_refl]

          change idist (IterativeDomain.branch _) (IterativeDomain.lift _ (IterativeDomain.branch _)) ≤ unitInterval.half ^ (n + 1)

          repeat rw [IterativeDomain.lift_branch]
          rw [IterativeDomain.idist_branch_branch]

          apply iSup_le
          intro σ

          rw [← Set.image_comp, Branch.map_comp]
          trans
          · exact IMetric.hausdorffIDist_image_le_of_le_sup
          · apply iSup₂_le
            intros b b_in
            convert_to idist (Branch.map id b) _ ≤ _
            · rw [Branch.map_id]; rfl
            · apply Branch.map_idist_le
              intros x

              trans (unitInterval.half * unitInterval.half^n)
              · have IH := trunc_idist (Nat.add_one_le_add_one_iff.mp h) x

                have max_eq' : max m n = m := by grind only [= max_def]

                change idist (IterativeDomain.lift _ _) (IterativeDomain.lift _ _) ≤ unitInterval.half ^ n at IH

                repeat rw [IterativeDomain.lift_refl_of_eq' rfl max_eq'] at IH
                rw [← IterativeDomain.idist_cast, IterativeDomain.lift_refl] at IH

                change _ * idist x ((IterativeDomain.lift _ ∘ IterativeDomain.trunc _) x) ≤ _
                change idist x ((IterativeDomain.lift _ ∘ IterativeDomain.trunc _) x) ≤ _ at IH
                grw [IH]
              · rw [pow_add, pow_one, mul_comm]
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

  theorem Domain.edist_eq {x y : Domain «Σ» Γ α β} : edist x y = ENNReal.ofReal (dist x y) := by
    rw [edist_dist]

  theorem Domain.dist_eq {x y : Domain «Σ» Γ α β} : dist x y = (idist x y : ℝ) := by
    rfl

  variable {«Σ» Γ α β γ δ} [PseudoIMetricSpace γ]

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

    lemma embedAt_idist_eq {n m : ℕ} (x : (IterativeDomain «Σ» Γ α β n).carrier)
        (y : (IterativeDomain «Σ» Γ α β m).carrier) :
        (idist (embedAt n x) (embedAt m y) : ℝ) = DomainUnion.idist ⟨n, x⟩ ⟨m, y⟩ := by
      erw [UniformSpace.Completion.idist_eq]
      rfl

    def φ : DomainUnion «Σ» Γ α β → β ⊕ PUnit.{x + 1} ⊕ («Σ» →ᵤ Closeds (Branch «Σ» Γ α (Domain «Σ» Γ α β)))
      | ⟨0, IterativeDomain.leaf v⟩ | ⟨_ + 1, IterativeDomain.leaf v⟩ => .inl v
      | ⟨0, IterativeDomain.abort⟩ | ⟨_ + 1, IterativeDomain.abort⟩ => .inr (.inl .unit)
      | ⟨_ + 1, IterativeDomain.branch f⟩ =>
        .inr <| .inr λ σ ↦ {
          carrier := closure <| Branch.map (embedAt _) '' f σ
          isClosed' := isClosed_closure
        }

    lemma Domain.approx_uniform (d : Domain «Σ» Γ α β) (n : ℕ) :
        ∃ x : (IterativeDomain «Σ» Γ α β n).carrier,
          (idist d (embedAt n x) : ℝ) < 2 * (1/2 : ℝ) ^ n := by
      have hpos : (0 : ℝ) < (1/2 : ℝ) ^ n := pow_pos (by norm_num) _
      obtain ⟨⟨m, y⟩, hy⟩ :
          ∃ z : DomainUnion «Σ» Γ α β, (idist d (↑z : Domain «Σ» Γ α β) : ℝ) < (1/2 : ℝ) ^ n :=
        UniformSpace.Completion.denseRange_coe.exists_dist_lt d hpos
      rcases le_or_gt m n with hmn | hnm
      · refine ⟨IterativeDomain.lift hmn y, ?_⟩
        have h0 : (idist (embedAt m y) (embedAt n (IterativeDomain.lift hmn y)) : ℝ) = 0 := by
          rw [embedAt_idist_eq, DomainUnion.lift_idist_zero hmn y]
          rfl
        linarith [idist_triangle (α := Domain «Σ» Γ α β) d (embedAt m y) (embedAt n (IterativeDomain.lift hmn y))]
      · refine ⟨IterativeDomain.trunc hnm.le y, ?_⟩
        have htr : (idist (embedAt m y) (embedAt n (IterativeDomain.trunc hnm.le y)) : ℝ) ≤ (1/2)^n := by
          rw [embedAt_idist_eq]
          exact IterativeDomain.trunc_idist hnm.le y
        linarith [idist_triangle (α := Domain «Σ» Γ α β) d (embedAt m y) (embedAt n (IterativeDomain.trunc (LT.lt.le hnm) y))]

    private lemma Branch.approx_uniform_depth (b : Branch «Σ» Γ α (Domain «Σ» Γ α β)) (n : ℕ) :
        ∃ b_n : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier,
          (idist b (Branch.map (embedAt n) b_n) : ℝ) ≤ (1/2) ^ n := by
      rcases b with ⟨γ₀, π⟩ | ⟨γ₀, a, d⟩ | ⟨γ₀, d⟩ | ⟨γ₀, d⟩ | ⟨s₀, d⟩
      · exists .recv γ₀ λ v ok => { val := Classical.choose (Domain.approx_uniform (π v ok).val n) }

        change max (idist γ₀ γ₀) (idist π _) ≤ unitInterval.half^n
        simp_rw [UniformFun.idist_eq_iSup]
        change max (idist γ₀ γ₀) (⨆ v, ⨆ ok, idist (π v ok) _) ≤ unitInterval.half^n
        rw [idist_self, ← unitInterval.bot_eq, bot_sup_eq]
        apply iSup₂_le λ v ok ↦ ?_

        change unitInterval.half * idist (π v ok).val (embedAt n (Classical.choose (Domain.approx_uniform (π v ok).val n))) ≤ _

        have : (idist (π v ok).val (embedAt n (Classical.choose (Domain.approx_uniform (π v ok).val n))) : ℝ) < 2 * (1/2)^n :=
          Classical.choose_spec (Domain.approx_uniform (π v ok).val n)

        change ((1/2) * _ : ℝ) ≤ (1/2)^n
        linarith
      · obtain ⟨x_n, hx⟩ := Domain.approx_uniform d.val n
        exists .send γ₀ a { val := x_n }

        change ↑(@max unitInterval _ (idist γ₀ γ₀) (max (idist a a) (idist _ _)) : ℝ) ≤ _
        erw [idist_self, idist_self, ← unitInterval.bot_eq, bot_sup_eq, bot_sup_eq]

        change (1/2) * (idist d.val (embedAt n x_n) : ℝ) ≤ _
        linarith
      · obtain ⟨x_n, hx⟩ := Domain.approx_uniform d.val n
        exists .close γ₀ { val := x_n }

        change ↑(@max unitInterval _ (idist γ₀ γ₀) (idist _ _) : ℝ) ≤ _
        erw [idist_self, ← unitInterval.bot_eq, bot_sup_eq]

        change (1/2) * (idist d.val (embedAt n x_n) : ℝ) ≤ _
        linarith
      · obtain ⟨x_n, hx⟩ := Domain.approx_uniform d.val n
        exists .sync γ₀ { val := x_n }

        change ↑(@max unitInterval _ (idist γ₀ γ₀) (idist _ _) : ℝ) ≤ _
        erw [idist_self, ← unitInterval.bot_eq, bot_sup_eq]

        change (1/2) * (idist d.val (embedAt n x_n) : ℝ) ≤ _
        linarith
      · obtain ⟨x_n, hx⟩ := Domain.approx_uniform d.val n
        exists .next s₀ { val := x_n }

        change ↑(@max unitInterval _ (idist s₀ s₀) (idist _ _) : ℝ) ≤ _
        erw [idist_self, ← unitInterval.bot_eq, bot_sup_eq]

        change (1/2) * (idist d.val (embedAt n x_n) : ℝ) ≤ _
        linarith

    lemma Branch.approx_at_depth (b : Branch «Σ» Γ α (Domain «Σ» Γ α β)) {ε : ℝ} (hε : 0 < ε) :
        ∃ (n : _) (b_n : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier),
          idist b (Branch.map (embedAt n) b_n) < ε := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2 : ℝ) < 1)
      obtain ⟨b_n, hb⟩ := Branch.approx_uniform_depth b n
      exact ⟨n, b_n, hb.trans_lt hn⟩

    lemma Closeds.Branch.approx_uniform
        (h : «Σ» → TopologicalSpace.Closeds (Branch «Σ» Γ α (Domain «Σ» Γ α β)))
        {ε : ℝ} (hε : 0 < ε) :
        ∃ n : ℕ, ∀ σ, ∃ T : Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier),
          IMetric.hausdorffIDist (closure (Branch.map (embedAt n) '' T)) (↑(h σ)) ≤ ε / 2 := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1/2 : ℝ) < 1)
      refine ⟨n, fun σ => ⟨(fun b => Classical.choose (Branch.approx_uniform_depth b n)) '' (h σ), ?_⟩⟩

      have hbound : ∀ b ∈ h σ,
          (idist b (Branch.map (embedAt n)
            (Classical.choose (Branch.approx_uniform_depth b n))) : ℝ) ≤ (1/2)^n :=
        fun b _ => Classical.choose_spec (Branch.approx_uniform_depth b n)

      trans (1 / 2)^n
      · conv_lhs =>
          enter [1, 2];
          rw [← IsClosed.closure_eq (h := TopologicalSpace.Closeds.isClosed (h σ))]
        rw [IMetric.hausdorffIDist_closure, IMetric.hausdorffIDist_comm, Set.image_image]
        grw [IMetric.hausdorffIDist_image_le_of_le_sup, iSup₂_le (a := unitInterval.half^n)]
        · rfl
        · exact hbound
      · exact le_of_lt hn

    lemma φ_dense : DenseRange (φ («Σ» := «Σ») (Γ := Γ) (α := α) (β := β)) := by
      intro y
      rcases y with v | ⟨⟩ | h
      · exact subset_closure ⟨⟨0, .inl v⟩, rfl⟩
      · exact subset_closure ⟨⟨0, .inr .unit⟩, rfl⟩
      · rw [mem_closure_iff_nhds']
        intro U hU
        obtain ⟨ε, hε, hball⟩ := IMetric.nhds_basis_ball.mem_iff.mp hU
        obtain ⟨n, hT⟩ := Closeds.Branch.approx_uniform h hε
        choose T hT' using hT
        exists ⟨φ ⟨n + 1, .inr (.inr (T ·))⟩, ?_⟩
        · grind only [= Set.mem_range]
        · apply hball
          rw [IMetric.mem_ball']

          apply LE.le.trans_lt (b := ε / 2)
          · erw [idist_comm, UniformFun.idist_eq_iSup]
            change (⨆ σ : «Σ», IMetric.hausdorffIDist (closure (Branch.map (embedAt n) '' T σ)) (h σ)).val ≤ ε / 2

            by_cases h : ε / 2 ≤ 1
            · have ge_zero : 0 ≤ ε / 2 := by linarith

              change _ ≤ (⟨ε / 2, ⟨ge_zero, h⟩⟩ : unitInterval)
              change ∀ σ, _ ≤ (⟨ε / 2, ⟨ge_zero, h⟩⟩ : unitInterval) at hT'

              apply iSup_le
              assumption
            · trans 1
              · apply unitInterval.le_one
              · apply le_of_not_ge h
          · exact half_lt_self hε

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
            idist (α := «Σ» →ᵤ _) (λ σ ↦ (closure (Branch.map (embedAt m) '' f σ))) (_) =
            idist (α := «Σ» →ᵤ _) (λ σ ↦ Branch.map (IterativeDomain.lift _) '' f σ) (λ σ ↦ Branch.map (IterativeDomain.lift _) '' g σ)
          repeat erw [UniformFun.idist_eq_iSup]
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

    section
      variable
        {«Σ» : Type u} {Γ : Type v} {α : Type w} {β : Type x} {γ : Type y} {δ : Type z}
        [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α] [IMetricSpace β]
        [CompleteSpace «Σ»] [CompleteSpace Γ] [CompleteSpace α] [CompleteSpace β]

      /--
        We establish the equivalence in order to prove that our defined domain is a solution
        to the original equation.
      -/
      private def Domain.isSolution :
          Domain «Σ» Γ α β ≃ᵢ β ⊕ PUnit.{x + 1} ⊕ («Σ» →ᵤ Closeds (Branch «Σ» Γ α (Domain «Σ» Γ α β))) :=
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

      def Domain.abort : Domain «Σ» Γ α β :=
        ⇑Domain.isSolution.symm (.inr (.inl .unit))

      def Domain.leaf (v : β) : Domain «Σ» Γ α β :=
        ⇑Domain.isSolution.symm (.inl v)

      def Domain.branch (f : «Σ» →ᵤ Set (Branch «Σ» Γ α (Domain «Σ» Γ α β))) : Domain «Σ» Γ α β :=
        ⇑Domain.isSolution.symm (.inr (.inr λ σ ↦ ⟨closure (f σ), isClosed_closure⟩))

      instance : Nonempty (Domain «Σ» Γ α β) := .intro .abort
    end
  end



  section Operators
    variable
      {«Σ» : Type u} {Γ : Type v} {α : Type w} {β : Type x} {γ : Type y} {δ : Type z}
      [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α] [IMetricSpace β] [IMetricSpace γ]
      -- [CompleteSpace «Σ»] [CompleteSpace Γ] [CompleteSpace α] [CompleteSpace β]

    section Functor
      /-! ## Functor -/

      def IterativeDomain.map {β'} [IMetricSpace β'] (f : β →ᵤ β') {n} :
          (IterativeDomain «Σ» Γ α β n).carrier → (IterativeDomain «Σ» Γ α β' n).carrier := match n with
        | 0 => Sum.map f id
        | _ + 1 =>
          Sum.map f <|
          Sum.map id <|
          UniformFun.map <| Set.image (Branch.map (IterativeDomain.map f))

      theorem IterativeDomain.map_leaf {β'} [IMetricSpace β'] {f : β →ᵤ β'} {v : β} {n} :
          map f (leaf («Σ» := «Σ») (Γ := Γ) (α := α) (n := n) v) = leaf (f v) := by
        cases n with rfl

      theorem IterativeDomain.map_abort {β'} [IMetricSpace β'] {f : β →ᵤ β'} {n} :
          map f (abort («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (n := n)) = abort := by
        cases n with rfl

      theorem IterativeDomain.map_branch {β'} [IMetricSpace β'] {f : β →ᵤ β'} {n} {g : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
          map f (branch g) = branch λ σ ↦ Branch.map (IterativeDomain.map f) '' g σ := by
        rfl

      theorem IterativeDomain.map_lift {β'} [IMetricSpace β'] (f : β →ᵤ β')
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
            rw [UniformFun.map_apply, UniformFun.map_apply, UniformFun.map_apply, UniformFun.map_apply,
                Set.image_image, Set.image_image]
            congr 1
            change Branch.map _ ∘ Branch.map _ = Branch.map _ ∘ Branch.map _
            rw [Branch.map_comp, Branch.map_comp]
            congr 1 with x
            change lift _ (map f x) = map f (lift _ x)
            erw [map_lift]

      theorem IterativeDomain.map_id {n} {p : (IterativeDomain «Σ» Γ α β n).carrier} : map id p = p := by
        match n, p with
        | 0, IterativeDomain.leaf v => rfl
        | 0, IterativeDomain.abort => rfl
        | n + 1, IterativeDomain.leaf v => rfl
        | n + 1, IterativeDomain.abort => rfl
        | n + 1, IterativeDomain.branch f =>
          change IterativeDomain.branch (λ σ ↦ Branch.map (map id) '' f σ) = _
          congr 1 with σ : 1
          convert Set.image_id _
          conv_lhs => enter [1, x]; rw [map_id]
          apply Branch.map_id

      theorem IterativeDomain.map_id' {n} : map («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (n := n) id = id := by
        funext p
        apply IterativeDomain.map_id

      theorem IterativeDomain.map_map {γ'} [IMetricSpace γ'] {n} {f : β →ᵤ γ} {g : γ →ᵤ γ'} {p : (IterativeDomain «Σ» Γ α β n).carrier} :
          map g (map f p) = map (g ∘ f) p := by
        match n, p with
        | 0, IterativeDomain.leaf v => rfl
        | n + 1, IterativeDomain.leaf v => rfl
        | 0, IterativeDomain.abort => rfl
        | n + 1, IterativeDomain.abort => rfl
        | n + 1, IterativeDomain.branch h =>
          change branch (λ σ : «Σ» ↦ Branch.map (map g) '' (Branch.map (map f) '' h σ)) = branch (λ σ ↦ Branch.map (map (g ∘ f)) '' h σ)
          congr 1 with σ : 1
          rw [Set.image_image]
          congr 1 with b : 1
          conv_rhs => enter [1, p]; rw [← IterativeDomain.map_map]
          erw [← Branch.map_comp (map f) (map g)]
          rfl

      theorem IterativeDomain.map_map' {γ'} [IMetricSpace γ'] {n} {f : β →ᵤ γ} {g : γ →ᵤ γ'} :
          map («Σ» := «Σ») (Γ := Γ) (α := α) (β := γ) (n := n) g ∘ map f = map (g ∘ f) := by
        funext p
        apply IterativeDomain.map_map

      def IterativeDomain.map_uniformContinuous {β'} [IMetricSpace β'] {n} (f : β →ᵤ β') (hf : UniformContinuous f) :
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
            · apply UniformFun.uniformContinuous_map
              apply UniformContinuous.image_hausdorff
              apply Branch.map_uniform_continuous
              apply IterativeDomain.map_uniformContinuous
              exact hf

      def DomainUnion.map {β'} [IMetricSpace β'] (f : β →ᵤ β') :
          DomainUnion «Σ» Γ α β → DomainUnion «Σ» Γ α β' :=
        Sigma.map id λ _ ↦ IterativeDomain.map f

      theorem DomainUnion.map_id {p : DomainUnion «Σ» Γ α β} : map id p = p := by
        unfold map
        conv_lhs => enter [2, x]; rw [IterativeDomain.map_id']
        rw [Sigma.map_id_id]
        rfl

      theorem DomainUnion.map_id' : map («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) id = id := by
        funext p
        apply DomainUnion.map_id

      theorem DomainUnion.map_map {γ'} [IMetricSpace γ'] {f : β →ᵤ γ} {g : γ →ᵤ γ'} {p : DomainUnion «Σ» Γ α β} :
          map g (map f p) = map (g ∘ f) p := by
        unfold map
        simp [Sigma.map_map, Function.comp_id, IterativeDomain.map_map']

      theorem DomainUnion.map_map' {γ'} [IMetricSpace γ'] {f : β →ᵤ γ} {g : γ →ᵤ γ'} :
          map («Σ» := «Σ») (Γ := Γ) (α := α) g ∘ map f = map (g ∘ f) := by
        funext p
        apply DomainUnion.map_map

      def DomainUnion.map_uniformContinuous {β'} [IMetricSpace β'] (f : β →ᵤ β') (hf : UniformContinuous f) :
          UniformContinuous (DomainUnion.map («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) f) := by
        -- TODO: Should be true
        admit

      /-- Map leaves of the tree using a given function. -/
      def Domain.map {β'} [IMetricSpace β'] (f : β →ᵤ β') :
          Domain «Σ» Γ α β → Domain «Σ» Γ α β' :=
        UniformSpace.Completion.map <| DomainUnion.map f

      theorem Domain.map_id {p : Domain «Σ» Γ α β} : map id p = p := by
        unfold map
        rw [DomainUnion.map_id', UniformSpace.Completion.map_id]
        rfl

      theorem Domain.map_map {γ'} [IMetricSpace γ'] {f : β →ᵤ γ} {g : γ →ᵤ γ'} {p : Domain «Σ» Γ α β}
        (hf : UniformContinuous f) (hg : UniformContinuous g) :
          map g (map f p) = map (g ∘ f) p := by
        unfold map
        change (UniformSpace.Completion.map _ ∘ _) p = _
        rw [UniformSpace.Completion.map_comp, DomainUnion.map_map']
        · apply DomainUnion.map_uniformContinuous
          assumption
        · apply DomainUnion.map_uniformContinuous
          assumption
    end Functor

    class HasDefaultInit (Γ : Type _) (α : outParam (Type _)) where
      zero : Γ → α

    -- Default initialisation depending on the given synchronous channel
    variable (zero : Γ → α)

    section Close
      /-! ## Channel closure -/

      mutual
        def Branch.syncClose {n} [DecidableEq Γ] (c : Γ) (σ : «Σ») :
            (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier) → (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier) :=
          Sum.elim (λ (c', π) ↦ if c = c' then .next σ ⟨IterativeDomain.syncClose c (π (zero c) false).val⟩
                                else .recv c' (λ v ok ↦ ⟨IterativeDomain.syncClose c (π v ok).val⟩)) <|
          Sum.elim (λ (c', v, p) ↦ if c = c' then .next σ ⟨IterativeDomain.abort⟩ else .send c' v ⟨IterativeDomain.syncClose c p.val⟩) <|
          Sum.elim (λ (c', p) ↦ if c = c' then .next σ ⟨IterativeDomain.abort⟩ else .close c' ⟨IterativeDomain.syncClose c p.val⟩) <|
          Sum.elim (λ (c', p) ↦ if c = c' then .next σ ⟨IterativeDomain.abort⟩ else .sync c' ⟨IterativeDomain.syncClose c p.val⟩) <|
                    (λ (σ, p) ↦ .next σ ⟨IterativeDomain.syncClose c p.val⟩)

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

      /--
        Close a synchronous channel `c` in the tree, pruning subtrees accordingly.
      -/
      def Domain.syncClose [DecidableEq Γ] (c : Γ) : Domain «Σ» Γ α β → Domain «Σ» Γ α β :=
        UniformSpace.Completion.map <| DomainUnion.syncClose zero c

      @[inherit_doc Domain.syncClose]
      abbrev Domain.syncClose' [DecidableEq Γ] [inst : HasDefaultInit Γ α] (c : Γ) : Domain «Σ» Γ α β → Domain «Σ» Γ α β :=
        Domain.syncClose inst.zero c
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
        def Branch.ap {m n} [DecidableEq Γ] (p' : (IterativeDomain «Σ» Γ α β n).carrier) :
            Branch «Σ» Γ α (IterativeDomain «Σ» Γ α (β →ᵤ γ) m).carrier → Branch «Σ» Γ α (IterativeDomain «Σ» Γ α γ (m + n)).carrier :=
          Sum.map (Prod.map id (Pi.map λ _ ↦ Pi.map λ _ ↦ Restriction.map (IterativeDomain.ap · p'))) <|
          Sum.map (Prod.map id <| Prod.map id <| Restriction.map (IterativeDomain.ap · p')) <|
          Sum.map (λ (c, p) ↦ (c, Restriction.map (IterativeDomain.syncClose zero c <| IterativeDomain.ap · p') p)) <|
          Sum.map (Prod.map id <| Restriction.map (IterativeDomain.ap · p')) <|
                  (Prod.map id <| Restriction.map (IterativeDomain.ap · p'))

        def IterativeDomain.ap {m n} [DecidableEq Γ] :
            (IterativeDomain «Σ» Γ α (β →ᵤ γ) m).carrier → (IterativeDomain «Σ» Γ α β n).carrier → (IterativeDomain «Σ» Γ α γ (m + n)).carrier := match m with
          | 0 => Sum.elim
              (λ f t ↦ IterativeDomain.map f ((Nat.zero_add n).symm ▸ t))
              (λ _ _ ↦ IterativeDomain.abort)
          | m + 1 => Sum.elim
              (λ f t ↦ IterativeDomain.map f ((IterativeDomain.lift) t))
              (reorder ▸ Sum.elim
                (λ _ _ ↦ IterativeDomain.abort)
                (λ g t ↦ IterativeDomain.branch λ σ ↦ Branch.ap t '' g σ))
      end

      theorem IterativeDomain.ap_leaf {v : β → γ} [DecidableEq Γ] {m n} {q : (IterativeDomain «Σ» Γ α β n).carrier} :
          ap zero (leaf (n := m) v) q = map v (lift (Nat.le_add_left _ _) q) := by
        cases m with unfold ap
        | zero =>
          dsimp [leaf]
          rw [IterativeDomain.lift_refl_of_eq' rfl (Nat.zero_add n), lift_refl]
          rfl
        | succ n =>
          rfl

      theorem IterativeDomain.ap_abort [DecidableEq Γ] {m n} {q : (IterativeDomain «Σ» Γ α β n).carrier} :
          ap zero (abort (β := β →ᵤ γ) (n := m)) q = abort := by
        cases m with (unfold ap)
        | zero =>
          rfl
        | succ n =>
          rw! [reorder]
          rfl

      theorem IterativeDomain.ap_branch [DecidableEq Γ] {m n} {g : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α (β →ᵤ γ) m).carrier)} {q : (IterativeDomain «Σ» Γ α β n).carrier} :
          ap zero (branch g) q = reorder ▸ branch λ σ ↦ Branch.ap zero q '' g σ := by
        unfold ap
        rw! [reorder]
        rfl

      theorem Branch.ap_recv [DecidableEq Γ] {c : Γ} {m n} {π : α →ᵤ Bool →ᵤ Restriction (IterativeDomain «Σ» Γ α (β →ᵤ γ) m).carrier unitInterval.half} {q : (IterativeDomain «Σ» Γ α β n).carrier} :
          Branch.ap zero q (Branch.recv c π) = Branch.recv c λ v ok ↦ Restriction.map (IterativeDomain.ap zero · q) (π v ok) := by
        unfold ap
        rfl

      theorem Branch.ap_send [DecidableEq Γ] {c : Γ} {v : α} {m n} {p : Restriction (IterativeDomain «Σ» Γ α (β →ᵤ γ) m).carrier unitInterval.half} {q : (IterativeDomain «Σ» Γ α β n).carrier} :
          Branch.ap zero q (Branch.send c v p) = Branch.send c v (Restriction.map (IterativeDomain.ap zero · q) p) := by
        unfold ap
        rfl

      theorem Branch.ap_close [DecidableEq Γ] {c : Γ} {m n} {p : Restriction (IterativeDomain «Σ» Γ α (β →ᵤ γ) m).carrier unitInterval.half} {q : (IterativeDomain «Σ» Γ α β n).carrier} :
          Branch.ap zero q (Branch.close c p) = Branch.close c (Restriction.map (IterativeDomain.syncClose zero c <| IterativeDomain.ap zero · q) p) := by
        unfold ap
        rfl

      theorem Branch.ap_sync [DecidableEq Γ] {c : Γ} {m n} {p : Restriction (IterativeDomain «Σ» Γ α (β →ᵤ γ) m).carrier unitInterval.half} {q : (IterativeDomain «Σ» Γ α β n).carrier} :
          Branch.ap zero q (Branch.sync c p) = Branch.sync c (Restriction.map (IterativeDomain.ap zero · q) p) := by
        unfold ap
        rfl

      theorem Branch.ap_next [DecidableEq Γ] {σ : «Σ»} {m n} {p : Restriction (IterativeDomain «Σ» Γ α (β →ᵤ γ) m).carrier unitInterval.half} {q : (IterativeDomain «Σ» Γ α β n).carrier} :
          Branch.ap zero q (Branch.next σ p) = Branch.next σ (Restriction.map (IterativeDomain.ap zero · q) p) := by
        unfold ap
        rfl

      theorem IterativeDomain.ap.uniform_continuous₂ [DecidableEq Γ] {m n} :
          UniformContinuous₂ (IterativeDomain.ap zero («Σ» := «Σ») (β := β) (γ := γ) (m := m) (n := n)) := by
        admit

      def DomainUnion.ap [DecidableEq Γ] :
          DomainUnion «Σ» Γ α (β →ᵤ γ) → DomainUnion «Σ» Γ α β → DomainUnion «Σ» Γ α γ :=
        λ ⟨_, p⟩ ⟨_, q⟩ ↦ DomainUnion.mk (IterativeDomain.ap zero p q)

      theorem DomainUnion.ap.uniform_continuous₂ [DecidableEq Γ] :
          UniformContinuous₂ (DomainUnion.ap zero («Σ» := «Σ») (β := β) (γ := γ)) := by
        admit

      def Domain.ap [DecidableEq Γ] : Domain «Σ» Γ α (β →ᵤ γ) → Domain «Σ» Γ α β → Domain «Σ» Γ α γ :=
        UniformSpace.Completion.extension₂ (λ x y ↦ DomainUnion.ap zero x y)

      /-- General form of sequential composition. -/
      def Domain.ap' [DecidableEq Γ] [inst : HasDefaultInit Γ α] : Domain «Σ» Γ α (β →ᵤ γ) → Domain «Σ» Γ α β → Domain «Σ» Γ α γ :=
        Domain.ap inst.zero
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

      /-- Replace leaves of the tree with subtrees depending on the value of the leaves. -/
      axiom Domain.bind : Domain «Σ» Γ α β → (β → Domain «Σ» Γ α γ) → Domain «Σ» Γ α γ
    end Monad

    section Sequence
      mutual
        def Branch.seq [DecidableEq Γ] {m n} (q : (IterativeDomain «Σ» Γ α PUnit n).carrier) : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α PUnit.{x + 1} m).carrier → Branch «Σ» Γ α (IterativeDomain «Σ» Γ α PUnit.{x + 1} (m + n)).carrier :=
          Sum.map (Prod.map id (Pi.map λ _ ↦ Pi.map λ _ ↦ Restriction.map (IterativeDomain.seq · q))) <|
          Sum.map (Prod.map id (Prod.map id (Restriction.map (IterativeDomain.seq · q)))) <|
          Sum.map (λ (c, p) ↦ (c, Restriction.map (IterativeDomain.syncClose zero c <| IterativeDomain.seq · q) p)) <|
          Sum.map (Prod.map id (Restriction.map (IterativeDomain.seq · q))) <|
          Prod.map id (Restriction.map (IterativeDomain.seq · q))

        def IterativeDomain.seq [DecidableEq Γ] {m n} : (IterativeDomain «Σ» Γ α PUnit.{x + 1} m).carrier → (IterativeDomain «Σ» Γ α PUnit.{x + 1} n).carrier → (IterativeDomain «Σ» Γ α PUnit.{x + 1} (m + n)).carrier :=
          match m with
          | 0 => Sum.elim (λ _ t ↦ Nat.zero_add _ ▸ t) (λ _ _ ↦ IterativeDomain.abort)
          | m + 1 =>
            Sum.elim (λ _ t ↦ IterativeDomain.lift (by grind only) t) <|
            Sum.elim (λ _ _ ↦ IterativeDomain.abort) <|
            λ g t ↦ reorder ▸ IterativeDomain.branch λ σ ↦ Branch.seq t '' g σ
      end

      theorem IterativeDomain.seq_leaf [DecidableEq Γ] {v} {m n} {q : (IterativeDomain «Σ» Γ α PUnit n).carrier} :
          IterativeDomain.seq zero (leaf (n := m) v) q = IterativeDomain.lift (Nat.le_add_left _ _) q := by
        cases m with unfold seq
        | zero =>
          rw! [Nat.zero_add, lift_refl]
          rfl
        | succ n =>
          rfl

      theorem IterativeDomain.seq_abort [DecidableEq Γ] {m n} {q : (IterativeDomain «Σ» Γ α PUnit n).carrier} :
          IterativeDomain.seq zero (abort (n := m)) q = abort := by
        cases m with unfold seq
        | zero =>
          rw! [Nat.zero_add]
          rfl
        | succ n =>
          rfl

      theorem IterativeDomain.seq_branch [DecidableEq Γ] {m n} {g : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α PUnit m).carrier)} {q : (IterativeDomain «Σ» Γ α PUnit n).carrier} :
          seq zero (branch g) q = reorder ▸ branch λ σ ↦ Branch.seq zero q '' g σ := by
        unfold seq
        rfl

      theorem Branch.seq_recv [DecidableEq Γ] {m n} {c : Γ} {π : α →ᵤ Bool →ᵤ Restriction (IterativeDomain «Σ» Γ α PUnit m).carrier unitInterval.half} {q : (IterativeDomain «Σ» Γ α PUnit n).carrier} :
          Branch.seq zero q (Branch.recv c π) = Branch.recv c λ v ok ↦ (Restriction.map (IterativeDomain.seq zero · q) (π v ok)) := by
        unfold seq
        rfl

      theorem Branch.seq_send [DecidableEq Γ] {m n} {c : Γ} {v : α} {p : Restriction (IterativeDomain «Σ» Γ α PUnit m).carrier unitInterval.half} {q : (IterativeDomain «Σ» Γ α PUnit n).carrier} :
          Branch.seq zero q (Branch.send c v p) = Branch.send c v (Restriction.map (IterativeDomain.seq zero · q) p) := by
        unfold seq
        rfl

      theorem Branch.seq_close [DecidableEq Γ] {m n} {c : Γ} {p : Restriction (IterativeDomain «Σ» Γ α PUnit m).carrier unitInterval.half} {q : (IterativeDomain «Σ» Γ α PUnit n).carrier} :
          Branch.seq zero q (Branch.close c p) = Branch.close c (Restriction.map (IterativeDomain.syncClose zero c <| IterativeDomain.seq zero · q) p) := by
        unfold seq
        rfl

      theorem Branch.seq_sync [DecidableEq Γ] {m n} {c : Γ} {p : Restriction (IterativeDomain «Σ» Γ α PUnit m).carrier unitInterval.half} {q : (IterativeDomain «Σ» Γ α PUnit n).carrier} :
          Branch.seq zero q (Branch.sync c p) = Branch.sync c (Restriction.map (IterativeDomain.seq zero · q) p) := by
        unfold seq
        rfl

      theorem Branch.seq_next [DecidableEq Γ] {m n} {σ : «Σ»} {p : Restriction (IterativeDomain «Σ» Γ α PUnit m).carrier unitInterval.half} {q : (IterativeDomain «Σ» Γ α PUnit n).carrier} :
          Branch.seq zero q (Branch.next σ p) = Branch.next σ (Restriction.map (IterativeDomain.seq zero · q) p) := by
        unfold seq
        rfl

      mutual
        theorem Branch.seq_eq_app [DecidableEq Γ] {m n} {b : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α PUnit m).carrier} {q : (IterativeDomain «Σ» Γ α PUnit n).carrier} :
            Branch.seq zero q b = (Branch.ap zero q ∘ Branch.map (IterativeDomain.map (β' := PUnit.{x + 1} →ᵤ PUnit.{x + 1}) (λ _ _ ↦ PUnit.unit))) b := by
          cases b using Branch.casesOn with
            unfold Function.comp
          | recv c π =>
            rw [Branch.map_recv, Branch.seq_recv, Branch.ap_recv]
            conv_rhs => enter [2, v, ok]; rw [Restriction.map_map, Function.comp_def]
            congr 2 with v ok : 2
            congr 1 with p : 1
            apply IterativeDomain.seq_eq_app
          | send c v p =>
            rw [Branch.map_send, Branch.seq_send, Branch.ap_send]
            conv_rhs => rw [Restriction.map_map, Function.comp_def]
            congr 2 with p : 1
            apply IterativeDomain.seq_eq_app
          | close c p =>
            rw [Branch.map_close, Branch.seq_close, Branch.ap_close]
            conv_rhs => rw [Restriction.map_map, Function.comp_def]
            congr 2 with p : 1
            congr 1
            apply IterativeDomain.seq_eq_app
          | sync c p =>
            rw [Branch.map_sync, Branch.seq_sync, Branch.ap_sync]
            conv_rhs => rw [Restriction.map_map, Function.comp_def]
            congr 2 with p : 1
            apply IterativeDomain.seq_eq_app
          | next σ p =>
            rw [Branch.map_next, Branch.seq_next, Branch.ap_next]
            conv_rhs => rw [Restriction.map_map, Function.comp_def]
            congr 2 with p : 1
            apply IterativeDomain.seq_eq_app

        theorem IterativeDomain.seq_eq_app [DecidableEq Γ] {m n} {p : (IterativeDomain «Σ» Γ α PUnit m).carrier} {q : (IterativeDomain «Σ» Γ α PUnit n).carrier} :
            IterativeDomain.seq zero p q = IterativeDomain.ap zero (IterativeDomain.map (β' := PUnit.{x + 1} →ᵤ PUnit.{x + 1}) (λ _ _ ↦ PUnit.unit) p) q := by
          match m, p with
          | 0, IterativeDomain.leaf v | m + 1, IterativeDomain.leaf v =>
            rw [IterativeDomain.map_leaf, IterativeDomain.ap_leaf, IterativeDomain.seq_leaf, IterativeDomain.map_id]
          | 0, IterativeDomain.abort | m + 1, IterativeDomain.abort =>
            rw [IterativeDomain.map_abort, IterativeDomain.ap_abort, IterativeDomain.seq_abort]
          | m + 1, IterativeDomain.branch f =>
            rw [IterativeDomain.map_branch, IterativeDomain.ap_branch, IterativeDomain.seq_branch]
            congr 2 with σ : 1
            rw [← Set.image_comp]
            congr 1 with b : 1
            apply Branch.seq_eq_app
      end

      theorem IterativeDomain.seq_uniform_continuous [DecidableEq Γ] {m n} :
          UniformContinuous₂ (IterativeDomain.seq zero («Σ» := «Σ») (m := m) (n := n)) := by
        conv => enter [1, p, q]; rw [IterativeDomain.seq_eq_app]
        change UniformContinuous₂ (_ ∘ _)
        apply UniformContinuous₂.bicompl
        · apply IterativeDomain.ap.uniform_continuous₂
        · apply IterativeDomain.map_uniformContinuous
          apply uniformContinuous_const
        · exact uniformContinuous_id

      def DomainUnion.seq [DecidableEq Γ] : DomainUnion «Σ» Γ α PUnit → DomainUnion «Σ» Γ α PUnit → DomainUnion «Σ» Γ α PUnit :=
        λ ⟨_, p⟩ ⟨_, q⟩ ↦ DomainUnion.mk (IterativeDomain.seq zero p q)

      open Function in
      theorem DomainUnion.seq_uniform_continuous [DecidableEq Γ] :
          UniformContinuous₂ (DomainUnion.seq zero («Σ» := «Σ»)) := by
        -- change UniformContinuous₂ (Function.bicompr DomainUnion.mk (Function.bicompl (IterativeDomain.seq zero) Sigma.snd Sigma.snd))

        admit

      /-- Restricted form of sequential composition where all leaves are replaced with the same subtree. -/
      def Domain.seq [DecidableEq Γ] : Domain «Σ» Γ α PUnit → Domain «Σ» Γ α PUnit → Domain «Σ» Γ α PUnit :=
        UniformSpace.Completion.extension₂ (λ x y ↦ DomainUnion.seq zero x y)

      @[inherit_doc Domain.seq]
      def Domain.seq' [DecidableEq Γ] [inst : HasDefaultInit Γ α] : Domain «Σ» Γ α PUnit → Domain «Σ» Γ α PUnit → Domain «Σ» Γ α PUnit :=
        flip (Domain.seq inst.zero)
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

      /-- Non-deterministic choice, aka tree union. -/
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
          λ (σ, p) ↦ {Branch.next σ ⟨IterativeDomain.hide c Ω p.val⟩}

        def IterativeDomain.hide [DecidableEq Γ] (c : Γ) (Ω : Set Γ) {n} : (IterativeDomain «Σ» Γ α β n).carrier → (IterativeDomain «Σ» Γ α β n).carrier :=
          match n with
          | 0 => id
          | n + 1 =>
            Sum.map id <|
            Sum.map id <|
            Pi.map λ σ X ↦
              let Y := ⋃ b ∈ X, Branch.hide σ c Ω b
              Y ∪ if Y = ∅ ∧ X ≠ ∅ then {Branch.next σ ⟨IterativeDomain.abort⟩} else ∅
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

      /-- Remove branches that mention the synchronous channel `c`, or channels in `Ω`. -/
      def Domain.hide' [DecidableEq Γ] [inst : HasDefaultInit Γ α] (c : Γ) (Ω : Set Γ) : Domain «Σ» Γ α β → Domain «Σ» Γ α β :=
        Domain.hide inst.zero c Ω
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
            ∪ {p | ∃ v γ p' π', .send γ v ⟨p'⟩ ∈ g σ ∧ .recv γ π' ∈ g' σ ∧ p = .sync γ ⟨IterativeDomain.lift (by grind only) (IterativeDomain.parallel p' (π' v true).val)⟩}
            ∪ {p | ∃ v γ p' π', .send γ v ⟨p'⟩ ∈ g' σ ∧ .recv γ π' ∈ g σ ∧ p = .sync γ ⟨IterativeDomain.lift (by grind only) (IterativeDomain.parallel (π' v true).val p')⟩}
            -- Channel closure
            ∪ {p | ∃ v γ p' p'', .send γ v ⟨p'⟩ ∈ g σ ∧ .close γ ⟨p''⟩ ∈ g' σ ∧ p = .next σ ⟨IterativeDomain.abort⟩}
            ∪ {p | ∃ v γ p' p'', .send γ v ⟨p'⟩ ∈ g' σ ∧ .close γ ⟨p''⟩ ∈ g σ ∧ p = .next σ ⟨IterativeDomain.abort⟩}
            ∪ {p | ∃ γ π' p', .recv γ π' ∈ g σ ∧ .close γ ⟨p'⟩ ∈ g' σ ∧ p = .close γ ⟨IterativeDomain.lift (by grind only) (IterativeDomain.parallel (π' (zero γ) false).val p')⟩}
            ∪ {p | ∃ γ π' p', .recv γ π' ∈ g' σ ∧ .close γ ⟨p'⟩ ∈ g σ ∧ p = .close γ ⟨IterativeDomain.lift (by grind only) (IterativeDomain.parallel p' (π' (zero γ) false).val)⟩}
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

      /-- Parallel composition. Generates all the possible interleavings as well as synchronizations. -/
      def Domain.parallel' [inst : HasDefaultInit Γ α] : Domain «Σ» Γ α β → Domain «Σ» Γ α γ → Domain «Σ» Γ α (β × γ) :=
        Domain.parallel inst.zero
    end Parallel
  end Operators

  section
    @[inherit_doc]
    scoped[Domain] infixr:100 " <$> " => Domain.map

    @[inherit_doc]
    scoped[Domain] infixl:65 " ⊖ " => Domain.syncClose'

    @[inherit_doc]
    scoped[Domain] infixr:60 " <*> " => Domain.ap'

    @[inherit_doc]
    scoped[Domain] infixl:55 " >>= " => Domain.bind

    @[inherit_doc]
    scoped[Domain] infixl:60 " ⬰ " => Domain.seq'

    @[inherit_doc]
    scoped[Domain] infixl:65 " ⊻ " => Domain.choice

    @[inherit_doc]
    scoped[Domain] notation:50 p:51 " ∖[" Ω:0 "] " c:50 => Domain.hide' c Ω p

    @[inherit_doc]
    scoped[Domain] infixl:60 " ∥ " => Domain.parallel'
  end



  namespace Value
    variable
      {«Σ» : Type u} {Γ : Type v} {α : Type w} {β : Type x} {γ : Type y} {δ : Type z}
      [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α] [IMetricSpace β] [IMetricSpace γ]
    variable (Γ «Σ»)
    variable (ℍ : Type y) (Typ : Type w) [IMetricSpace ℍ] [IMetricSpace Typ]

    protected abbrev F (𝕍 : Type x) [IMetricSpace 𝕍] : Type (max u v w x y) :=
      -- bool
        Bool
      -- int
      ⊕ ℤ
      -- str
      ⊕ String
      -- slice
      ⊕ ℕ × ℕ × ℕ × ℍ
      -- chan
      ⊕ ℕ × Typ × ℍ × ℍ
      -- struct
      ⊕ (String →ᵤ Option ℍ)
      -- array
      ⊕ ℕ × (ℕ →ᵤ Option ℍ)
      -- map
      ⊕ (Restriction 𝕍 unitInterval.half →ᵤ Option ℍ) × Bool
      -- func
      ⊕ (String →ᵤ Option ℍ) × (List (Restriction 𝕍 unitInterval.half) × List Γ × (String → Option Γ) →ᵤ Domain «Σ» Γ 𝕍 (Restriction 𝕍 unitInterval.half))
      -- tuples
      ⊕ List (Restriction 𝕍 unitInterval.half)

    variable {«Σ» Γ ℍ Typ}

    instance {𝕍 : Type u} [IMetricSpace 𝕍] : IMetricSpace (Value.F «Σ» Γ ℍ Typ 𝕍) :=
      inferInstance

    /-!
      `𝕍` is constructed similarly to `Domain`.
      This is painful, and we know that it will work.

      For now, let's just axiomatize `𝕍`. We know it exists (from various results
      of domain theory), we just don't construct them yet.
      `𝕍` is just very cumbersome to define and construct. We'll leave this as
      future work for now.
    -/
    axiom 𝕍 («Σ» : Type u) (Γ : Type v) (ℍ : Type w) (Typ : Type x) : NonemptyType.{max u v w x}

    instance : Nonempty (𝕍 «Σ» Γ ℍ Typ).type := (𝕍 ..).property

    @[instance]
    axiom 𝕍_metricSpace : IMetricSpace (𝕍 «Σ» Γ ℍ Typ).type

    /--
      Axiomatize the fact that `𝕍` is a solution to the recursive domain
      equation `𝕍 = F(𝕍)`.
    -/
    axiom 𝕍_iso : (𝕍 «Σ» Γ ℍ Typ).type ≃ᵢ Value.F «Σ» Γ ℍ Typ (𝕍 «Σ» Γ ℍ Typ).type

    @[instance]
    axiom 𝕍_complete : CompleteSpace (𝕍 «Σ» Γ ℍ Typ).type



    def 𝕍.bool (b : Bool) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inl b)

    def 𝕍.int (n : ℤ) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inl n)

    def 𝕍.str (s : String) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inl s)

    def 𝕍.slice (cap low high : ℕ) (array : ℍ) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inl ⟨cap, low, high, array⟩)

    def 𝕍.chan (length : ℕ) (τ : Typ) (array closed : ℍ) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inl ⟨length, τ, array, closed⟩)

    def 𝕍.struct (fields : String →ᵤ Option ℍ) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inr <| .inl fields)

    def 𝕍.array (len : ℕ) (indices : ℕ →ᵤ Option ℍ) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨len, indices⟩)

    def 𝕍.map (maps : (𝕍 «Σ» Γ ℍ Typ).type →ᵤ Option ℍ) (isNil : Bool) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨maps ∘ Restriction.val, isNil⟩)

    def 𝕍.func (closure : String →ᵤ Option ℍ) (call : List (𝕍 «Σ» Γ ℍ Typ).type × List Γ × (String → Option Γ) →ᵤ Domain «Σ» Γ (𝕍 «Σ» Γ ℍ Typ).type (𝕍 «Σ» Γ ℍ Typ).type) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨closure, λ ⟨vs, ξ, ς⟩ ↦ call ⟨vs.map Restriction.val, ξ, ς⟩ |>.map Restriction.mk⟩)

    def 𝕍.tuple (vs : List (𝕍 «Σ» Γ ℍ Typ).type) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr vs)


    @[cases_eliminator]
    noncomputable def 𝕍.casesOn {motive : (𝕍 «Σ» Γ ℍ Typ).type → Sort _}
      (bool : ∀ b, motive (𝕍.bool b))
      (int : ∀ n, motive (𝕍.int n))
      (str : ∀ s, motive (𝕍.str s))
      (slice : ∀ cap low high array, motive (𝕍.slice cap low high array))
      (chan : ∀ len τ array closed, motive (𝕍.chan len τ array closed))
      (struct : ∀ fields, motive (𝕍.struct fields))
      (array : ∀ len indices, motive (𝕍.array len indices))
      (map : ∀ maps isNil, motive (𝕍.map maps isNil))
      (func : ∀ closure call, motive (𝕍.func closure call))
      (tuple : ∀ vs : List (𝕍 «Σ» Γ ℍ Typ).type, motive (𝕍.tuple vs))
      (v : (𝕍 «Σ» Γ ℍ Typ).type) :
        motive v :=
      match h : 𝕍_iso v with
      | .inl b =>
        have h' : v = 𝕍.bool b := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ bool b
      | .inr (.inl n) =>
        have h' : v = 𝕍.int n := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ int n
      | .inr (.inr (.inl s)) =>
        have h' : v = 𝕍.str s := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ str s
      | .inr (.inr (.inr (.inl ⟨cap, low, high, array⟩))) =>
        have h' : v = 𝕍.slice cap low high array := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ slice cap low high array
      | .inr (.inr (.inr (.inr (.inl ⟨length, τ, array, closed⟩)))) =>
        have h' : v = 𝕍.chan length τ array closed := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ chan length τ array closed
      | .inr (.inr (.inr (.inr (.inr (.inl fields))))) =>
        have h' : v = 𝕍.struct fields := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ struct fields
      | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨len, indices⟩)))))) =>
        have h' : v = 𝕍.array len indices := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ array len indices
      | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨maps, isNil⟩))))))) =>
        have h' : v = 𝕍.map (maps ∘ Restriction.mk) isNil := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ map (maps ∘ Restriction.mk) isNil
      | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨closure, call⟩)))))))) =>
        have h' : v = 𝕍.func closure (λ ⟨vs, ξ, ς⟩ ↦ call ⟨vs.map Restriction.mk, ξ, ς⟩ |>.map Restriction.val) := by
          apply_fun 𝕍_iso.symm at h
          rw [IsometryEquiv.symm_apply_apply] at h
          rw [h, 𝕍.func]
          dsimp
          congr 11 with ⟨vs, ξ, ς⟩ : 1
          rw [List.map_map, Domain.map_map, Restriction.mk_comp_val_eq_id, List.map_id, Domain.map_id]
          · apply Restriction.val_uniformContinuous
          · apply Restriction.mk_uniformContinuous
        h' ▸ func closure (λ ⟨vs, ξ, ς⟩ ↦ call ⟨vs.map Restriction.mk, ξ, ς⟩ |>.map Restriction.val)
      | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr vs)))))))) =>
        have h' : v = 𝕍.tuple (List.map Restriction.val vs) := by
          apply_fun 𝕍_iso.symm at h
          rw [IsometryEquiv.symm_apply_apply] at h
          rw [h, 𝕍.tuple, ← List.map_eq_map, bind_map_left]
          simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_singleton']
        h' ▸ tuple (List.map Restriction.val vs)
  end Value
end Domain
