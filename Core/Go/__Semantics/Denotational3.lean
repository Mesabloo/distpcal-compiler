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

class abbrev CompleteIMetricSpace (α : Type _) := IMetricSpace α, CompleteSpace α

structure Object.{u} where
  carrier : Type u
  [MetricSpace : IMetricSpace carrier]

instance {o : Object} : IMetricSpace o.carrier := o.MetricSpace

noncomputable section Domain
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

    instance Branch.instCompleteSpace [Nonempty α] [CompleteIMetricSpace «Σ»] [CompleteIMetricSpace Γ] [CompleteIMetricSpace α] [CompleteIMetricSpace γ] :
        CompleteSpace (Branch «Σ» Γ α γ) :=
      inferInstanceAs (CompleteSpace (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _))
  end Branch

  variable [Nonempty «Σ»] [Nonempty α] [IMetricSpace β] [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α]

  open TopologicalSpace (Closeds)

  instance : IMetricSpace PUnit.{u + 1} := .of_metric_space_of_dist_le_one

  -- set_option pp.explicit true in
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

    @[match_pattern]
    def IterativeDomain.abort {n} : (IterativeDomain «Σ» Γ α β n).carrier := match n with
      | 0 => .inr .unit
      | _ + 1 => .inr (.inl .unit)

    @[match_pattern]
    def IterativeDomain.branch {n} (f : «Σ» → Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)) :
        (IterativeDomain «Σ» Γ α β (n + 1)).carrier :=
      .inr <| .inr f

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
  end

  abbrev Domain := UniformSpace.Completion (DomainUnion «Σ» Γ α β)

  -- example : MetricSpace (Domain «Σ» Γ α β) := inferInstance
  example : CompleteSpace (Domain «Σ» Γ α β) := inferInstance

  theorem _root_.UniformSpace.Completion.dist_le_iff {α} [PseudoMetricSpace α] {ε}
    (h : ∀ x y : α, dist x y ≤ ε) :
      ∀ x y : UniformSpace.Completion α, dist x y ≤ ε := by
    intros x y
    apply UniformSpace.Completion.induction_on₂ (p := (dist · · ≤ ε)) x y
    · exact isClosed_le continuous_dist continuous_const
    · intro a b
      simp only [UniformSpace.Completion.dist_eq, h]

  instance : IMetricSpace (Domain «Σ» Γ α β) :=
    .of_metric_space_of_dist_le_one <|
      UniformSpace.Completion.dist_le_iff λ x y ↦ unitInterval.le_one (idist x y)

  variable {«Σ» Γ α β γ δ} [IMetricSpace γ]

  /--
    We establish the equivalence in order to prove that our defined domain is a solution
    to the original equation.
  -/
  private def Domain.isSolution :
      Domain «Σ» Γ α β ≃ β ⊕ PUnit ⊕ («Σ» → Closeds (Branch «Σ» Γ α (Domain «Σ» Γ α β))) where
    toFun x := sorry
    invFun x := sorry
    left_inv := sorry
    right_inv := sorry

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
        UniformSpace.Completion.map <| DomainUnion.syncClose («Σ» := «Σ») (β := β) zero c
    end Close

    section Applicative
      /-! ## Applicative functor -/

      variable (zero : Γ → α)

      private lemma reorder {m n : ℕ} : m + 1 + n = m + n + 1 := by
        simp +arith only

      def IterativeDomain.pure {n} (v : β) : (IterativeDomain «Σ» Γ α β n).carrier := match n with
        | 0 | _ + 1 => .inl v

      def Domain.pure (v : β) : Domain «Σ» Γ α β :=
        UniformSpace.Completion.coe' ⟨0, IterativeDomain.pure v⟩

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
        UniformSpace.Completion.extension₂ (λ x y ↦ DomainUnion.ap zero («Σ» := «Σ») (β := β) (γ := γ) x y : _ → _ → UniformSpace.Completion _)
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
  end Operators
end Domain
