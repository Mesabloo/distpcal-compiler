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
import Extra.Topology.Constructions.SumProd
import Extra.Topology.Constructions.Maps
import Extra.Topology.IMetricSpace.Constructions
import Extra.Topology.ClosedEmbedding

class abbrev CompleteIMetricSpace (α : Type _) := IMetricSpace α, CompleteSpace α

structure Object.{u} where
  carrier : Type u
  [completeMetricSpace : CompleteIMetricSpace carrier]

instance {o : Object} : CompleteIMetricSpace o.carrier := o.completeMetricSpace

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

  variable [Nonempty «Σ»] [Nonempty α] [CompleteIMetricSpace β] [CompleteIMetricSpace «Σ»] [CompleteIMetricSpace Γ] [CompleteIMetricSpace α]

  open TopologicalSpace (Closeds)

  instance : IMetricSpace PUnit.{u + 1} := .of_metric_space_of_dist_le_one

  -- set_option pp.explicit true in
  private def IterativeDomain : ℕ → Object.{max u v w x}
    | 0 => { carrier := β ⊕ PUnit.{max u v w + 1} }
    | n + 1 => { carrier := β ⊕ PUnit.{u + 1} ⊕ («Σ» → Closeds (Branch «Σ» Γ α (IterativeDomain n).carrier)) }

  def DomainUnion : Object where
    carrier := Σ n, (IterativeDomain «Σ» Γ α β n).carrier

  abbrev Domain := UniformSpace.Completion (DomainUnion «Σ» Γ α β).carrier

  instance : MetricSpace (Domain «Σ» Γ α β) :=
    UniformSpace.Completion.instMetricSpace

  instance : CompleteSpace (Domain «Σ» Γ α β) :=
    UniformSpace.Completion.completeSpace _

  variable {«Σ» Γ α β γ δ} [CompleteIMetricSpace γ]

  @[match_pattern]
  def IterativeDomain.abort {n} : (IterativeDomain «Σ» Γ α β n).carrier := match n with
    | 0 => .inr .unit
    | _ + 1 => .inr (.inl .unit)

  @[match_pattern]
  def IterativeDomain.branch {n} (f : «Σ» → Closeds (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)) :
      (IterativeDomain «Σ» Γ α β (n + 1)).carrier :=
    .inr <| .inr f

  section Operators
    section Functor
      /-! ## Functor -/

      def Branch.map {γ'} [CompleteIMetricSpace γ'] (g : γ → γ') :
          (Branch «Σ» Γ α γ) → (Branch «Σ» Γ α γ') :=
        Sum.map (Prod.map id (Pi.map λ _ ↦ Pi.map λ _ ↦ Restriction.map g)) <|
        Sum.map (Prod.map id (Prod.map id (Restriction.map g))) <|
        Sum.map (Prod.map id (Restriction.map g)) <|
        Sum.map (Prod.map id (Restriction.map g)) <|
                (Prod.map id (Restriction.map g))

      def IterativeDomain.map {β'} [CompleteIMetricSpace β'] (f : β → β') {n} :
          (IterativeDomain «Σ» Γ α β n).carrier → (IterativeDomain «Σ» Γ α β' n).carrier := match n with
        | 0 => Sum.map f id
        | _ + 1 =>
          Sum.map f <|
          Sum.map id <|
          Pi.map λ _ ↦ Closeds.closed_map (Branch.map (IterativeDomain.map f))

      theorem DomainUnion.map.uniform_continuous {β'} [CompleteIMetricSpace β'] (f : β → β') :
          UniformContinuous (Sigma.map id λ _ ↦ IterativeDomain.map f : _ → (DomainUnion «Σ» Γ α _).carrier) := by
        admit

      def Domain.map {β'} [CompleteIMetricSpace β'] (f : β → β') :
          Domain «Σ» Γ α β → Domain «Σ» Γ α β' :=
        UniformSpace.Completion.map <| Sigma.map id λ _ ↦ IterativeDomain.map f
    end Functor

    section Lift
      /-! ## Lifting depth of trees -/

      def IterativeDomain.lift {m n} (h : m ≤ n := by linarith) :
          (IterativeDomain «Σ» Γ α β m).carrier → (IterativeDomain «Σ» Γ α β n).carrier :=
        sorry
    end Lift

    section Close
      /-! ## Channel closure -/

      variable (zero : Γ → α)

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
          | n + 1 => Sum.map id (Sum.map id (Pi.map λ σ ↦ Closeds.closed_map (Branch.syncClose c σ)))
      end

      theorem DomainUnion.syncClose.uniform_continuous [DecidableEq Γ] {c : Γ} :
          UniformContinuous (Sigma.map id λ n ↦ IterativeDomain.syncClose zero c : _ → (DomainUnion «Σ» _ α β).carrier) := by
        admit

      def Domain.syncClose [DecidableEq Γ] (c : Γ) : Domain «Σ» Γ α β → Domain «Σ» Γ α β :=
        UniformSpace.Completion.map <| Sigma.map id λ _ ↦ IterativeDomain.syncClose zero c
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
                (λ g t ↦ IterativeDomain.branch λ σ ↦ Closeds.closed_map (Branch.ap t) (g σ)))
      end

      theorem DomainUnion.IterativeDomain.ap.uniform_continuous [DecidableEq Γ] [Nonempty β] {m} {p : (IterativeDomain «Σ» Γ α (β → γ) m).carrier} :
          UniformContinuous (Sigma.map (m + ·) λ _ ↦ IterativeDomain.ap zero p : _ → (DomainUnion «Σ» Γ α γ).carrier) := by
        admit

      theorem DomainUnion.IterativeUnion.ap.uniform_continuous₂ [DecidableEq Γ] [Nonempty β] :
          UniformContinuous (λ ⟨m, p⟩ ↦ UniformSpace.Completion.map (Sigma.map (m + ·) λ _ ↦ IterativeDomain.ap zero p) : (DomainUnion «Σ» Γ α (β → γ)).carrier → _ → Domain «Σ» Γ α γ) := by
        admit

      def Domain.ap [DecidableEq Γ] [Nonempty β] :
          Domain «Σ» Γ α (β → γ) → Domain «Σ» Γ α β → Domain «Σ» Γ α γ :=
        UniformSpace.Completion.extension λ ⟨m, p⟩ ↦ UniformSpace.Completion.map (Sigma.map (m + ·) λ _ ↦ IterativeDomain.ap zero p)
    end Applicative

    section Monad
      /-! ## Monad -/

      -- def Domain.bind
    end Monad
  end Operators
end Domain
