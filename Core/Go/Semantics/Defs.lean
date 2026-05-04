import Core.Go.Semantics.Domains
import Core.Go.Syntax
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
  Now that we have finished defining our domains…we can finally define the semantics of
  Go.
-/

open scoped UniformConvergence

theorem ENNReal.toReal_two : ENNReal.toReal 2 = 2 := rfl

open TypedSetTheory (Expression Typ)

abbrev Address := PUnit ⊕ PUnit ⊕ ℕ -- WithBot (WithTop ℕ)

abbrev nil : Address := .inl .unit
abbrev dummy : Address := .inr (.inl .unit)
instance : Coe ℕ Address := ⟨λ x ↦ .inr (.inr x)⟩

noncomputable instance : DiscreteIMetricSpace TypedSetTheory.Typ where
  __ := IMetricSpace.discrete
instance : CompleteSpace TypedSetTheory.Typ :=
  DiscreteIMetricSpace.completeSpace

def Channel := (ℕ × TypedSetTheory.Typ)
  deriving DecidableEq

noncomputable instance : DiscreteIMetricSpace Channel where
  __ := IMetricSpace.discrete
instance : CompleteSpace Channel := DiscreteIMetricSpace.completeSpace

-- TODO: this will need to be defined mutually with 𝕍
axiom Store.{u, v, w, x} : NonemptyType.{max u v w x}

instance : Nonempty Store.type := Store.property

@[instance]
axiom Store_metricspace : IMetricSpace Store.type

@[instance]
axiom Store_completespace : CompleteSpace Store.type

open Classical in
axiom Store_iso.{u, v, w, x} :
  Store.{u, v, w, x}.type ≃ᵢ (Address.{u, v} →ᵤ Option (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type) × List (String →ᵤ Option Address.{u, v})

-- structure Store where
--   /-- The main memory -/
--   ϙ : Address → Option (Value.𝕍 Store Channel Address Typ).type
--   /-- Scopes, i.e. a stack of bindings from variable names to addresses. -/
--   h : List (String → Option Address)
--   deriving Nonempty

noncomputable def Store.type.h : Store.type → Address → Option (Value.𝕍 Store.type Channel Address Typ).type :=
  Prod.fst ∘ ⇑Store_iso

noncomputable def Store.type.ϙ : Store.type → List (String → Option Address) :=
  Prod.snd ∘ ⇑Store_iso

open Classical in
noncomputable def Store.popϙ (σ : Store.type) : Option Store.type := match Store.type.ϙ σ with
  | [] => .none
  | _ :: ϙ => .some (⇑Store_iso.symm ⟨Store.type.h σ, ϙ⟩)

noncomputable def Store.deref (σ : Store.type) (addr : Address) : Option (Value.𝕍 Store.type Channel Address Typ).type :=
  Store.type.h σ addr

open Classical in
noncomputable def Store.update.{u, v, w, x} (σ : Store.{u, v, w, x}.type) (addr : Address.{u, v}) (v : (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type) : Option Store.{u, v, w, x}.type :=
  -- Check that the address is allocated
  Store.deref σ addr |>.bind λ _ ↦
    let h' := Function.update (Store.type.h σ) addr (.some v)
    pure (Store_iso.symm (h', Store.type.ϙ σ))


-- def Store.toProd (s : Store) : (Address → Option (Value.𝕍 Store Channel Address Typ)) × List (String → Option Address) :=
--   (s.ϙ, s.h)

-- theorem Store.toProd_injective : Function.Injective Store.toProd := by
--   rintro ⟨ϙx, hx⟩ ⟨ϙy, hy⟩ (_|_)
--   rfl

-- noncomputable instance : IMetricSpace Store :=
--   .induced _ Store.toProd_injective inferInstance

-- instance : CompleteSpace Store := by
--   apply IsUniformInducing.completeSpace (f := Store.toProd)
--   · solve_by_elim
--   ·
--     admit
--   -- Surely?

-- abbrev 𝔽.{u, v, w, x, y} :=
--   List (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type × List Channel.{w} × (String → Option Channel.{w}) → Domain Store.{u, v, w, x}.type Channel.{w} (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type PUnit.{y + 1}

noncomputable section
  open scoped Domain

  universe u v w x y

  /-! # Some helpers -/

  def boolean {α} (v : (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type) (default : α) (f : Bool → α) : α :=
    Value.𝕍.casesOn (motive := λ _ ↦ α)
      f
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ ↦ default)
      v

  def integer {α} (v : (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type) (default : α) (f : ℤ → α) : α :=
    Value.𝕍.casesOn (motive := λ _ ↦ α)
      (λ _ ↦ default)
      f
      (λ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ ↦ default)
      v

  def array {α} (v : (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type) (default : α)
    (f : (n : ℕ) → (Fin n →ᵤ Address.{u, v}) → α) :
      α :=
    Value.𝕍.casesOn (motive := λ _ ↦ α)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ ↦ default)
      f
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ ↦ default)
      v

  def channel {α} (v : (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type) (default : α)
    (async : Address.{u, v} → Typ → Address.{u, v} → Address.{u, v} → α) :
      α :=
    Value.𝕍.casesOn (motive := λ _ ↦ α)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      async
      (λ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ ↦ default)
      v

  /-! # The main semantics -/

  open Classical

  namespace TypedSetTheory.Expression
    protected def denotation (ξ : List Channel.{w}) (ς : String → Option Channel.{w}) : Expression.{y} Typ → Domain Store.{u, v, w, x}.type Channel.{w} (Value.Send𝕍 Address.{u, v} Typ.{x}) (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type
      | _ => sorry

    protected def denotations (ξ : List Channel) (ς : String → Option Channel) : List (Expression Typ) → Domain Store.type Channel (Value.Send𝕍 Address.{u, v} Typ.{x}) (List (Value.𝕍 Store.type Channel Address Typ).type)
      | [] => .pure []
      | e :: es => e.denotation ξ ς >>= λ v ↦ (v :: ·) <$> Expression.denotations ξ ς es
  end TypedSetTheory.Expression

  namespace GoCal
    namespace Statement
      variable (out : Channel)

      -- TODO: introduce another type of types?
      -- Because there are TLA+ types which don't mean anything in here, e.g. set vs seq
      private def zero (σ : Store.{u, v, w, x}.type) : Typ.{y} → Store.{u, v, w, x}.type × (Value.Send𝕍 Address.{u, v} Typ.{x})
        | .bool => (σ, .bool false)
        | .int => (σ, .int 0)
        | .str => (σ, .str "")
        | .function _ _ => (σ, .map [] true)
        | .set _ => sorry
        | .seq _ => sorry
        | .tuple _ => sorry
        | .operator _ _ => sorry
        | .var _ => sorry
        | .const _ => sorry
        | .record _ => sorry
        | .channel _ => sorry
        | .address => sorry

      instance : HasDefaultInit Store.type Channel (Value.Send𝕍 Address Typ) where
        zero c σ := zero σ (Prod.snd c)

      def guard (ξ : List Channel.{w}) (ς : String → Option Channel.{w}) (e : Expression.{y} Typ) : Domain Store.{u, v, w, x}.type Channel.{w} (Value.Send𝕍 Address.{u, v} Typ.{x}) PUnit.{y + 1} :=
        Expression.denotation ξ ς e >>= λ v ↦ Domain.branch λ σ ↦
          boolean v (default := {.next σ { val := .abort }})
            λ b ↦ if b then {.next σ { val := .pure .unit }} else ∅

      theorem guard.is_branch {ξ ς e} : ∃ f, guard ξ ς e = Domain.branch f := by
        -- by_contra! h
        -- unfold guard at h
        admit

      def deref (σ : Store.{u, v, w, x}.type) (addr : Address.{u, v}) : Domain Store.{u, v, w, x}.type Channel.{w} (Value.Send𝕍 Address.{u, v} Typ.{x}) (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type :=
        match Store.deref σ addr with
        | .some v => .pure v
        | .none => .abort

      private def while_seq_F (ξ : List Channel.{w}) (ς : String → Option Channel.{w}) (e : Expression Typ) (P' P : Domain Store.{u, v, w, x}.type Channel.{w} (Value.Send𝕍 Address.{u, v} Typ.{x}) PUnit.{y + 1}) :
          Domain Store.{u, v, w, x}.type Channel.{w} (Value.Send𝕍 Address.{u, v} Typ.{x}) PUnit.{y + 1} :=
        (P ⬰ P' ⬰ guard ξ ς e) ⊻ (.pure .unit ⬰ guard ξ ς (.prefix .«¬» e))

      private def while_seq (ξ : List Channel.{w}) (ς : String → Option Channel.{w}) (e : Expression Typ) (P : Domain Store.{u, v, w, x}.type Channel.{w} (Value.Send𝕍 Address.{u, v} Typ.{x}) PUnit.{y + 1}) :
          ℕ → Domain Store.{u, v, w, x}.type Channel.{w} (Value.Send𝕍 Address.{u, v} Typ.{x}) PUnit.{y + 1}
        | 0 => .branch λ σ ↦ {.next σ { val := .pure .unit }}
        | i + 1 => while_seq_F ξ ς e P (while_seq ξ ς e P i)

      protected def denotation (ξ : List Channel.{w}) (ς : String → Option Channel.{w}) : List (Statement.{y} Typ (Expression Typ) Typ.initArgs) → Domain Store.{u, v, w, x}.type Channel.{w} (Value.Send𝕍 Address.{u, v} Typ.{x}) PUnit.{y + 1}
        | [] => .branch λ σ ↦ {.next σ { val := .pure .unit }}
        | .panic e :: ss => Statement.denotation ξ ς ss ⬰ (Expression.denotation ξ ς e >>= λ _ ↦ .abort)
        | .return es :: ss => match ss with
          | [] => match ξ with
            | ret :: _ => Expression.denotations ξ ς es >>= λ vs ↦ .branch λ σ ↦ match Store.popϙ σ with
              | .none => {.next σ { val := .abort }}
              | .some σ => {.next σ {
                val := if h : ∀ v ∈ vs, Value.𝕍_isSend v then
                  .branch λ _ ↦ {.send ret (Value.𝕍_extract (Value.𝕍.tuple vs) (Value.𝕍_isSend.tuple h)) { val := .pure .unit }}
                else
                  .abort
              }}
            | [] => .branch λ σ ↦ {.next σ { val := .abort }}
          | _ => .branch λ σ ↦ {.next σ { val := .abort }}
        | .print e :: ss =>
          Statement.denotation ξ ς ss ⬰ (Expression.denotation ξ ς e >>= λ v ↦
            if h : Value.𝕍_isSend v then
              .branch λ _ ↦ {.send out (Value.𝕍_extract v h) { val := .pure .unit }}
            else
              .abort)
        -- make
        -- var
        | .if e S₁ S₂ :: ss =>
          Statement.denotation ξ ς ss ⬰ ((Statement.denotation ξ ς S₁ ⬰ guard ξ ς e) ⊻ (Statement.denotation ξ ς S₂ ⬰ guard ξ ς (.prefix .«¬» e)))
        | .while e S :: ss =>
          -- NOTE: we show in `while_seq_cauchy'` that the limit is actually defined
          Statement.denotation ξ ς ss ⬰ lim (Filter.atTop.map (while_seq ξ ς e (Statement.denotation ξ ς S)))
        -- close
        -- select
        -- switch
        | .go S :: ss => (λ _ ↦ PUnit.unit) <$> (Statement.denotation ξ ς S ∥ Statement.denotation ξ ς ss)
        | .send c e :: ss =>
          -- FIXME: need to explicitly check if `c` is a synchronous channel or not
          -- i.e. if it syntactically is some names bound in `ς`.
          Expression.denotation ξ ς e >>= λ v ↦
          Expression.denotation ξ ς c >>= λ c ↦
          Statement.denotation ξ ς ss ⬰ Domain.branch λ σ ↦
            channel c (default := {.next σ { val := .abort }})
              (λ len' τ buf closed? ↦
                match (Store.deref σ closed?).bind λ closed? ↦ (Store.deref σ len').bind λ len ↦ (Store.deref σ buf).bind λ buf ↦ pure (closed?, len, buf) with
                | .none => {.next σ { val := .abort }}
                | .some (closed?, len, buf) =>
                  boolean closed? (default := {.next σ { val := .abort }})
                    λ closed? ↦ integer len (default := {.next σ { val := .abort }})
                    λ len ↦ array buf (default := {.next σ { val := .abort }})
                    λ cap indices ↦
                      if h : closed? ∧ len ≥ 0 ∧ len < cap then
                        let i : Fin cap := ⟨len.toNat, propext (Int.toNat_lt h.2.1) ▸ h.2.2⟩
                        let σ' := Store.update σ (indices i) v |>.bind λ σ ↦ Store.update σ len' (Value.𝕍.int <| len + 1)
                        match σ' with
                        | .some σ' => {.next σ' { val := .pure .unit }}
                        | .none => {.next σ { val := .abort }}
                      else if closed? ∧ len ≥ cap then
                        ∅
                      else
                        {.next σ { val := .abort }}
              )
        -- recv
        | _ => sorry

        theorem while_seq_F_nonexpansive {ξ ς e q} :
            ∀ p p', edist (while_seq_F ξ ς e q p) (while_seq_F ξ ς e q p') ≤ (1/2) * edist p p' := by
          intros p p'
          repeat rw [Domain.edist_eq]

          have : 1 / 2 = ENNReal.ofReal (1 / 2) := by simp only [one_div, zero_lt_two, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_ofNat]
          rw [this, ← ENNReal.ofReal_mul (by norm_num)]
          apply ENNReal.ofReal_le_ofReal

          repeat rw [Domain.dist_eq]
          change idist _ _ ≤ unitInterval.half * idist _ _

          unfold while_seq_F
          apply le_trans Domain.choice_idist_le
          rw [idist_self, ← unitInterval.bot_eq, sup_bot_eq, Domain.seq'_assoc, Domain.seq'_assoc]

          obtain ⟨f, hf⟩ : ∃ f, (q ⬰ guard ξ ς e) = Domain.branch f := by
            obtain ⟨f', hf'⟩ := guard.is_branch (ξ := ξ) (ς := ς) (e := e)
            apply Domain.seq'_is_branch_of_branch
            exact hf'

          rw [hf]
          apply Domain.seq'_branch_contracting_left

        theorem while_seq_F_contracting {ξ ς e q} : ContractingWith (1/2) (while_seq_F ξ ς e q) := by
          constructor
          · exact one_half_lt_one
          · intros p p'

            have : ENNReal.ofNNReal (1 / 2) = 1 / 2 := by norm_num
            rw [this]

            exact while_seq_F_nonexpansive p p'

        theorem while_seq_eq {ξ ς e S n} :
            while_seq.{u, v, w, x, y} ξ ς e (Statement.denotation out ξ ς S) n =
            (while_seq_F.{u, v, w, x, y} ξ ς e (Statement.denotation out ξ ς S))^[n] (Domain.branch λ σ ↦ {.next σ { val := .pure .unit }}) := by
          induction n with
          | zero => rfl
          | succ n IH =>
            unfold while_seq
            rw [IH, Nat.add_comm, Function.iterate_add, Function.iterate_one]
            rfl

        theorem while_seq_cauchy (ξ : List Channel.{w}) (ς : String → Option Channel.{w}) (e : Expression.{y} Typ) (S : List (Statement.{y} Typ (Expression Typ) Typ.initArgs)) :
            CauchySeq (while_seq.{u, v, w, x, y} ξ ς e (Statement.denotation out ξ ς S)) := by
          set p₀ : Domain.{max u v w x, w, max u v x, y} Store.{u, v, w, x}.type Channel.{w} (Value.Send𝕍 Address.{u, v} Typ.{x}) PUnit.{y + 1} :=
            Domain.branch λ σ ↦ {.next σ { val := .pure .unit }}

          have edist_ne_top : edist p₀ (while_seq_F.{u, v, w, x, y} ξ ς e (Statement.denotation out ξ ς S) p₀) ≠ ⊤ := by
            rw [Domain.edist_eq]
            exact ENNReal.ofReal_ne_top

          obtain ⟨q, q_fixed_point, tendsto_nhds, dist_le⟩ := while_seq_F_contracting.exists_fixedPoint p₀ edist_ne_top
          conv at tendsto_nhds =>
            enter [1, n]; rw [← while_seq_eq]
          exact Filter.Tendsto.cauchySeq tendsto_nhds

        theorem while_seq_cauchy' (ξ : List Channel.{w}) (ς : String → Option Channel.{w}) (e : Expression.{y} Typ) (S : List (Statement.{y} Typ (Expression Typ) Typ.initArgs)) :
            ∃ p, lim (Filter.atTop.map (while_seq ξ ς e (Statement.denotation out ξ ς S))) = p := by
          apply Exists.imp
          · intros p
            apply Filter.Tendsto.limUnder_eq
          · apply cauchySeq_tendsto_of_complete
            apply while_seq_cauchy
    end Statement
  end GoCal
end
