import Core.Go.Semantics.Domains
import Core.Go.Syntax
import Mathlib.Analysis.SpecificLimits.Basic

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

instance : IMetricSpace TypedSetTheory.Typ where
  idist := sorry
  idist_self := sorry
  idist_comm := sorry
  idist_triangle := sorry
  eq_of_idist_eq_zero := sorry
instance : CompleteSpace TypedSetTheory.Typ where
  complete := by
    admit

def Channel := (ℕ × TypedSetTheory.Typ)
  deriving DecidableEq

-- noncomputable instance : PseudoIMetricSpace Channel :=
--   inferInstanceAs (PseudoIMetricSpace (ℕ × TypedSetTheory.Typ))
noncomputable instance : IMetricSpace Channel :=
  inferInstanceAs (IMetricSpace (ℕ × TypedSetTheory.Typ))
instance : CompleteSpace Channel :=
  inferInstanceAs (CompleteSpace (ℕ × TypedSetTheory.Typ))

-- TODO: this will need to be defined mutually with 𝕍
axiom Store.{u, v, w, x} : NonemptyType.{max u v w x}

instance : Nonempty Store.type := Store.property

@[instance]
axiom Store_metricspace : IMetricSpace Store.type

@[instance]
axiom Store_completespace : CompleteSpace Store.type

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

noncomputable def Store.popϙ (σ : Store.type) : Option Store.type := match Store.type.ϙ σ with
  | [] => .none
  | _ :: ϙ => .some (⇑Store_iso.symm ⟨Store.type.h σ, ϙ⟩)

noncomputable def Store.deref (σ : Store.type) (addr : Address) : Option (Value.𝕍 Store.type Channel Address Typ).type :=
  Store.type.h σ addr

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
      (λ _ ↦ default)
      v

  def channel {α} (v : (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type) (default : α)
    (sync : Channel.{w} → α) (async : Address.{u, v} → Typ → Address.{u, v} → Address.{u, v} → α) :
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
      sync
      v

  /-! # The main semantics -/

  namespace TypedSetTheory.Expression
    protected def denotation (ξ : List Channel.{w}) (ς : String → Option Channel.{w}) : Expression.{y} Typ → Domain Store.{u, v, w, x}.type Channel.{w} (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type
      | _ => sorry

    protected def denotations (ξ : List Channel) (ς : String → Option Channel) : List (Expression Typ) → Domain Store.type Channel (Value.𝕍 Store.type Channel Address Typ).type (List (Value.𝕍 Store.type Channel Address Typ).type)
      | [] => .pure []
      | e :: es => e.denotation ξ ς >>= λ v ↦ (v :: ·) <$> Expression.denotations ξ ς es
  end TypedSetTheory.Expression

  namespace GoCal
    namespace Statement
      variable (out : Channel)

      private def zero : Typ.{y} → (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type
        | .bool => sorry
        | .int => sorry
        | .str => sorry
        | .function _ _ => sorry
        | .set _ => sorry
        | .seq _ => sorry
        | .tuple _ => sorry
        | .operator _ _ => sorry
        | .var _ => sorry
        | .const _ => sorry
        | .record _ => sorry
        | .channel _ => sorry
        | .address => sorry

      instance : HasDefaultInit Channel (Value.𝕍 Store.type Channel Address Typ).type where
        zero := zero ∘ Prod.snd

      def guard (ξ : List Channel.{w}) (ς : String → Option Channel.{w}) (e : Expression.{y} Typ) : Domain Store.{u, v, w, x}.type Channel.{w} (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type PUnit.{y + 1} :=
        Expression.denotation ξ ς e >>= λ v ↦ Domain.branch λ σ ↦
          boolean v (default := {.next σ { val := .abort }})
            λ b ↦ if b then {.next σ { val := .pure .unit }} else ∅

      def deref (σ : Store.{u, v, w, x}.type) (addr : Address.{u, v}) : Domain Store.{u, v, w, x}.type Channel.{w} (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type :=
        match Store.deref σ addr with
        | .some v => .pure v
        | .none => .abort

      mutual
        -- TODO: there is some way to remove that `mutual` dependency, by abstracting over
        -- some `Domain` rather than the list of statements `S`.
        -- But is it worth it? Can be establish that `while_seq` is a Cauchy sequence irrespective
        -- of how `S` is reduced?
        private def while_seq (ξ : List Channel.{w}) (ς : String → Option Channel.{w}) (e : Expression Typ) (S : List (Statement.{y} Typ (Expression Typ) Typ.initArgs)) : ℕ → Domain Store.{u, v, w, x}.type Channel.{w} (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type PUnit.{y + 1}
          | 0 => .branch λ σ ↦ {.next σ { val := .pure .unit }}
          | i + 1 => (while_seq ξ ς e S i ⬰ Statement.denotation ξ ς S ⬰ guard ξ ς e) ⊻ (.pure .unit ⬰ guard ξ ς (.prefix .«¬» e))

        protected def denotation (ξ : List Channel.{w}) (ς : String → Option Channel.{w}) : List (Statement.{y} Typ (Expression Typ) Typ.initArgs) → Domain Store.{u, v, w, x}.type Channel.{w} (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type PUnit.{y + 1}
          | [] => .pure .unit
          | .panic e :: ss => Statement.denotation ξ ς ss ⬰ (Expression.denotation ξ ς e >>= λ _ ↦ .abort)
          | .return es :: ss => match ss with
            | [] => match ξ with
              | ret :: _ => Expression.denotations ξ ς es >>= λ vs ↦ .branch λ σ ↦ match Store.popϙ σ with
                | .none => {.next σ { val := .abort }}
                | .some σ => {.next σ <| { val := .branch λ _ ↦ {.send ret (Value.𝕍.tuple vs) { val := .pure .unit }}} }
              | [] => .abort
            | _ => .abort
          | .print e :: ss =>
            Statement.denotation ξ ς ss ⬰ (Expression.denotation ξ ς e >>= λ v ↦ .branch λ _ ↦ {.send out v { val := .pure .unit }})
          -- make
          -- var
          | .if e S₁ S₂ :: ss =>
            Statement.denotation ξ ς ss ⬰ ((Statement.denotation ξ ς S₁ ⬰ guard ξ ς e) ⊻ (Statement.denotation ξ ς S₂ ⬰ guard ξ ς (.prefix .«¬» e)))
          | .while e S :: ss =>
            -- NOTE: we show in `while_seq_cauchy` that the limit is actually defined
            Statement.denotation ξ ς ss ⬰ lim (Filter.atTop.map (while_seq ξ ς e S))
          -- close
          -- select
          -- switch
          | .go S :: ss => (λ _ ↦ PUnit.unit) <$> (Statement.denotation ξ ς S ∥ Statement.denotation ξ ς ss)
          | .send c e :: ss =>
            Expression.denotation ξ ς e >>= λ v ↦
            Expression.denotation ξ ς c >>= λ c ↦
            Statement.denotation ξ ς ss ⬰ Domain.branch λ σ ↦
              channel c (default := {.next σ { val := .abort }})
                (λ c ↦ {.send c v { val := .pure .unit }})
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
        end

        theorem while_seq_nonexpansive {ξ ς e S} {n} : edist (while_seq out ξ ς e S n) (while_seq out ξ ς e S (n + 1)) ≤ (1/2)^n := by
          rw [Domain.edist_eq, Domain.dist_eq]
          apply ENNReal.ofReal_le_of_le_toReal
          rw [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_two]
          change idist _ _ ≤ unitInterval.half^n
          conv_lhs => enter [2]; unfold while_seq

          admit

        theorem while_seq_cauchy {ξ ς e S} : CauchySeq (while_seq out ξ ς e S) := by
          apply cauchySeq_of_edist_le_geometric (1/2) 1
          · simp only [one_div, ENNReal.inv_lt_one, Nat.one_lt_ofNat]
          · exact ENNReal.one_ne_top
          · intros _
            grw [while_seq_nonexpansive]
            simp only [one_div, one_mul, Std.le_refl]
    end Statement
  end GoCal
end
