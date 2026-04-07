import Core.Go.Semantics.Domains
import Core.Go.Syntax
import Mathlib.Topology.Defs.Filter

/-!
  Now that we have finished defining our domains…we can finally define the semantics of
  Go.
-/

open TypedSetTheory (Expression Typ)

abbrev Address := PUnit ⊕ PUnit ⊕ ℕ

abbrev nil : Address := .inl .unit
abbrev dummy : Address := .inr (.inl .unit)
instance : Coe ℕ Address := ⟨λ x ↦ .inr (.inr x)⟩

def Channel := (ℕ × TypedSetTheory.Typ)
  deriving DecidableEq

instance : IMetricSpace TypedSetTheory.Typ where
  idist := sorry
  idist_self := sorry
  idist_comm := sorry
  idist_triangle := sorry
  eq_of_idist_eq_zero := sorry

noncomputable instance : IMetricSpace Channel :=
  inferInstanceAs (IMetricSpace (ℕ × TypedSetTheory.Typ))
instance : CompleteSpace Channel :=
  -- Maybe?
  sorry

-- TODO: this will need to be defined mutually with 𝕍
axiom Store.{u, v, w, x} : NonemptyType.{max u v w x}

instance : Nonempty Store.type := Store.property

@[instance]
axiom Store_metricspace : IMetricSpace Store.type

@[instance]
axiom Store_completespace : CompleteSpace Store.type

axiom Store_iso.{u, v, w, x} :
  Store.{u, v, w, x}.type ≃ᵢ (Address.{u, v} → Option (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type) × List (String → Option Address.{u, v})

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
        Expression.denotation ξ ς e >>= λ v ↦ Domain.branch λ σ ↦ Value.𝕍.casesOn (motive := λ _ ↦ Set _)
          (λ b ↦ if b then {.next σ { val := .pure .unit }} else ∅)
          (λ _ ↦ {.next σ { val := .abort }})
          (λ _ ↦ {.next σ { val := .abort }})
          (λ _ _ _ _ ↦ {.next σ { val := .abort }})
          (λ _ _ _ _ ↦ {.next σ { val := .abort }})
          (λ _ ↦ {.next σ { val := .abort }})
          (λ _ _ ↦ {.next σ { val := .abort }})
          (λ _ _ ↦ {.next σ { val := .abort }})
          (λ _ _ ↦ {.next σ { val := .abort }})
          (λ _ ↦ {.next σ { val := .abort }})
          v

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
          let rec g : ℕ → Domain Store.{u, v, w, x}.type Channel.{w} (Value.𝕍 Store.{u, v, w, x}.type Channel.{w} Address.{u, v} Typ.{x}).type PUnit.{y + 1}
            | 0 => .branch λ σ ↦ {.next σ { val := .pure .unit }}
            | i + 1 => (g i ⬰ Statement.denotation ξ ς S ⬰ guard ξ ς e) ⊻ (.pure .unit ⬰ guard ξ ς (.prefix .«¬» e))

          have g_cauchy : CauchySeq g := by
            admit

          Statement.denotation ξ ς ss ⬰ lim (Filter.atTop.map g)
        -- close
        -- select
        -- switch
        | .go S :: ss => (λ _ ↦ PUnit.unit) <$> (Statement.denotation ξ ς S ‖ Statement.denotation ξ ς ss)
        -- send
        -- recv
        | _ => sorry
    end Statement
  end GoCal
end
