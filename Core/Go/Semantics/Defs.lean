import Core.Go.Semantics.Domains
import Core.Go.Syntax

/-!
  Now that we have finished defining our domains…we can finally define the semantics of
  Go.
-/

abbrev Address := PUnit ⊕ PUnit ⊕ ℕ

abbrev nil : Address := .inl .unit
abbrev dummy : Address := .inr (.inl .unit)
instance : Coe ℕ Address := ⟨λ x ↦ .inr (.inr x)⟩

def Channel := ℕ

instance : IMetricSpace Channel := inferInstanceAs (IMetricSpace ℕ)
instance : CompleteSpace Channel := sorry
  -- Yes: ℕ is a CompleteSpace

abbrev 𝕍 := Restriction Value.𝕍.type unitInterval.half

structure Store where
  /-- The main memory -/
  ϙ : Address → Option 𝕍
  /-- Scopes, i.e. a stack of bindings from variable names to addresses. -/
  h : List (String → Option Address)
  deriving Nonempty

def Store.toProd (s : Store) : (Address → Option 𝕍) × List (String → Option Address) :=
  (s.ϙ, s.h)

theorem Store.toProd_injective : Function.Injective Store.toProd := by
  rintro ⟨ϙx, hx⟩ ⟨ϙy, hy⟩ (_|_)
  rfl

noncomputable instance : IMetricSpace Store :=
  .induced _ Store.toProd_injective inferInstance

instance : CompleteSpace Store := sorry
  -- Surely?

abbrev 𝔽 :=
  List 𝕍 × List Channel × (String → Option Channel) → Domain Store Channel 𝕍 PUnit

noncomputable section
  universe u

  open TypedSetTheory (Expression Typ)

  namespace TypedSetTheory.Expression
    protected def denotation (χ : String → Option 𝔽) (ξ : List Channel) (ς : String → Option Channel) : Expression Typ → Domain Store Channel 𝕍.{u} 𝕍.{u}
      | _ => sorry
  end TypedSetTheory.Expression

  namespace GoCal
    namespace Statement
      variable {out : Channel}

      protected def denotation (χ : String → Option 𝔽) (ξ : List Channel) (ς : String → Option Channel) : Statement.{u} Typ (Expression Typ) Typ.initArgs → Domain Store Channel 𝕍.{u} PUnit
        | .panic e => e.denotation χ ξ ς |>.bind λ _ : 𝕍 ↦ .abort
        | _ => sorry
    end Statement
  end GoCal
end
