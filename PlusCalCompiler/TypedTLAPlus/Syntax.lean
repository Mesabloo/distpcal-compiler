import PlusCalCompiler.CoreTLAPlus.Syntax

namespace TypedTLAPlus
  open CoreTLAPlus (PrefixOperator InfixOperator)

  inductive Expression.{u} (Typ : Type u) : Type u
    /-- An (unqualified) identifier. -/
    | var (name : String) (τ : Typ)
    /-- A string literal. -/
    | str (raw : String)
    /-- An integer literal. -/
    | nat (raw : String)
    /-- A boolean literal. -/
    | bool (raw : Bool)
    /-- A set literal `{e₁, …, eₙ}` of type `𝒫(τ)`. -/
    | set (elems : List (Expression Typ)) (τ : Typ)
    /-- A record literal `[x₁ ↦ e₁, …, xₙ ↦ eₙ]`, with types ascribed to the fields. -/
    | record (fields : List (String × Typ × Expression Typ))
    /-- Prefix operator call `⊙ e`. -/
    | prefix (op : PrefixOperator) (e : Expression Typ)
    /-- Infix operator call `e₁ ⊙ e₂`. -/
    | infix (e₁ : Expression Typ) (op : InfixOperator) (e₂ : Expression Typ)
    /-- Function call `f[e₁, …, eₙ]`. -/
    | funcall (fn : Expression Typ) (args : List (Expression Typ))
    /-- Record access `e.x`. -/
    | access (e : Expression Typ) (x : String)
    /-- A literal sequence `Seq(⟨e₁, …, eₙ⟩)` of type `Seq(τ)`. -/
    | seq (es : List (Expression Typ)) (τ : Typ)
    /-- Operator call `f(e₁, …, eₙ)`. -/
    | opcall (fn : Expression Typ) (args : List (Expression Typ))
    /-- Function update `[x EXCEPT ![e₁, …, eₙ] = e]`. -/
    | except (e : Expression Typ) (upds : List ((List (List (Expression Typ) ⊕ String)) × Expression Typ))
    deriving Inhabited, BEq
