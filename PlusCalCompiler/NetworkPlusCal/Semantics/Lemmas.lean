import PlusCalCompiler.NetworkPlusCal.Semantics.Denotational

namespace NetworkPlusCal
  -- Inversion rules

  theorem Statement.reducing.let.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {pos x τ «=|∈» e}
    (h : ∃ M T F v, T ∪ M ⊢ e ⇒ v ∧ AList.lookup x (T ∪ M) = none ∧ σ = .running M T F ∧ ε = [] ∧ match «=|∈», v with
      | true, .set vs => ∃ v' ∈ vs, σ' = .running M (T.insert x v') F
      | true, _ => False
      | false, v' => σ' = .running M (T.insert x v') F) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.let.{u} pos x τ «=|∈» e) := by
    trivial

  theorem Statement.reducing.await.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {pos e}
    (h : ∃ M T F, σ = .running M T F ∧ σ' = .running M T F ∧ T ∪ M ⊢ e ⇒ .bool true ∧ ε = []) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.await.{u} pos e) := by
      trivial

  theorem Statement.reducing.skip.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior} {pos}
    (h : ∃ M T F, σ = .running M T F ∧ σ' = .running M T F ∧ ε = []) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.skip.{u} pos) := by
    trivial

  theorem Statement.reducing.goto.intro.{u} {σ : LocalState.{u} false} {σ' : LocalState.{u} true} {ε : List Behavior.{u}} {pos l}
    (h : ∃ M T F, σ = .running M T F ∧ σ' = .done M T F l ∧ ε = []) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.goto.{u} pos l) := by
    trivial

  theorem Statement.reducing.print.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {pos e}
    (h : ∃ M T F v, σ = .running M T F ∧ σ' = .running M T F ∧ T ∪ M ⊢ e ⇒ v ∧ ε = [.print v]) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.print.{u} pos e) := by
    trivial

  theorem Statement.reducing.assert.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {pos e}
    (h : ∃ M T F, σ = .running M T F ∧ σ' = .running M T F ∧ T ∪ M ⊢ e ⇒ .bool true ∧ ε = []) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.assert.{u} pos e) := by
    trivial

  theorem Statement.reducing.send.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {pos chan e}
    (h : ∃ M T F v vs vs',
        T ∪ M ⊢ e ⇒ v ∧ List.Forall₂ (T ∪ M ⊢ · ⇒ ·) chan.args vs ∧
        F.lookup ⟨chan.name, vs⟩ = .some vs' ∧
        σ = .running M T F ∧ σ' = .running M T (F.replace ⟨chan.name, vs⟩ (vs'.concat v)) ∧ ε = [.send {chan with args := vs} v]) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.send.{u} pos chan e) := by
    trivial

  theorem Statement.reducing.assign.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {pos ref e}
    (h : ∃ M T F M' v vss,
        T ∪ M ⊢ e ⇒ v ∧ List.Forall₂ (List.Forall₂ (T ∪ M ⊢ · ⇒ ·)) ref.args vss ∧
        Memory.updateRef M {ref with args := vss} v = some M' ∧ ref.name ∉ T ∧
        σ = .running M T F ∧ σ' = .running M' T F ∧ ε = []) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.assign.{u} pos ref e) := by
    trivial
end NetworkPlusCal

section
  open Lean Parser Tactic

  syntax "sem_redn " term (" ⤳ " term)? ", " term (" ⤳ " term)? ", " term (" ⤳ " term)? (", " term)? : tactic
  macro_rules
  | `(tactic| sem_redn $w₁ $[⤳ $w₂]?, $x₁ $[⤳ $x₂]?, $y₁ $[⤳ $y₂]? $[, $z]?) => do
    let w₂ := w₂.getD w₁
    let x₂ := x₂.getD x₁
    let y₂ := y₂.getD y₁

    match z with
    | .none => `(tactic| first
      | refine ⟨NetworkPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, NetworkPlusCal.Statement.reducing.skip.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨NetworkPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, NetworkPlusCal.Statement.reducing.print.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨NetworkPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, NetworkPlusCal.Statement.reducing.assert.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨NetworkPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, NetworkPlusCal.Statement.reducing.send.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨NetworkPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, NetworkPlusCal.Statement.reducing.await.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨NetworkPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, NetworkPlusCal.Statement.reducing.let.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨NetworkPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, NetworkPlusCal.Statement.reducing.assign.intro ⟨$w₁, $x₁, $y₁, $w₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | fail "Statement unsupported (yet)"
    )
    | .some z => `(tactic| first
      | refine ⟨NetworkPlusCal.LocalState.done $w₂ $y₂ $z, ?_, NetworkPlusCal.Statement.reducing.goto.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_⟩, $z, ?_, ?_⟩ <;> try rfl
    )

  syntax "sem_compn " term " ⤳ " term " ⤳ " term ", " term " ⤳ " term " ⤳ " term ", " term " ⤳ " term " ⤳ " term (", " term)? : tactic
  macro_rules
  | `(tactic| sem_compn $w₁ ⤳ $w₂ ⤳ $w₃, $x₁ ⤳ $x₂ ⤳ $x₃, $y₁ ⤳ $y₂ ⤳ $y₃ $[, $z]?) =>
    `(tactic|
      refine ⟨⟨$w₂, $x₂, $y₂, .none⟩, _, _, ?red₁, ?red₂, rfl⟩;
      (case' red₂ => sem_redn $w₂ ⤳ $w₃, $x₂ ⤳ $x₃, $y₂ ⤳ $y₃ $[, $z]?);
      (case' red₁ => sem_redn $w₁ ⤳ $w₂, $x₁ ⤳ $x₂, $y₁ ⤳ $y₂);
    )
