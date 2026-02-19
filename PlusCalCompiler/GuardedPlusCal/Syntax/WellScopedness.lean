import PlusCalCompiler.GuardedPlusCal.Syntax
import PlusCalCompiler.GuardedPlusCal.Syntax.Lemmas
import Mathlib.Data.Finset.Basic
import Extra.Finset

abbrev Scope := Finset String

namespace GuardedPlusCal
  universe u
  variable {Expr Typ : Type u} (Expr_WellScoped : (Γ : Scope) → Expr → Prop)

  protected def AtomicBranch.WellScoped (Br : AtomicBranch Typ Expr) («Σ» Δ Γ Ξ : Scope) («Σ_disj_Δ» : Disjoint «Σ» Δ := by simp [*]) («Σ_disj_Γ» : Disjoint «Σ» Γ := by simp [*]) (Δ_disj_Γ : Disjoint Δ Γ := by simp [*]) («Σ_disj_Ξ» : Disjoint «Σ» Ξ := by simp [*]) (Δ_disj_Ξ : Disjoint Δ Ξ := by simp [*]) (Γ_disj_Ξ : Disjoint Γ Ξ := by simp [*]) : Prop := match Br with
    | ⟨.some ⟨[], .let x τ «=|∈» e⟩, B⟩ => ∃ (h₁ : x ∉ «Σ») (h₂ : x ∉ Δ) (h₃ : x ∉ Γ) (h₄ : x ∉ Ξ), Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ AtomicBranch.WellScoped ⟨.none, B⟩ «Σ» Δ Γ (insert x Ξ)
    | ⟨.some ⟨.let x τ «=|∈» e :: Ss, I⟩, B⟩ => ∃ (h₁ : x ∉ «Σ») (h₂ : x ∉ Δ) (h₃ : x ∉ Γ) (h₄ : x ∉ Ξ), Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ AtomicBranch.WellScoped ⟨.some ⟨Ss, I⟩, B⟩ «Σ» Δ Γ (insert x Ξ)
    | ⟨.some ⟨[], .await e⟩, B⟩ => Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ AtomicBranch.WellScoped ⟨.none, B⟩ «Σ» Δ Γ Ξ
    | ⟨.some ⟨.await e :: Ss, I⟩, B⟩ => Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ AtomicBranch.WellScoped ⟨.some ⟨Ss, I⟩, B⟩ «Σ» Δ Γ Ξ
    | ⟨.some ⟨[], .receive chan ref⟩, B⟩ =>
      ref.name ∈ Γ ∧ chan.name ∈ Δ ∧ (∀ idx ∈ chan.args, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) ∧ (∀ arg ∈ ref.args, ∀ idx ∈ arg, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) ∧
      AtomicBranch.WellScoped ⟨.none, B⟩ «Σ» Δ Γ Ξ
    | ⟨.some ⟨.receive chan ref :: Ss, I⟩, B⟩ =>
      ref.name ∈ Γ ∧ chan.name ∈ Δ ∧ (∀ idx ∈ chan.args, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) ∧ (∀ arg ∈ ref.args, ∀ idx ∈ arg, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) ∧
      AtomicBranch.WellScoped ⟨.some ⟨Ss, I⟩, B⟩ «Σ» Δ Γ Ξ
    | ⟨.none, .skip :: Ss, I⟩ => AtomicBranch.WellScoped ⟨.none, Ss, I⟩ «Σ» Δ Γ Ξ
    | ⟨.none, .print e :: Ss, I⟩ => Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ AtomicBranch.WellScoped ⟨.none, Ss, I⟩ «Σ» Δ Γ Ξ
    | ⟨.none, .assert e :: Ss, I⟩ => Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ AtomicBranch.WellScoped ⟨.none, Ss, I⟩ «Σ» Δ Γ Ξ
    | ⟨.none, .send chan e :: Ss, I⟩ =>
      Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ chan.name ∈ Δ ∧ (∀ idx ∈ chan.args, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) ∧
      AtomicBranch.WellScoped ⟨.none, Ss, I⟩ «Σ» Δ Γ Ξ
    | ⟨.none, .multicast chan filter e :: Ss, I⟩ =>
      chan ∈ Δ ∧ (∀ r ∈ filter, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) r.2.2.2) ∧ (∀ r ∈ filter, r.1 ∉ «Σ» ∧ r.1 ∉ Γ ∧ r.1 ∉ Ξ) ∧
      Expr_WellScoped («Σ» ∪ Γ ∪ Ξ ∪ (filter.map Prod.fst).toFinset) e ∧ AtomicBranch.WellScoped ⟨.none, Ss, I⟩ «Σ» Δ Γ Ξ
    | ⟨.none, .assign ref e :: Ss, I⟩ =>
      Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ ref.name ∈ Γ ∧ (∀ arg ∈ ref.args, ∀ idx ∈ arg, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) ∧
      AtomicBranch.WellScoped ⟨.none, Ss, I⟩ «Σ» Δ Γ Ξ
    | ⟨.none, [], .goto l⟩ => True

  @[mk_iff]
  protected inductive AtomicBranch.WellScopedPrecond («Σ» Δ Γ : Scope) («Σ_disj_Δ» : Disjoint «Σ» Δ := by simp [*]) («Σ_disj_Γ» : Disjoint «Σ» Γ := by simp [*]) (Δ_disj_Γ : Disjoint Δ Γ := by simp [*]) :
      Option (Block (Statement Typ Expr true) false) → (Ξ Ξ' : Scope) → («Σ_disj_Ξ» : Disjoint «Σ» Ξ := by simp [*]) → (Δ_disj_Ξ : Disjoint Δ Ξ := by simp [*]) → (Γ_disj_Ξ : Disjoint Γ Ξ := by simp [*]) → («Σ_disj_Ξ'» : Disjoint «Σ» Ξ' := by simp [*]) → (Δ_disj_Ξ' : Disjoint Δ Ξ' := by simp [*]) → (Γ_disj_Ξ' : Disjoint Γ Ξ' := by simp [*]) → Prop where
    | none {Ξ} («Σ_disj_Ξ» : Disjoint «Σ» Ξ) (Δ_disj_Ξ : Disjoint Δ Ξ) (Γ_disj_Ξ : Disjoint Γ Ξ) :
      AtomicBranch.WellScopedPrecond «Σ» Δ Γ ‹_› ‹_› ‹_› Option.none Ξ Ξ
    | some_await_end {Ξ e} («Σ_disj_Ξ» : Disjoint «Σ» Ξ) (Δ_disj_Ξ : Disjoint Δ Ξ) (Γ_disj_Ξ : Disjoint Γ Ξ) : Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e →
      AtomicBranch.WellScopedPrecond «Σ» Δ Γ ‹_› ‹_› ‹_› (Option.some <| Block.end <| .await e) Ξ Ξ
    | some_let_end {Ξ x τ «=|∈» e} («Σ_disj_Ξ» : Disjoint «Σ» Ξ) (Δ_disj_Ξ : Disjoint Δ Ξ) (Γ_disj_Ξ : Disjoint Γ Ξ) : Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e →
        (h₁ : x ∉ «Σ») → (h₂ : x ∉ Δ) → (h₃ : x ∉ Γ) → (h₄ : x ∉ Ξ) →
      AtomicBranch.WellScopedPrecond «Σ» Δ Γ ‹_› ‹_› ‹_› (Option.some <| Block.end <| .let x τ «=|∈» e) Ξ (insert x Ξ)
    | some_receive_end {Ξ chan ref} («Σ_disj_Ξ» : Disjoint «Σ» Ξ) (Δ_disj_Ξ : Disjoint Δ Ξ) (Γ_disj_Ξ : Disjoint Γ Ξ) : ref.name ∈ Γ → chan.name ∈ Δ →
        (∀ idx ∈ chan.args, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) → (∀ arg ∈ ref.args, ∀ idx ∈ arg, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) →
      AtomicBranch.WellScopedPrecond «Σ» Δ Γ ‹_› ‹_› ‹_› (Option.some <| Block.end <| .receive chan ref) Ξ Ξ
    | some_await_cons {Ξ e B Ξ'} («Σ_disj_Ξ» : Disjoint «Σ» Ξ) (Δ_disj_Ξ : Disjoint Δ Ξ) (Γ_disj_Ξ : Disjoint Γ Ξ) : Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e →
        {h₁ : Disjoint «Σ» Ξ'} → {h₂ : Disjoint Δ Ξ'} → {h₃ : Disjoint Γ Ξ'} → AtomicBranch.WellScopedPrecond «Σ» Δ Γ ‹_› ‹_› ‹_› (Option.some B) Ξ Ξ' →
      AtomicBranch.WellScopedPrecond «Σ» Δ Γ ‹_› ‹_› ‹_› (Option.some <| Block.cons (.await e) B) Ξ Ξ'
    | some_let_cons {Ξ x τ «=|∈» e B Ξ'} («Σ_disj_Ξ» : Disjoint «Σ» Ξ) (Δ_disj_Ξ : Disjoint Δ Ξ) (Γ_disj_Ξ : Disjoint Γ Ξ) : Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e →
        (h₁ : x ∉ «Σ») → (h₂ : x ∉ Δ) → (h₃ : x ∉ Γ) → (h₄ : x ∉ Ξ) →
        {h₅ : Disjoint «Σ» Ξ'} → {h₆ : Disjoint Δ Ξ'} → {h₇ : Disjoint Γ Ξ'} → AtomicBranch.WellScopedPrecond «Σ» Δ Γ ‹_› ‹_› ‹_› (Option.some B) (insert x Ξ) Ξ' →
      AtomicBranch.WellScopedPrecond «Σ» Δ Γ ‹_› ‹_› ‹_› (Option.some <| Block.cons (.let x τ «=|∈» e) B) Ξ Ξ'
    | some_receive_cons {Ξ chan ref B Ξ'} («Σ_disj_Ξ» : Disjoint «Σ» Ξ) (Δ_disj_Ξ : Disjoint Δ Ξ) (Γ_disj_Ξ : Disjoint Γ Ξ) : ref.name ∈ Γ → chan.name ∈ Δ →
        (∀ idx ∈ chan.args, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) → (∀ arg ∈ ref.args, ∀ idx ∈ arg, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) →
        {h₅ : Disjoint «Σ» Ξ'} → {h₆ : Disjoint Δ Ξ'} → {h₇ : Disjoint Γ Ξ'} → AtomicBranch.WellScopedPrecond «Σ» Δ Γ ‹_› ‹_› ‹_› (Option.some B) Ξ Ξ' →
      AtomicBranch.WellScopedPrecond «Σ» Δ Γ ‹_› ‹_› ‹_› (Option.some <| Block.cons (.receive chan ref) B) Ξ Ξ'

  theorem AtomicBranch.WellScopedPrecond.some_await_cons' {«Σ» Δ Γ Ξ Ξ' : Scope} {e} {B : Block (Statement Typ Expr true) false}
    {«Σ_disj_Δ» : Disjoint «Σ» Δ} {«Σ_disj_Γ» : Disjoint «Σ» Γ} {Δ_disj_Γ : Disjoint Δ Γ} {«Σ_disj_Ξ» : Disjoint «Σ» Ξ} {Δ_disj_Ξ : Disjoint Δ Ξ} {Γ_disj_Ξ : Disjoint Γ Ξ} {«Σ_disj_Ξ'» : Disjoint «Σ» Ξ'} {Δ_disj_Ξ' : Disjoint Δ Ξ'} {Γ_disj_Ξ' : Disjoint Γ Ξ'}
    (h : AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some <| Block.cons (.await e) B) Ξ Ξ') :
      Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some B) Ξ Ξ' := by
    rw [AtomicBranch.wellScopedPrecond_iff _ «Σ» Δ Γ ‹_› ‹_› ‹_› _ Ξ Ξ'] at h
    obtain h|h|h|h|h|h|h := h
    1-4,6-7:  absurd h
              nofun
    · obtain ⟨_, B', _, IH, _⟩ := h
      injections
      rw [← Block.ext_iff (B := B) (B' := B') ‹_› ‹_›] at IH
      subst e
      trivial

  theorem AtomicBranch.WellScopedPrecond.some_await_end' {«Σ» Δ Γ Ξ Ξ' : Scope} {e}
    {«Σ_disj_Δ» : Disjoint «Σ» Δ} {«Σ_disj_Γ» : Disjoint «Σ» Γ} {Δ_disj_Γ : Disjoint Δ Γ} {«Σ_disj_Ξ» : Disjoint «Σ» Ξ} {Δ_disj_Ξ : Disjoint Δ Ξ} {Γ_disj_Ξ : Disjoint Γ Ξ} {«Σ_disj_Ξ'» : Disjoint «Σ» Ξ'} {Δ_disj_Ξ' : Disjoint Δ Ξ'} {Γ_disj_Ξ' : Disjoint Γ Ξ'}
    (h : AtomicBranch.WellScopedPrecond (Typ := Typ) Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some <| Block.end (.await e)) Ξ Ξ') :
      Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ Ξ' = Ξ := by
    rw [AtomicBranch.wellScopedPrecond_iff _ «Σ» Δ Γ ‹_› ‹_› ‹_› _ Ξ Ξ'] at h
    obtain h|h|h|h|h|h|h := h
    1,3-7:  absurd h
            nofun
    · obtain ⟨_, _, _, rfl, _, _, _⟩ := h
      injections
      subst e
      trivial

  theorem AtomicBranch.WellScopedPrecond.some_let_cons' {«Σ» Δ Γ Ξ Ξ' : Scope} {name τ «=|∈» e} {B : Block (Statement Typ Expr true) false}
    {«Σ_disj_Δ» : Disjoint «Σ» Δ} {«Σ_disj_Γ» : Disjoint «Σ» Γ} {Δ_disj_Γ : Disjoint Δ Γ} {«Σ_disj_Ξ» : Disjoint «Σ» Ξ} {Δ_disj_Ξ : Disjoint Δ Ξ} {Γ_disj_Ξ : Disjoint Γ Ξ} {«Σ_disj_Ξ'» : Disjoint «Σ» Ξ'} {Δ_disj_Ξ' : Disjoint Δ Ξ'} {Γ_disj_Ξ' : Disjoint Γ Ξ'}
    (h : AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some <| Block.cons (.let name τ «=|∈» e) B) Ξ Ξ') :
      ∃ (h₁ : name ∉ «Σ») (h₂ : name ∉ Δ) (h₃ : name ∉ Γ) (_ : name ∉ Ξ) (_ : Disjoint «Σ» Ξ') (_ : Disjoint Δ Ξ') (_ : Disjoint Γ Ξ'),
        Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some B) (insert name Ξ) Ξ' := by
    rw [AtomicBranch.wellScopedPrecond_iff _ «Σ» Δ Γ ‹_› ‹_› ‹_› _ Ξ Ξ'] at h
    obtain h|h|h|h|h|h|h := h
    1-5,7:  absurd h
            nofun
    · obtain ⟨_, _, _, _, B', _, _, _, _, _, IH, _⟩ := h
      injections
      rw [← Block.ext_iff (B := B) (B' := B') ‹_› ‹_›] at IH
      subst name τ «=|∈» e
      exists ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›

  theorem AtomicBranch.WellScopedPrecond.some_let_end' {«Σ» Δ Γ Ξ Ξ' : Scope} {name τ «=|∈» e}
    {«Σ_disj_Δ» : Disjoint «Σ» Δ} {«Σ_disj_Γ» : Disjoint «Σ» Γ} {Δ_disj_Γ : Disjoint Δ Γ} {«Σ_disj_Ξ» : Disjoint «Σ» Ξ} {Δ_disj_Ξ : Disjoint Δ Ξ} {Γ_disj_Ξ : Disjoint Γ Ξ} {«Σ_disj_Ξ'» : Disjoint «Σ» Ξ'} {Δ_disj_Ξ' : Disjoint Δ Ξ'} {Γ_disj_Ξ' : Disjoint Γ Ξ'}
    (h : AtomicBranch.WellScopedPrecond (Typ := Typ) Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some <| Block.end (.let name τ «=|∈» e)) Ξ Ξ') :
      ∃ (_ : name ∉ «Σ») (_ : name ∉ Δ) (_ : name ∉ Γ) (_ : name ∉ Ξ), Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) e ∧ Ξ' = insert name Ξ := by
    rw [AtomicBranch.wellScopedPrecond_iff _ «Σ» Δ Γ ‹_› ‹_› ‹_› _ Ξ Ξ'] at h
    obtain h|h|h|h|h|h|h := h
    1-2,4-7:  absurd h
              nofun
    · obtain ⟨_, _, _, _, _, _, _, _,_, _, rfl, _, _, _⟩ := h
      injections
      subst name τ «=|∈» e
      exists ‹_›, ‹_›, ‹_›, ‹_›

  theorem AtomicBranch.WellScopedPrecond.some_receive_cons' {«Σ» Δ Γ Ξ Ξ' : Scope} {chan ref} {B : Block (Statement Typ Expr true) false}
    {«Σ_disj_Δ» : Disjoint «Σ» Δ} {«Σ_disj_Γ» : Disjoint «Σ» Γ} {Δ_disj_Γ : Disjoint Δ Γ} {«Σ_disj_Ξ» : Disjoint «Σ» Ξ} {Δ_disj_Ξ : Disjoint Δ Ξ} {Γ_disj_Ξ : Disjoint Γ Ξ} {«Σ_disj_Ξ'» : Disjoint «Σ» Ξ'} {Δ_disj_Ξ' : Disjoint Δ Ξ'} {Γ_disj_Ξ' : Disjoint Γ Ξ'}
    (h : AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some <| Block.cons (.receive chan ref) B) Ξ Ξ') :
      ref.name ∈ Γ ∧ chan.name ∈ Δ ∧ (∀ idx ∈ chan.args, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) ∧ (∀ arg ∈ ref.args, ∀ idx ∈ arg, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) ∧
        AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some B) Ξ Ξ' := by
    rw [AtomicBranch.wellScopedPrecond_iff _ «Σ» Δ Γ ‹_› ‹_› ‹_› _ Ξ Ξ'] at h
    obtain h|h|h|h|h|h|h := h
    1-6:  absurd h
          nofun
    · obtain ⟨_, _, B', _, _, _, _, IH, _⟩ := h
      injections
      rw [← Block.ext_iff (B := B) (B' := B') ‹_› ‹_›] at IH
      subst chan ref
      trivial

  theorem AtomicBranch.WellScopedPrecond.some_receive_end' {«Σ» Δ Γ Ξ Ξ' : Scope} {chan ref}
    {«Σ_disj_Δ» : Disjoint «Σ» Δ} {«Σ_disj_Γ» : Disjoint «Σ» Γ} {Δ_disj_Γ : Disjoint Δ Γ} {«Σ_disj_Ξ» : Disjoint «Σ» Ξ} {Δ_disj_Ξ : Disjoint Δ Ξ} {Γ_disj_Ξ : Disjoint Γ Ξ} {«Σ_disj_Ξ'» : Disjoint «Σ» Ξ'} {Δ_disj_Ξ' : Disjoint Δ Ξ'} {Γ_disj_Ξ' : Disjoint Γ Ξ'}
    (h : AtomicBranch.WellScopedPrecond (Typ := Typ) Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some <| Block.end (.receive chan ref)) Ξ Ξ') :
      ref.name ∈ Γ ∧ chan.name ∈ Δ ∧ (∀ idx ∈ chan.args, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) ∧ (∀ arg ∈ ref.args, ∀ idx ∈ arg, Expr_WellScoped («Σ» ∪ Γ ∪ Ξ) idx) ∧ Ξ' = Ξ := by
    rw [AtomicBranch.wellScopedPrecond_iff _ «Σ» Δ Γ ‹_› ‹_› ‹_› _ Ξ Ξ'] at h
    obtain h|h|h|h|h|h|h := h
    1-3,5-7:  absurd h
              nofun
    · obtain ⟨_, _, _, _, _, _, _, rfl, _, _, _⟩ := h
      injections
      subst chan ref
      trivial

  theorem AtomicBranch.scope_supset_of_wellscoped_precond {B : Option (Block (Statement Typ Expr true) false)} {«Σ» Δ Γ Ξ Ξ' : Scope} {«Σ_disj_Δ» : Disjoint «Σ» Δ} {«Σ_disj_Γ» : Disjoint «Σ» Γ} {Δ_disj_Γ : Disjoint Δ Γ} {«Σ_disj_Ξ» : Disjoint «Σ» Ξ} {Δ_disj_Ξ : Disjoint Δ Ξ} {Γ_disj_Ξ : Disjoint Γ Ξ} {«Σ_disj_Ξ'» : Disjoint «Σ» Ξ'} {Δ_disj_Ξ' : Disjoint Δ Ξ'} {Γ_disj_Ξ' : Disjoint Γ Ξ'}
    (ws : AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› B Ξ Ξ') :
      Ξ' ⊇ Ξ := by
    induction ws with
    | none «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ => apply Finset.Subset.rfl
    | some_await_end «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ => apply Finset.Subset.rfl
    | some_let_end «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ h₁ h₂ h₃ h₄ => apply Finset.subset_insert
    | some_receive_end «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ _ _ _ => apply Finset.Subset.rfl
    | some_await_cons «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ _ IH => assumption
    | some_let_cons «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ h₁ h₂ h₃ h₄ _ IH =>
      change _ ⊆ _ at IH
      erw [Finset.insert_subset_iff] at IH
      exact IH.right
    | some_receive_cons «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ _ _ _ _ IH => assumption

  /--
    An alternative definition of `AtomicBranch.WellScoped` that first checks the wellscopedness of the precondition and then the action in two different steps,
    exhibiting the temporary context `Ξ'` generated by the binders of the precondition.
  -/
  theorem AtomicBranch.wellscoped_precond_action_iff_wellscoped
    {Br : AtomicBranch Typ Expr} {«Σ» Δ Γ Ξ : Scope} {«Σ_disj_Δ» : Disjoint «Σ» Δ} {«Σ_disj_Γ» : Disjoint «Σ» Γ} {Δ_disj_Γ : Disjoint Δ Γ} {«Σ_disj_Ξ» : Disjoint «Σ» Ξ} {Δ_disj_Ξ : Disjoint Δ Ξ} {Γ_disj_Ξ : Disjoint Γ Ξ} :
      AtomicBranch.WellScoped Expr_WellScoped Br «Σ» Δ Γ Ξ ↔
      ∃ Ξ' ⊇ Ξ, ∃ (h₁ : Disjoint «Σ» Ξ') (h₂ : Disjoint Δ Ξ') (h₃ : Disjoint Γ Ξ'),
        AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› Br.precondition Ξ Ξ' ∧ AtomicBranch.WellScoped Expr_WellScoped ⟨.none, Br.action⟩ «Σ» Δ Γ Ξ' := by
    iff_rintro h ⟨Ξ', Ξ'_sup_Ξ, h₁, h₂, h₃, precond_ws, action_ws⟩
    · fun_induction AtomicBranch.WellScoped Expr_WellScoped Br «Σ» Δ Γ Ξ with
      | case1 Ξ h₁ h₂ h₃ x =>
        obtain ⟨h₁', h₂', h₃', h₄', _, h⟩ := h

        refine ⟨insert x Ξ, Finset.subset_insert _ _, ?_, ?_, ?_, ?_, h⟩
        1-3:  rw [Finset.disjoint_insert_right]; trivial
        · apply AtomicBranch.WellScopedPrecond.some_let_end <;> assumption
      | case2 Ξ h₁ h₂ h₃ x _ _ _ Ss I _ IH =>
        obtain ⟨h₁', h₂', h₃', h₄', _, h⟩ := h
        obtain ⟨Ξ', Ξ'_supset, h₁'', h₂'', h₃'', _, h⟩ := IH h₁' h₂' h₃' h

        change _ ⊆ _ at Ξ'_supset
        rw [Finset.insert_subset_iff] at Ξ'_supset
        obtain ⟨x_in, Ξ'_sup_Ξ⟩ := Ξ'_supset

        refine ⟨Ξ', Ξ'_sup_Ξ, ?_, ?_, ?_, ?_, h⟩
        1-3:  assumption
        · rw [← Block.cons.eq_def _ ⟨Ss, I⟩]
          apply AtomicBranch.WellScopedPrecond.some_let_cons <;> assumption
      | case3 Ξ h₁ h₂ h₃ =>
        obtain ⟨_, h⟩ := h
        refine ⟨Ξ, Finset.Subset.rfl, ?_, ?_, ?_, ?_, h⟩
        1-3:  assumption
        · apply AtomicBranch.WellScopedPrecond.some_await_end
          assumption
      | case4 Ξ h₁ h₂ h₃ _ Ss I _ IH =>
        obtain ⟨_, h⟩ := h
        obtain ⟨Ξ', Ξ'_supset, h₁', h₂', h₃', _, h⟩ := IH h

        refine ⟨Ξ', Ξ'_supset, ?_, ?_, ?_, ?_, h⟩
        1-3:  assumption
        · rw [← Block.cons.eq_def _ ⟨Ss, I⟩]
          apply AtomicBranch.WellScopedPrecond.some_await_cons <;> assumption
      | case5 Ξ h₁ h₂ h₃ =>
        obtain ⟨h₁', h₂', h₃', h₄', h⟩ := h
        refine ⟨Ξ, Finset.Subset.rfl, ?_, ?_, ?_, ?_, h⟩
        1-3: assumption
        · apply AtomicBranch.WellScopedPrecond.some_receive_end <;> assumption
      | case6 Ξ h₁ h₂ h₃ _ _ Ss I _ IH =>
        obtain ⟨h₁', h₂', h₃', h₄', h⟩ := h
        obtain ⟨Ξ', Ξ'_supset, h₁'', h₂'', h₃'', _, h⟩ := IH h

        refine ⟨Ξ', Ξ'_supset, ?_, ?_, ?_, ?_, h⟩
        1-3: assumption
        · rw [← Block.cons.eq_def _ ⟨Ss, I⟩]
          apply AtomicBranch.WellScopedPrecond.some_receive_cons <;> assumption
      | case7 Ξ h₁ h₂ h₃ | case8 Ξ h₁ h₂ h₃ | case9 Ξ h₁ h₂ h₃ | case10 Ξ h₁ h₂ h₃
      | case11 Ξ h₁ h₂ h₃ | case12 Ξ h₁ h₂ h₃ | case13 Ξ h₁ h₂ h₃ =>
        refine ⟨Ξ, Finset.Subset.rfl, h₁, h₂, h₃, ?_, ?_⟩
        · apply WellScopedPrecond.none
        · unfold AtomicBranch.WellScoped
          exact h
    · let ⟨precond, action⟩ := Br; dsimp at precond_ws action_ws
      induction precond_ws with
      | none «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ =>
        assumption
      | some_await_end «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ e_ws =>
        rw [Block.end]
        unfold AtomicBranch.WellScoped
        constructor <;> assumption
      | some_let_end «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ e_ws h₁ h₂ h₃ h₄ =>
        rw [Block.end]
        unfold AtomicBranch.WellScoped
        exists h₁, h₂, h₃, h₄
      | some_receive_end «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ _ _ _ =>
        rw [Block.end]
        unfold AtomicBranch.WellScoped
        and_intros <;> trivial
      | some_await_cons «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ _ IH =>
        rw [Block.cons]
        unfold AtomicBranch.WellScoped
        constructor
        · assumption
        · apply IH <;> assumption
      | some_let_cons «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ h₁ h₂ h₃ h₄ jsp IH =>
        rw [Block.cons]
        unfold AtomicBranch.WellScoped
        exists h₁, h₂, h₃, h₄, ‹_›
        apply IH
        · apply AtomicBranch.scope_supset_of_wellscoped_precond <;> assumption
        · assumption
      | some_receive_cons «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ _ _ _ _ IH =>
        rw [Block.cons]
        unfold AtomicBranch.WellScoped
        and_intros <;> try trivial
        apply IH <;> assumption

  theorem AtomicBranch.WellScopedPrecond.append {«Σ» Δ Γ Ξ Ξ' Ξ'' : Scope}
    {«Σ_disj_Δ» : Disjoint «Σ» Δ} {«Σ_disj_Γ» : Disjoint «Σ» Γ} {Δ_disj_Γ : Disjoint Δ Γ} {«Σ_disj_Ξ» : Disjoint «Σ» Ξ} {Δ_disj_Ξ : Disjoint Δ Ξ} {Γ_disj_Ξ : Disjoint Γ Ξ}
    {«Σ_disj_Ξ'» : Disjoint «Σ» Ξ'} {Δ_disj_Ξ' : Disjoint Δ Ξ'} {Γ_disj_Ξ' : Disjoint Γ Ξ'}
    {«Σ_disj_Ξ''» : Disjoint «Σ» Ξ''} {Δ_disj_Ξ'' : Disjoint Δ Ξ''} {Γ_disj_Ξ'' : Disjoint Γ Ξ''}
    {Ss Ss' : List (Statement Typ Expr true false)} (h : Ss ≠ []) (h' : Ss' ≠ [])
    (wellscoped_Ss : AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some (Block.ofList Ss h)) Ξ Ξ')
    (wellscoped_Ss' : AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some (Block.ofList Ss' h')) Ξ' Ξ'') :
      AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some (Block.ofList (Ss ++ Ss') (List.append_ne_nil_of_left_ne_nil h _))) Ξ Ξ'' := by
    induction Ss, h using List.non_empty_induction generalizing Ξ with
    | singleton S =>
      simp [Block.ofList_cons_of_non_empty h']
      simp [Block.ofList_singleton] at wellscoped_Ss
      cases S with
      | «let» name τ «=|∈» e =>
        obtain ⟨_, _, _, _, _, rfl⟩ := AtomicBranch.WellScopedPrecond.some_let_end' Expr_WellScoped wellscoped_Ss
        apply AtomicBranch.WellScopedPrecond.some_let_cons <;> assumption
      | await e =>
        obtain ⟨_, rfl⟩ := AtomicBranch.WellScopedPrecond.some_await_end' Expr_WellScoped wellscoped_Ss
        apply AtomicBranch.WellScopedPrecond.some_await_cons <;> assumption
      | receive chan ref =>
        obtain ⟨_, _, _, _, rfl⟩ := AtomicBranch.WellScopedPrecond.some_receive_end' Expr_WellScoped wellscoped_Ss
        apply AtomicBranch.WellScopedPrecond.some_receive_cons <;> assumption
    | cons S Ss h IH =>
      simp [Block.ofList_cons_of_non_empty h, Block.ofList_cons_of_non_empty (List.append_ne_nil_of_left_ne_nil h _)] at wellscoped_Ss ⊢
      cases S with
      | «let» name τ «=|∈» e =>
        obtain ⟨_, _, _, _, _, _, _, _, h⟩ := AtomicBranch.WellScopedPrecond.some_let_cons' Expr_WellScoped wellscoped_Ss
        specialize IH h
        apply AtomicBranch.WellScopedPrecond.some_let_cons <;> assumption
      | await e =>
        obtain ⟨_, h⟩ := AtomicBranch.WellScopedPrecond.some_await_cons' Expr_WellScoped wellscoped_Ss
        specialize IH h
        apply AtomicBranch.WellScopedPrecond.some_await_cons <;> assumption
      | receive chan ref =>
        obtain ⟨_, _, _, _, h⟩ := AtomicBranch.WellScopedPrecond.some_receive_cons' Expr_WellScoped wellscoped_Ss
        specialize IH h
        apply AtomicBranch.WellScopedPrecond.some_receive_cons <;> assumption

  theorem wellscopedprecond_of_append
    {«Σ» Δ Γ Ξ Ξ''' : Scope}
    {«Σ_disj_Δ» : Disjoint «Σ» Δ} {«Σ_disj_Γ» : Disjoint «Σ» Γ} {Δ_disj_Γ : Disjoint Δ Γ} {«Σ_disj_Ξ» : Disjoint «Σ» Ξ} {Δ_disj_Ξ : Disjoint Δ Ξ} {Γ_disj_Ξ : Disjoint Γ Ξ}
    {«Σ_disj_Ξ'''» : Disjoint «Σ» Ξ'''} {Δ_disj_Ξ''' : Disjoint Δ Ξ'''} {Γ_disj_Ξ''' : Disjoint Γ Ξ'''}
    {Ss Ss' : List (Statement Typ Expr true false)} {S : Statement Typ Expr true false}
    (h : AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some (Block.ofList (Ss ++ S :: Ss') (by simp))) Ξ Ξ''') :
      ∃ Ξ' Ξ'', ∃ (h₁ : Disjoint «Σ» Ξ') (h₂ : Disjoint Δ Ξ') (h₃ : Disjoint Γ Ξ') (h₁' : Disjoint «Σ» Ξ'') (h₂' : Disjoint Δ Ξ'') (h₃' : Disjoint Γ Ξ''),
        (if h' : !Ss.isEmpty then
          AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some <| Block.ofList Ss (by simp_all)) Ξ Ξ'
        else Ξ' = Ξ) ∧
        AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some <| Block.end S) Ξ' Ξ'' ∧
        (if h' : !Ss'.isEmpty then
          AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› (.some <| Block.ofList Ss' (by simp_all)) Ξ'' Ξ'''
        else Ξ'' = Ξ''') := by
    induction Ss generalizing Ξ with
    | nil =>
      -- NOTE: can't `rw` here
      simp [List.nil_append] at h
      by_cases Ss'_empty : Ss' = []
      · subst Ss'
        rw [Block.ofList_singleton] at h
        cases S <;> [
            obtain ⟨_, _, _, _, _, rfl⟩ := AtomicBranch.WellScopedPrecond.some_let_end' Expr_WellScoped h
          | obtain ⟨_, rfl⟩ := AtomicBranch.WellScopedPrecond.some_await_end' Expr_WellScoped h
          | obtain ⟨_, _, _, _, rfl⟩ := AtomicBranch.WellScopedPrecond.some_receive_end' Expr_WellScoped h
        ] <;> {
          refine ⟨_, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl, ?_, rfl⟩
          assumption
        }
      · rw [Block.ofList_cons_of_non_empty Ss'_empty] at h
        cases S <;> [
            (obtain ⟨_, _, _, _, _, _, _, _, h⟩ := AtomicBranch.WellScopedPrecond.some_let_cons' Expr_WellScoped h; letI Ξ'' := insert ‹String› Ξ)
          | (obtain ⟨_, h⟩ := AtomicBranch.WellScopedPrecond.some_await_cons' Expr_WellScoped h; letI Ξ'' := Ξ)
          | (obtain ⟨_, _, _, _, h⟩ := AtomicBranch.WellScopedPrecond.some_receive_cons' Expr_WellScoped h; letI Ξ'' := Ξ)
        ] <;> {
          refine ⟨Ξ, Ξ'', ‹_›, ‹_›, ‹_›, ?_, ?_, ?_, rfl, ?_, ?_⟩
          1-3:  simp [Ξ'', *]
          · apply_rules [
              AtomicBranch.WellScopedPrecond.some_let_end,
              AtomicBranch.WellScopedPrecond.some_await_end,
              AtomicBranch.WellScopedPrecond.some_receive_end
            ]
          · rwa [dite_cond_eq_true (eq_true (by rwa [Bool.not_eq_true', List.isEmpty_eq_false_iff]))]
        }
    | cons S' Ss IH =>
      -- NOTE: can't `rw` here
      simp [List.cons_append, Block.ofList_cons_of_non_empty] at h
      cases S' <;> [
          obtain ⟨_, _, _, _, _, _, _, _, h⟩ := AtomicBranch.WellScopedPrecond.some_let_cons' Expr_WellScoped h
        | obtain ⟨_, h⟩ := AtomicBranch.WellScopedPrecond.some_await_cons' Expr_WellScoped h
        | obtain ⟨_, _, _, _, h⟩ := AtomicBranch.WellScopedPrecond.some_receive_cons' Expr_WellScoped h
      ] <;> {
        specialize IH h
        obtain ⟨Ξ', Ξ'', _, _, _, _, _, _, IH₁, IH₂, IH₃⟩ := IH
        refine ⟨Ξ', Ξ'', ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ?_, ‹_›, ‹_›⟩
        rw [dite_cond_eq_true (eq_true (by rfl))]
        split_ifs at IH₁ with Ss_empty
        · rw [Bool.not_eq_true', List.isEmpty_eq_false_iff] at Ss_empty
          rw [Block.ofList_cons_of_non_empty Ss_empty]
          apply_rules [
            AtomicBranch.WellScopedPrecond.some_let_cons,
            AtomicBranch.WellScopedPrecond.some_await_cons,
            AtomicBranch.WellScopedPrecond.some_receive_cons
          ]
        · rw [Bool.not_eq_true, Bool.not_eq_false', List.isEmpty_iff] at Ss_empty
          subst Ss Ξ'
          rw [Block.ofList_singleton]
          apply_rules [
            AtomicBranch.WellScopedPrecond.some_let_end,
            AtomicBranch.WellScopedPrecond.some_await_end,
            AtomicBranch.WellScopedPrecond.some_receive_end
          ]
      }

  theorem AtomicBranch.WellScopedPrecond_det
    {«Σ» Δ Γ Ξ Ξ' Ξ'' : Scope}
    {«Σ_disj_Δ» : Disjoint «Σ» Δ} {«Σ_disj_Γ» : Disjoint «Σ» Γ} {Δ_disj_Γ : Disjoint Δ Γ} {«Σ_disj_Ξ» : Disjoint «Σ» Ξ} {Δ_disj_Ξ : Disjoint Δ Ξ} {Γ_disj_Ξ : Disjoint Γ Ξ}
    {«Σ_disj_Ξ'» : Disjoint «Σ» Ξ'} {Δ_disj_Ξ' : Disjoint Δ Ξ'} {Γ_disj_Ξ' : Disjoint Γ Ξ'} {«Σ_disj_Ξ''» : Disjoint «Σ» Ξ''} {Δ_disj_Ξ'' : Disjoint Δ Ξ''} {Γ_disj_Ξ'' : Disjoint Γ Ξ''}
    {B : Option (Block (Statement Typ Expr true) false)}
    (h : AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› B Ξ Ξ')
    (h' : AtomicBranch.WellScopedPrecond Expr_WellScoped «Σ» Δ Γ ‹_› ‹_› ‹_› B Ξ Ξ'') :
      Ξ' = Ξ'' := by
    induction h with
    | none «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ =>
      obtain _|_|_|_|_|_ := h'
      rfl
    | some_await_end «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ =>
      obtain _|_|_|_|_|_ := h'
      rfl
    | some_let_end «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ h₁ h₂ h₃ h₄ =>
      obtain _|_|_|_|_|_ := h'
      rfl
    | some_receive_end «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ _ _ _ =>
      obtain _|_|_|_|_|_ := h'
      rfl
    | @some_await_cons _ _ B _ _ _ _ _ «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ IH =>
      rw [AtomicBranch.wellScopedPrecond_iff  _ «Σ» Δ Γ ‹_› ‹_› ‹_› _ _ Ξ''] at h'
      obtain ⟨_|_, -⟩|⟨_, -, _|_, -⟩|⟨_, _, _, _, -, -, -, -, -, _|_, -⟩|⟨_, _, -, -, -, -, _|_, -⟩
            |⟨_, _, -, h', _⟩|⟨_, _, _, _, -, -, -, -, -, -, -, _|_, -⟩|⟨_, _, -, -, -, -, -, -, _|_, -⟩ := h'
      injections; subst_eqs
      apply IH
      conv at h' => enter [8, 1]; apply Block.ext_iff (B := B) ‹_› ‹_› |>.symm
      assumption
    | @some_let_cons _ _ _ _ _ B _ «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ h₁ h₂ h₃ h₄ _ _ _ _ IH =>
      rw [AtomicBranch.wellScopedPrecond_iff  _ «Σ» Δ Γ ‹_› ‹_› ‹_› _ _ Ξ''] at h'
      obtain ⟨_|_, -⟩|⟨_, -, _|_, -⟩|⟨_, _, _, _, -, -, -, -, -, _|_, -⟩|⟨_, _, -, -, -, -, _|_, -⟩
            |⟨_, _, -, -, _|_⟩|⟨_, _, _, _, _, -, _, _, _, _, h', _⟩|⟨_, _, -, -, -, -, -, -, _|_, -⟩ := h'
      injections; subst_eqs
      apply IH
      conv at h' => enter [8, 1]; apply Block.ext_iff (B := B) ‹_› ‹_› |>.symm
      assumption
    | @some_receive_cons _ _ _ B _ «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ _ _ _ _ _ _ _ _ IH =>
      rw [AtomicBranch.wellScopedPrecond_iff  _ «Σ» Δ Γ ‹_› ‹_› ‹_› _ _ Ξ''] at h'
      obtain ⟨_|_, -⟩|⟨_, -, _|_, -⟩|⟨_, _, _, _, -, -, -, -, -, _|_, -⟩|⟨_, _, -, -, -, -, _|_, -⟩
            |⟨_, _, -, -, _|_⟩|⟨_, _, _, _, _, -, -, -, -, -, -, _|_⟩|⟨_, _, _, -, -, -, -, h', _⟩ := h'
      injections; subst_eqs
      apply IH
      conv at h' => enter [8, 1]; apply Block.ext_iff (B := B) ‹_› ‹_› |>.symm
      assumption

  protected abbrev AtomicBlock.WellScoped (B : AtomicBlock Typ Expr) («Σ» Δ Γ : Scope) («Σ_disj_Δ» : Disjoint «Σ» Δ := by simp [*]) («Σ_disj_Γ» : Disjoint «Σ» Γ := by simp [*]) (Δ_disj_Γ : Disjoint Δ Γ := by simp [*]) : Prop :=
    ∀ Br ∈ B.branches, Br.WellScoped Expr_WellScoped («Σ» \ {"self"}) (Δ \ {"self"}) (Γ \ {"self"}) {"self"}
      (Finset.disjoint_sdiff_sdiff_of_disjoint ‹_›) (Finset.disjoint_sdiff_sdiff_of_disjoint ‹_›) (Finset.disjoint_sdiff_sdiff_of_disjoint ‹_›)
      Finset.sdiff_disjoint Finset.sdiff_disjoint Finset.sdiff_disjoint

  protected structure Process.WellScoped (P : Process Typ Expr) («Σ» Δ : Scope) («Σ_disj_Δ» : Disjoint «Σ» Δ := by simp [*]) : Prop where
    mailbox_ws : ∀ e ∈ P.mailbox, Expr_WellScoped («Σ» ∪ Δ) e
    locals_Nodup : P.locals.keys.Nodup
    locals_ws : ∀ k ∈ P.locals.values, Expr_WellScoped «Σ» k.2.2

    «Σ_locals_disjoint» : Disjoint «Σ» P.locals.keys.toFinset := by simp [*]
    Δ_locals_disjoint : Disjoint Δ P.locals.keys.toFinset := by simp [*]

    threads_ws : ∀ T ∈ P.threads, ∀ B ∈ T, B.WellScoped Expr_WellScoped «Σ» Δ P.locals.keys.toFinset

  protected structure Algorithm.WellScoped (A : Algorithm Typ Expr) («Σ» : Scope) : Prop where
    channels_Nodup : A.channels.keys.Nodup
    fifos_Nodup : A.fifos.keys.Nodup

    channels_fifos_disjoint : A.channels.keys.Disjoint A.fifos.keys := by simp [*]
    «Σ_channels_disjoint» : Disjoint «Σ» A.channels.keys.toFinset := by simp [*]
    «Σ_fifos_disjoint» : Disjoint «Σ» A.fifos.keys.toFinset := by simp [*]

    procs_ws : ∀ P ∈ A.procs, P.WellScoped Expr_WellScoped «Σ» (A.channels.keys.toFinset ∪ A.fifos.keys.toFinset)

  --------------------------------------

  variable (Expr_FreshIn : Expr → String → Prop)

  protected def Statement.FreshIn {b b' : Bool} (S : Statement Typ Expr b b') (x : String) := match b, b', S with
    | _, _, .let y _ _ e => x ≠ y ∧ Expr_FreshIn e x
    | _, _, .await e => Expr_FreshIn e x
    | _, _, .receive chan ref => chan.name ≠ x ∧ ref.name ≠ x ∧ (∀ arg ∈ chan.args, Expr_FreshIn arg x) ∧ (∀ arg ∈ ref.args, ∀ idx ∈ arg, Expr_FreshIn idx x)
    | _, _, .skip => True
    | _, _, .goto _ => True
    | _, _, .print e => Expr_FreshIn e x
    | _, _, .assert e => Expr_FreshIn e x
    | _, _, .send chan e => chan.name ≠ x ∧ (∀ arg ∈ chan.args, Expr_FreshIn arg x) ∧ Expr_FreshIn e x
    | _, _, .multicast chan filter e => chan ≠ x ∧ (∀ b ∈ filter, b.1 ≠ x ∧ Expr_FreshIn b.2.2.2 x) ∧ Expr_FreshIn e x
    | _, _, .assign ref e => ref.name ≠ x ∧ (∀ arg ∈ ref.args, ∀ idx ∈ arg, Expr_FreshIn idx x) ∧ Expr_FreshIn e x

  protected structure AtomicBranch.FreshIn (Br : AtomicBranch Typ Expr) (x : String) : Prop where
    fresh_in_precond : ∀ S ∈ Br.precondition.elim [] Block.toList, Statement.FreshIn Expr_FreshIn S x
    fresh_in_action : ∀ S ∈ Br.action.begin, Statement.FreshIn Expr_FreshIn S x

  protected structure Process.FreshIn (P : Process Typ Expr) (x : String) : Prop where
    fresh_in_locals : x ∉ P.locals.keys
    fresh_in_blocks : ∀ T ∈ P.threads, ∀ B ∈ T, ∀ Br ∈ B.branches, AtomicBranch.FreshIn Expr_FreshIn Br x

  -- set_option linter.dupNamespace false in
  -- class FreshIn (α : outParam (Type _)) (β : Type _) where
  --   FreshIn : α → β → Prop
  -- notation:50 x:50 " fresh " "in " y:50 => FreshIn.FreshIn x y

  -- instance [f : FreshIn String Expr] : FreshIn String (Process Typ Expr) := ⟨flip (Process.FreshIn (flip f.FreshIn))⟩
