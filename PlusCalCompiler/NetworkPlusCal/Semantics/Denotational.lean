import PlusCalCompiler.NetworkPlusCal.Syntax
import Extra.Rel
import PlusCalCompiler.CoreTLAPlus.Semantics.Operational
import Mathlib.Data.Multiset.Basic
import Extra.AList
import Mathlib.Order.FixedPoints
import VerifiedCompiler.Denotational.Notations
import Extra.List
import PlusCalCompiler.GuardedPlusCal.Semantics.Denotational
import Mathlib.Order.Zorn
import Mathlib.Order.WellFoundedSet

namespace NetworkPlusCal
  export CoreTLAPlus (Value Memory)
  export GuardedPlusCal (Behavior FIFOs Memory.updateRef)

  /-!
    In the following, we dissociate channels from the main memory. This allows us to impose restrictions
    on what is allowed in expressions.
    Note that an expressions doing arbitrary things on channels on the PlusCal is expected to have
    an undefined behavior (or rather, to have no behavior at all).
  -/

  --/-- The global map containing FIFOs. -/
  --abbrev FIFOs.{u} : Type u := Batteries.AssocList (String × List Value.{u}) (List Value.{u})

  /-- The local reduction state of an atomic block. -/
  inductive LocalState.{u} : Bool → Type u
    | running (M : Memory) (tmp : Memory) (F : FIFOs) : LocalState false
    | done (M : Memory) (tmp : Memory) (F : FIFOs) (l : String) : LocalState true

  -- def Memory.updateRef (M : Memory) (r : Ref Value) (v : Value) : Option Memory := do
  --   let v' ← M.lookup r.name
  --   let v' ← doUpdate v v' r.args
  --   return M.insert r.name v'
  -- where
  --   doUpdate (v' : Value) : Value → List (List Value) → Option Value
  --     | _, [] => return v'
  --     | fn@(.fn maps), v :: vs => do
  --       let tup := CoreTLAPlus.Value.tuple v
  --       -- If `tup` is in the domain of `fn`, then update
  --       if let .some ⟨_, v⟩ := maps.find? λ ⟨k, _⟩ ↦ k == tup then
  --         let v ← doUpdate v' v vs
  --         return .fn (⟨tup, v⟩ :: maps.filter λ ⟨k, _⟩ ↦ k != tup)
  --       else
  --         return fn
  --     | _, _ => failure

  ------------

  /-! # Reduction of statements -/

  -- for FIFOs, we push on the right, and pop on the left
  def Statement.reducing : {b b' : Bool} → Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) b b' → Set (LocalState false × List Behavior × LocalState b')
    | true, false, .let _ name _ «=|∈» e =>
      {⟨σ, ε, σ'⟩ | ∃ M T F v,
        T ∪ M ⊢ e ⇒ v ∧
        AList.lookup name (T ∪ M) = none ∧
        σ = .running M T F ∧ ε = [] ∧ match «=|∈», v with
          -- non empty set membership
          | true, .set vs => ∃ v' ∈ vs, σ' = .running M (T.insert name v') F
          | true, _ => False
          | false, v => σ' = .running M (T.insert name v) F
      }
    | true, false, .await _ e => test e (.bool true)
    | false, false, .skip _ => id
    | false, true, .goto _ label => {⟨σ, ε, σ'⟩ | ∃ M T F, σ = .running M T F ∧ σ' = .done M T F label ∧ ε = []}
    | false, false, .print _ e => {⟨σ, ε, σ'⟩ | ∃ M T F v, σ = .running M T F ∧ σ' = .running M T F ∧ T ∪ M ⊢ e ⇒ v ∧ ε = [.print v]}
    | false, false, .assert _ e => test e (.bool true)
    | false, false, .send _ chan e =>
      {⟨σ, ε, σ'⟩ | ∃ M T F v vs vs',
        T ∪ M ⊢ e ⇒ v ∧ List.Forall₂ (T ∪ M ⊢ · ⇒ ·) chan.args vs ∧
        F.lookup ⟨chan.name, vs⟩ = .some vs' ∧
        σ = .running M T F ∧ σ' = .running M T (F.replace ⟨chan.name, vs⟩ (vs'.concat v)) ∧ ε = [.send {chan with args := vs} v]
      }
    | false, false, .multicast _ chan filter e => sorry
    | false, false, .assign _ ref e =>
      {⟨σ, ε, σ'⟩ | ∃ M T F M' v vss,
        T ∪ M ⊢ e ⇒ v ∧ List.Forall₂ (List.Forall₂ (T ∪ M ⊢ · ⇒ ·)) ref.args vss ∧
        Memory.updateRef M {ref with args := vss} v = some M' ∧ ref.name ∉ T ∧
        σ = .running M T F ∧ σ' = .running M' T F ∧ ε = []
      }
  where
    /-- `test e v ε` represents the identity transition restricted to states that evaluate `e` to `v`. -/
    test (e : CoreTLAPlus.Expression CoreTLAPlus.Typ) (v : Value) : Set (LocalState false × List Behavior × LocalState false) :=
      {⟨σ, ε, σ'⟩ | ∃ M T F, σ = .running M T F ∧ σ' = .running M T F ∧ T ∪ M ⊢ e ⇒ v ∧ ε = []}

    /-- The identity transition, i.e. nothing is performed. -/
    id : Set (LocalState false × List Behavior × LocalState false) :=
      {⟨σ, ε, σ'⟩ | ∃ M T F, σ = .running M T F ∧ σ' = .running M T F ∧ ε = 1}

  def Statement.aborting : {b b' : Bool} → Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) b b' → Set (LocalState false × List Behavior)
    | true, false, .let _ name _ «=|∈» e =>
      -- the set of all states which fail to reduce `e`
      {⟨σ, ε⟩ | ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      -- the set of states that reduce `e` to anything else than a set when `«=|∈»` is `true`
      ∪ {⟨σ, ε⟩ | ∃ M T F v, T ∪ M ⊢ e ⇒ v ∧ σ = .running M T F ∧ ε = [] ∧ match «=|∈», v with
        | true, .set vs | false, _ => False
        | true, _ => True}
    | true, false, .await _ e =>
      {⟨σ, ε⟩ | ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      ∪ {⟨σ, ε⟩ | ∃ M T F v, (∀ b, v ≠ .bool b) ∧ T ∪ M ⊢ e ⇒ v ∧ σ = .running M T F ∧ ε = []}
    | false, false, .skip _ => ∅
    | false, true, .goto _ label => ∅
    | false, false, .print _ e => {⟨σ, ε⟩ | ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
    | false, false, .assert _ e =>
      -- the set of all states that fail to reduce `e`
      {⟨σ, ε⟩ | ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      -- the set of all states that reduce `e` to something else than `TRUE`
      ∪ {⟨σ, ε⟩ | ∃ M T F v, v ≠ .bool true ∧ T ∪ M ⊢ e ⇒ v ∧ σ = .running M T F ∧ ε = []}
    | false, false, .send _ chan e =>
      {⟨σ, ε⟩ | ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      ∪ {⟨σ, ε⟩ | ∃ e ∈ chan.args, ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      ∪ {⟨σ, ε⟩ | ∃ M T F vs, List.Forall₂ (T ∪ M ⊢ · ⇒ ·) chan.args vs ∧
        F.lookup ⟨chan.name, vs⟩ = none ∧ σ = .running M T F ∧ ε = []}
    | false, false, .multicast _ chan filter e => sorry
    | false, false, .assign _ ref e =>
      {⟨σ, ε⟩ | ∃ M T F, (ref.name ∉ M ∨ ref.name ∈ T) ∧ σ = .running M T F ∧ ε = []}
      ∪ {⟨σ, ε⟩ | ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      ∪ {⟨σ, ε⟩ | ∃ arg ∈ ref.args, ∃ e ∈ arg, ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      ∪ {⟨σ, ε⟩ | ∃ M T F v vss,
        T ∪ M ⊢ e ⇒ v ∧ List.Forall₂ (List.Forall₂ (T ∪ M ⊢ · ⇒ ·)) ref.args vss ∧
        Memory.updateRef M {ref with args := vss} v = none ∧ ref.name ∉ T ∧ σ = .running M T F ∧ ε = []
      }

  def Statement.diverging : {b b' : Bool} → Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) b b' → Set (LocalState false × List Behavior)
    -- There is no divergence possible when reducing statements
    | _, _, _ => ∅

  @[reducible] instance instReduceStatement {b b' : Bool} : Reduce (Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) b b') (Set (LocalState false × List Behavior × LocalState b')) := ⟨Statement.reducing⟩
  @[reducible] instance instAbortStatement {b b' : Bool} : Abort (Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) b b') (Set (LocalState false × List Behavior)) := ⟨Statement.aborting⟩
  @[reducible] instance instDivergeStatement {b b' : Bool} : Diverge (Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) b b') (Set (LocalState false × List Behavior)) := ⟨Statement.diverging⟩

  /-! # Reduction of blocks -/

  -- def Block.reducing {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (B : Block α b) : Set (β false × γ × β b) :=
  --   match _h : B.begin with
  --   | [] => f B.last
  --   | x :: xs => f x ∘ᵣ₂ Block.reducing f {B with begin := xs}
  -- termination_by B.begin
  -- decreasing_by
  --   all_goals simp_wf
  --   · rw [_h]; decreasing_trivial

  -- def Block.aborting {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} (f : ⦃b : Bool⦄ → α b → Set (β false × γ)) (g : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (B : Block α b) : Set (β false × γ) :=
  --   match _h : B.begin with
  --   | [] => f B.last
  --   | x :: xs => f x ∪ g x ∘ᵣ₁ Block.aborting f g {B with begin := xs}
  -- termination_by B.begin
  -- decreasing_by
  --   all_goals simp_wf
  --   · rw [_h]; decreasing_trivial

  -- def Block.diverging {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} (f : ⦃b : Bool⦄ → α b → Set (β false × γ)) (g : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (B : Block α b) : Set (β false × γ) :=
  --   match _h : B.begin with
  --   | [] => f B.last
  --   | x :: xs => f x ∪ g x ∘ᵣ₁ Block.diverging f g {B with begin := xs}
  -- termination_by B.begin
  -- decreasing_by
  --   all_goals simp_wf
  --   · rw [_h]; decreasing_trivial

  -- @[reducible] instance instReduceBlock {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} [reduceα : ⦃b : Bool⦄ → Reduce (α b) (Set (β false × γ × β b))] : Reduce (Block α b) (Set (β false × γ × β b)) where
  --   reducing := Block.reducing λ ⦃b⦄ ↦ reduceα (b := b) |>.reducing
  -- @[reducible] instance instAbortBlock {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} [abortα : ⦃b : Bool⦄ → Abort (α b) (Set (β false × γ))] [reduceα : ⦃b : Bool⦄ → Reduce (α b) (Set (β false × γ × β b))] :
  --   Abort (Block α b) (Set (β false × γ)) where
  --     abort := Block.aborting (λ ⦃b⦄ ↦ abortα (b := b) |>.abort) (λ ⦃b⦄ ↦ reduceα (b := b) |>.reducing)
  -- @[reducible] instance instDivergeBlock {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} [divα : ⦃b : Bool⦄ → Diverge (α b) (Set (β false × γ))] [reduceα : ⦃b : Bool⦄ → Reduce (α b) (Set (β false × γ × β b))] :
  --   Diverge (Block α b) (Set (β false × γ)) where
  --     div := Block.aborting (λ ⦃b⦄ ↦ divα (b := b) |>.div) (λ ⦃b⦄ ↦ reduceα (b := b) |>.reducing)

  instance instReduceAtomicBranch : Reduce (AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) (Set (LocalState false × List Behavior × LocalState true)) where
    reducing B := B.precondition.elim NetworkPlusCal.Statement.reducing.id.{0} (⟦·⟧*) ∘ᵣ₂ ⟦B.action⟧*
  instance instAbortAtomicBranch : Abort (AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) (Set (LocalState false × List Behavior)) where
    abort B := match B.precondition with
      | .none => ⟦B.action⟧⊥
      | .some B' => ⟦B'⟧⊥ ∪ ⟦B'⟧* ∘ᵣ₁ ⟦B.action⟧⊥
  instance instDivergeAtomicBranch : Diverge (AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) (Set (LocalState false × List Behavior)) where
    div B := match B.precondition with
      | .none => ⟦B.action⟧∞
      | .some B' => ⟦B'⟧∞ ∪ ⟦B'⟧* ∘ᵣ₁ ⟦B.action⟧∞

  -- /-! # Reduction of processes -/

  -- -- TODO: consider threads with message reception

  -- structure ProcessState.{u} : Type u where
  --   /-- A view of the local variables of a process. -/
  --   localMemory : Memory.{u}
  --   /-- All the labels to be concurrently executing in a single process. -/
  --   labels : Multiset String
  --   deriving DecidableEq

  -- def Process.reducing.{u, v} (Ξ : AList λ _ : String ↦ List (AtomicBranch.{u} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ))) (F : FIFOs.{v}) : Set (ProcessState.{v} × List Behavior.{v} × ProcessState.{v} × FIFOs.{v}) :=
  --   {⟨⟨M, L⟩, ε, ⟨M', L'⟩, F'⟩ | ∃ l ∈ L, ∃ h : l ∈ Ξ, ∃ B ∈ Ξ.get l h, ∃ l',
  --     ⟨.running M F, ε, .done M' F' l'⟩ ∈ ⟦B⟧* ∧
  --     L' = (l' ::ₘ (L - {l})).filter (· ≠ "Done")
  --   }

  -- def Process.aborting (Ξ : AList λ _ : String ↦ List (AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ))) (F : FIFOs) : Set (ProcessState × List Behavior) :=
  --   {⟨⟨M, L⟩, ε⟩ | ∃ l ∈ L, ∃ h : l ∈ Ξ, ∃ B ∈ Ξ.get l h, ⟨.running M F, ε⟩ ∈ ⟦B⟧⊥}

  -- def Process.diverging (Ξ : AList λ _ : String ↦ List (AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ))) (F : FIFOs) : Set (ProcessState × List Behavior) :=
  --   {⟨⟨M, L⟩, ε⟩ | ∃ l ∈ L, ∃ h : l ∈ Ξ, ∃ B ∈ Ξ.get l h, ⟨.running M F, ε⟩ ∈ ⟦B⟧∞}

  -- /-! # Global ("distributed") reduction -/

  -- structure GlobalState.{u, v} : Type (max u v) where
  --   procs : Multiset ProcessState.{u}
  --   /-- The state of all FIFOs of the system. -/
  --   fifos : FIFOs.{u}
  --   /-- A mapping from (globally unique) labels to branches to be executed. -/
  --   code : AList λ _ : String ↦ List (AtomicBranch.{v} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ))

  -- -- the parameter `f` in `reducing` and `diverging` is there for fixed point construction

  -- def GlobalState.reducing'.{u, v} : Set (GlobalState.{u, v} × List Behavior.{u} × GlobalState.{u, v}) →o Set (GlobalState.{u, v} × List Behavior.{u} × GlobalState.{u, v}) := {
  --   toFun := λ f ↦ {⟨⟨Ps, F, Ξ⟩, ε, ⟨Ps', F', Ξ'⟩⟩ : GlobalState × _ × GlobalState | ∃ P ∈ Ps, ∃ P',
  --                    ⟨P, ε, P', F'⟩ ∈ Process.reducing Ξ F ∧ Ps' = Ps - {P} + {P'} ∧ Ξ' = Ξ} ∘ᵣ₂ f
  --                ⊔ {⟨⟨Ps, F, Ξ⟩, ε, ⟨Ps', F', Ξ'⟩⟩ : GlobalState × _ × GlobalState | Ps' = Ps ∧ Ps = ∅ ∧ F' = F ∧ Ξ' = Ξ ∧ ε = []}
  --   monotone' := by intros _ _ _; mono
  -- }
  -- def GlobalState.reducing : Set (GlobalState × List Behavior × GlobalState) := OrderHom.lfp GlobalState.reducing'

  -- /-- A `GlobalState` is aborting if, after any number of reductions, one of its processes aborts. -/
  -- def GlobalState.aborting : Set (GlobalState × List Behavior) :=
  --   GlobalState.reducing ∘ᵣ₁ {⟨⟨Ps, F, Ξ⟩, ε⟩ : GlobalState × _ | ∃ P ∈ Ps, ⟨P, ε⟩ ∈ Process.aborting Ξ F}

  -- def GlobalState.diverging' : Set (GlobalState × List Behavior) →o Set (GlobalState × List Behavior) := {
  --   toFun := λ f ↦ {⟨⟨Ps, F, Ξ⟩, ε, ⟨Ps', F', Ξ'⟩⟩ : GlobalState × _ × GlobalState | ∃ P ∈ Ps, ∃ P',
  --                    ⟨P, ε, P', F'⟩ ∈ Process.reducing Ξ F ∧ Ps' = Ps - {P} + {P'} ∧ Ξ' = Ξ} ∘ᵣ₁ f
  --   monotone' := by intros _ _ _; mono
  -- }
  -- def GlobalState.diverging : Set (GlobalState × List Behavior) := OrderHom.gfp GlobalState.diverging'

  -----------------------------------------------------------------------------------------------------

  -- theorem GlobalState.reducing'.ωcontinuous : OmegaCompletePartialOrder.ωScottContinuous ⇑GlobalState.reducing' := by
  --   apply OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
  --   exists OrderHom.monotone _
  --   intros chain
  --   unfold GlobalState.reducing'
  --   conv in (occs := *) OmegaCompletePartialOrder.ωSup _ => all_goals dsimp [OmegaCompletePartialOrder.ωSup]
  --   ext ⟨a, e, c⟩
  --   refine ⟨λ x_in ↦ ?_, λ x_in ↦ ?_⟩
  --   · rw [Set.mem_iUnion]
  --     simp [Relation.mem_lcomp₂] at x_in ⊢
  --     obtain ⟨b, e₁, ⟨P, P_in, P', red, b_procs_eq, b_code_eq⟩, e₂, ⟨i, _⟩, rfl⟩|⟨c_procs_eq, c_procs_empty, c_fifos_eq, c_code_eq, rfl⟩ := x_in
  --     · exists i
  --       left
  --       exists b, e₁
  --       and_intros
  --       · exists P, P_in, P'
  --       · exists e₂
  --     · exists 0
  --       right
  --       trivial
  --   · rw [Set.mem_iUnion] at x_in
  --     obtain ⟨i, x_in⟩ := x_in
  --     simp [Relation.mem_lcomp₂] at x_in ⊢
  --     obtain ⟨b, e₁, ⟨P, P_in, P', red, b_procs_eq, b_code_eq⟩, e₂, _, rfl⟩|⟨c_procs_eq, c_procs_empty, c_fifos_eq, c_code_eq, rfl⟩ := x_in
  --     · left
  --       exists b, e₁
  --       and_intros
  --       · exists P, P_in, P'
  --       · exists e₂
  --         and_intros
  --         · exists i
  --         · rfl
  --     · right
  --       trivial

  -- theorem GlobalState.mem_reducing {σ σ'} {ε} : (σ, ε, σ') ∈ GlobalState.reducing ↔ ∃ n > 0, (σ, ε, σ') ∈ GlobalState.reducing'^[n] ⊥ := by
  --   unfold GlobalState.reducing
  --   rw [fixedPoints.lfp_eq_sSup_iterate _ GlobalState.reducing'.ωcontinuous]
  --   constructor
  --   · intro h
  --     apply Set.mem_iUnion.mp at h
  --     obtain ⟨n, h⟩ := h
  --     cases n <;> try contradiction
  --     case succ n =>
  --     exists n + 1, Nat.add_one_pos _
  --   · rintro ⟨n, -, h⟩
  --     exact Set.mem_iUnion.mpr ⟨n, h⟩

  -- theorem jsp {f : Set (GlobalState × List Behavior)} : OrderDual.toDual (GlobalState.diverging' f) = GlobalState.diverging' f := rfl

  -- theorem jsp₂ {f : Set (GlobalState × List Behavior)} : GlobalState.diverging' (OrderDual.ofDual f) = GlobalState.diverging' f := rfl

  -- theorem jsp₃ : OrderHom.dual GlobalState.diverging' = OrderDual.toDual ∘ GlobalState.diverging' ∘ OrderDual.ofDual := by
  --   dsimp [OrderHom.dual, Function.comp_def]

  -- theorem jsp₄ {α} {chain : OmegaCompletePartialOrder.Chain (Set α)ᵒᵈ} : OmegaCompletePartialOrder.ωSup chain = ⋂ i, chain i := rfl

  -- theorem jsp₆ {ι α} {t : Set α} {s : ι → Set α} (h : ∀ (i : ι), t ⊂ s i) : t ⊂ ⋂ i, s i := by
  --   change t ⊆ ⋂ i, s i ∧ ¬⋂ i, s i ⊆ t
  --   and_intros
  --   · replace h : ∀ i, t ⊆ s i := λ i ↦ Set.ssubset_iff_subset_ne.mp (h i) |>.left
  --     apply le_iInf h
  --   · --have h' : ∀ i, ∃ x ∈ s i, x ∉ t := Set.exists_of_ssubset ∘' h
  --     intros iInf_le_t
  --     replace iInf_le_t : ∀ b, (∀ i, b ⊆ s i) → b ⊆ t := iInf_le_iff.mp iInf_le_t

  --     _admit

  -- /-- Given a chain `𝒞₀ ⊇ 𝒞₁ ⊇ … ⊇ 𝒞∞` such that its intersection is non-empty, there will be a point `i` from which all next `𝒞ₖ = 𝒞ᵢ`. -/
  -- theorem OmegaCompletePartialOrder.Chain.stable {α} (𝒞 : OmegaCompletePartialOrder.Chain (Set α)ᵒᵈ) (h : ⋂ i, 𝒞 i ≠ ∅) : ∃ i, ∀ k ≥ i, 𝒞 i = 𝒞 k := by
  --   have 𝒞_mono : ∀ m n, m ≤ n → OrderDual.ofDual (𝒞 m) ⊇ 𝒞 n := 𝒞.monotone'

  --   replace h : (⋂ i, 𝒞 i).Nonempty := Set.nonempty_iff_ne_empty.mpr h
  --   have inter_sub_all : ∀ (i : ℕ), (⋂ i, 𝒞 i) ⊆ 𝒞 i := by
  --     intros i x x_in_inter
  --     apply Set.mem_iInter.mp
  --     assumption
  --   have ex_i_𝒞_i_is_inter : ∃ i, OrderDual.ofDual (𝒞 i) = ⋂ j, 𝒞 j := by
  --     by_contra! h'
  --     replace inter_sub_all : ∀ (i : ℕ), (⋂ j, 𝒞 j) ⊂ 𝒞 i := by
  --       intros i
  --       apply HasSubset.Subset.ssubset_of_ne
  --       · exact inter_sub_all i
  --       · exact (h' i).symm
  --     have inter_ssub_inter : ⋂ j, 𝒞 j ⊂ ⋂ j, 𝒞 j := jsp₆ inter_sub_all
  --     apply ssubset_irrfl inter_ssub_inter

  --   suffices h : ∃ i, ∀ k ≥ i, ¬ OrderDual.ofDual (𝒞 i) ⊃ 𝒞 k by
  --     refine Exists.imp ?_ h
  --     intros i not_sup k k_ge_i
  --     specialize not_sup _ k_ge_i
  --     obtain _|h := ssubset_or_eq_of_subset (𝒞_mono _ _ k_ge_i)
  --     · contradiction
  --     · exact h.symm

  --   obtain ⟨m, m_in_𝒞, m_maximal_in_𝒞⟩ := zorn_le₀ (Set.range 𝒞) λ 𝒞' 𝒞'_sub 𝒞'_chain ↦ by
  --     exists ⋂ i, 𝒞 i
  --     and_intros
  --     · exact ex_i_𝒞_i_is_inter
  --     · intros z z_in_𝒞'
  --       apply Set.sInter_subset_of_mem
  --       exact 𝒞'_sub z_in_𝒞'

  --   refine Exists.imp ?_ m_in_𝒞
  --   rintro i (rfl) k k_ge_i
  --   specialize 𝒞_mono i k k_ge_i
  --   specialize @m_maximal_in_𝒞 (𝒞 k) (by exists k) 𝒞_mono

  --   have 𝒞_k_eq_𝒞_i : 𝒞 k = 𝒞 i := by apply PartialOrder.le_antisymm <;> assumption
  --   rw [𝒞_k_eq_𝒞_i]
  --   apply ssubset_irrfl

  -- theorem jsp₅ {f : OmegaCompletePartialOrder.Chain (Set (GlobalState × List Behavior))ᵒᵈ} (h : ⋂ i, f i ≠ ∅) : GlobalState.diverging' (⋂ i, f i) = ⋂ i, GlobalState.diverging' (f i) := by
  --   dsimp [GlobalState.diverging', Relation.lcomp₁]

  --   ext ⟨b, e⟩
  --   constructor
  --   · rintro ⟨a, e₁, e₂, ⟨P, P_in, P', P_red, b_procs_eq, b_code_eq⟩, b_in, rfl⟩
  --     rw [Set.mem_iInter] at b_in ⊢
  --     intro i

  --     exists a, e₁, e₂
  --     and_intros
  --     · exists P, P_in, P'
  --     · apply b_in
  --     · rfl
  --   · rintro b_in
  --     simp_rw [Set.mem_iInter] at b_in ⊢

  --     obtain ⟨i, stable⟩ := OmegaCompletePartialOrder.Chain.stable f h
  --     obtain ⟨a, e₁, e₂, ⟨P, P_in, P', P_red, b_procs_eq, b_code_eq⟩, b_in, rfl⟩ := b_in i

  --     exists a, e₁, e₂
  --     and_intros
  --     · exists P, P_in, P'
  --     · intro j

  --       have : ∀ k ≤ i, OrderDual.ofDual (f k) ⊇ OrderDual.ofDual (f i) := by
  --         intros _ _
  --         apply @f.monotone'
  --         assumption

  --       by_cases j_lt_i : j < i
  --       · apply this
  --         · exact Nat.le_of_succ_le j_lt_i
  --         · exact b_in
  --       · replace j_lt_i : j ≥ i := Nat.le_of_not_lt j_lt_i
  --         rwa [← stable _ j_lt_i]
  --     · rfl

  -- theorem GlobalState.diverging'.dual_ωcontinuous.{u, v} : OmegaCompletePartialOrder.ωScottContinuous ⇑(OrderHom.dual GlobalState.diverging'.{u, v}) := by
  --   apply OmegaCompletePartialOrder.ωScottContinuous.of_map_ωSup_of_orderHom
  --   intro 𝒞

  --   simp_rw [OrderHom.dual_apply_coe, Function.comp_def, jsp, jsp₂, jsp₄]
  --   change _ = ⋂ i, (OrderHom.dual diverging') (𝒞 i)
  --   simp_rw [OrderHom.dual_apply_coe, Function.comp_def, jsp, jsp₂]

  --   by_cases h : ⋂ i, 𝒞 i = ∅
  --   · have : diverging' (⋂ i, 𝒞 i) = ∅ := by rw [h]; apply Relation.lcomp₁.right_empty_eq_empty


  --     _admit
  --     -- have : (∃ i, 𝒞 i = OrderDual.toDual ∅) ∨ (∀ i, (𝒞 i).Infinite) := by
  --     --   rw [Set.iInter_eq_empty_iff] at h
  --     --   by_cases h' : ∃ i, 𝒞 i = OrderDual.toDual ∅
  --     --   · left
  --     --     assumption
  --     --   · push_neg at h'

  --     --     _admit
  --     -- _admit
  --   · apply jsp₅ h

  -- theorem GlobalState.mem_diverging {σ} {ε} : (σ, ε) ∈ GlobalState.diverging ↔ ∀ n, (σ, ε) ∈ GlobalState.diverging'^[n] ⊤ := by
  --   unfold GlobalState.diverging
  --   rw [fixedPoints.gfp_eq_sInf_iterate _ GlobalState.diverging'.dual_ωcontinuous]
  --   conv_lhs => apply propext Set.mem_iInter
