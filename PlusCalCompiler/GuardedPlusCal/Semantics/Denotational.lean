import PlusCalCompiler.GuardedPlusCal.Syntax
import Extra.Rel
import PlusCalCompiler.CoreTLAPlus.Semantics.Operational
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Filter
import Extra.AList
import Mathlib.Order.FixedPoints
import VerifiedCompiler.Denotational.Notations
import Extra.List

namespace GuardedPlusCal
  export CoreTLAPlus (Value Memory)

  /-- One of the possible behaviors exhibited by PlusCal statements. -/
  inductive Behavior.{u} : Type u
    | print (_ : Value.{u})
    | send (_ : ChanRef.{u} Value) (_ : Value.{u})
    --| recv (_ : ChanRef.{u} Value) (_ : Value.{u})

  /-!
    In the following, we dissociate channels from the main memory. This allows us to impose restrictions
    on what is allowed in expressions.
    Note that an expressions doing arbitrary things on channels on the PlusCal is expected to have
    an undefined behavior (or rather, to have no behavior at all).
  -/

  /-- The global map containing FIFOs. -/
  abbrev FIFOs.{u} : Type u := AList λ _ : String × List Value.{u} ↦ List Value.{u}

  /-- The local reduction state of an atomic block. -/
  inductive LocalState.{u} : Bool → Type u
    | running (M : Memory) (tmp : Memory) (F : FIFOs) : LocalState false
    | done (M : Memory) (tmp : Memory) (F : FIFOs) (l : String) : LocalState true

  def Memory.updateRef (M : Memory) (r : Ref Value) (v : Value) : Option Memory := do
    let v' ← M.lookup r.name
    let v' ← doUpdate v v' r.args
    return M.insert r.name v'
  where
    doUpdate (v' : Value) : Value → List (List Value) → Option Value
      | _, [] => return v'
      | fn@(.fn maps), v :: vs => do
        let tup := if let [v] := v then v else CoreTLAPlus.Value.tuple v
        -- If `tup` is in the domain of `fn`, then update
        if let .some ⟨_, v⟩ := maps.find? λ ⟨k, _⟩ ↦ k == tup then
          let v ← doUpdate v' v vs
          return .fn (maps.replaceF λ ⟨k, _⟩ ↦ if k == tup then .some ⟨tup, v⟩ else .none) -- (⟨tup, v⟩ :: maps.filter λ ⟨k, _⟩ ↦ k != tup)
        else
          return fn
      | _, _ => failure

  ------------

  -- class Denotation.{u} (α β γ : Type u) where
  --   /-- Finite traces ending in a state of type `γ`. -/
  --   reducing : Set (α × β × γ)
  --   /-- Finite traces that trigger abortion (e.g. when reaching stuff like `assert false`). -/
  --   aborting : Set (α × β)
  --   /-- (In)finite traces. -/
  --   diverging : Set (α × β)

  -- set_option synthInstance.checkSynthOrder false in
  -- instance {β γ δ : Type _} {α : outParam (Type _)} [Reduce α (Set (β × γ × δ))] [Abort α (Set (β × γ))] [Diverge α (Set (β × γ))] : (x : α) → Denotation β γ δ := λ x ↦ {
  --   reducing := ⟦x⟧*
  --   aborting := ⟦x⟧⊥
  --   diverging := ⟦x⟧∞
  -- }

  /-! # Reduction of statements -/

  -- for FIFOs, we push on the right, and pop on the left
  def Statement.reducing : {b b' : Bool} → Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) b b' → Set (LocalState false × List Behavior × LocalState b')
    | true, false, .let name _ «=|∈» e =>
      {⟨σ, ε, σ'⟩ | ∃ M T F v,
        T ∪ M ⊢ e ⇒ v ∧
        AList.lookup name (T ∪ M) = none ∧
        σ = .running M T F ∧ ε = [] ∧ match «=|∈», v with
          -- non empty set membership
          | true, .set vs => ∃ v' ∈ vs, σ' = .running M (T.insert name v') F
          | true, _ => False
          | false, v => σ' = .running M (T.insert name v) F
      }
    | true, false, .await e => test e (.bool true)
    | true, false, .receive chan ref =>
      {⟨σ, ε, σ'⟩ | ∃ M T F M' vs vss v vs',
        List.Forall₂ (T ∪ M ⊢ · ⇒ ·) chan.args vs ∧ List.Forall₂ (List.Forall₂ (T ∪ M ⊢ · ⇒ ·)) ref.args vss ∧
        F.lookup ⟨chan.name, vs⟩ = .some (v :: vs') ∧
        Memory.updateRef M {ref with args := vss} v = some M' ∧
        σ = .running M T F ∧ σ' = .running M' T (F.replace ⟨chan.name, vs⟩ vs') ∧ ε = []
      }
    | false, false, .skip => id
    | false, true, .goto label => {⟨σ, ε, σ'⟩ | ∃ M T F, σ = .running M T F ∧ σ' = .done M T F label ∧ ε = []}
    | false, false, .print e => {⟨σ, ε, σ'⟩ | ∃ M T F v, σ = .running M T F ∧ σ' = .running M T F ∧ T ∪ M ⊢ e ⇒ v ∧ ε = [.print v]}
    | false, false, .assert e => test e (.bool true)
    | false, false, .send chan e =>
      {⟨σ, ε, σ'⟩ | ∃ M T F v vs vs',
        T ∪ M ⊢ e ⇒ v ∧ List.Forall₂ (T ∪ M ⊢ · ⇒ ·) chan.args vs ∧
        F.lookup ⟨chan.name, vs⟩ = .some vs' ∧
        σ = .running M T F ∧ σ' = .running M T (F.replace ⟨chan.name, vs⟩ (vs'.concat v)) ∧ ε = [.send {chan with args := vs} v]
      }
    | false, false, .multicast chan filter e => sorry -- TODO:
    | false, false, .assign ref e =>
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
      {⟨σ, ε, σ'⟩ | ∃ M T F, σ = .running M T F ∧ σ' = .running M T F ∧ ε = []}

  def Statement.aborting : {b b' : Bool} → Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) b b' → Set (LocalState false × List Behavior)
    | true, false, .let name _ «=|∈» e =>
      -- the set of all states which fail to reduce `e`
      {⟨σ, ε⟩ | ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      -- the set of states that reduce `e` to anything else than a set when `«=|∈»` is `true`
      ∪ {⟨σ, ε⟩ | ∃ M T F v, T ∪ M ⊢ e ⇒ v ∧ σ = .running M T F ∧ ε = [] ∧ match «=|∈», v with
        | true, .set vs | false, _ => False
        | true, _ => True}
    | true, false, .await e =>
      {⟨σ, ε⟩ | ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      ∪ {⟨σ, ε⟩ | ∃ M T F v, (∀ b, v ≠ .bool b) ∧ T ∪ M ⊢ e ⇒ v ∧ σ = .running M T F ∧ ε = []}
    | true, false, .receive chan ref =>
      {⟨σ, ε⟩ | ∃ M T F, (ref.name ∉ M ∨ ref.name ∈ T) ∧ σ = .running M T F ∧ ε = []}
      ∪ {⟨σ, ε⟩ | ∃ M T F, σ = .running M T F ∧ ε = [] ∧ ∃ e ∈ chan.args, T ∪ M ⊢ e ↯}
      ∪ {⟨σ, ε⟩ | ∃ M T F, σ = .running M T F ∧ ε = [] ∧ ∃ e ∈ ref.args.flatten, T ∪ M ⊢ e ↯}
      ∪ {⟨σ, ε⟩ | ∃ M T F vs', σ = .running M T F ∧ ε = [] ∧ List.Forall₂ (T ∪ M ⊢ · ⇒ ·) chan.args vs' ∧
          F.lookup ⟨chan.name, vs'⟩ = .none}
      ∪ {⟨σ, ε⟩ | ∃ M T F vss v vs vs', σ = .running M T F ∧ ε = [] ∧ List.Forall₂ (T ∪ M ⊢ · ⇒ ·) chan.args vs' ∧
          List.Forall₂ (List.Forall₂ (T ∪ M ⊢ · ⇒ ·)) ref.args vss ∧
          F.lookup ⟨chan.name, vs'⟩ = .some (v :: vs) ∧ Memory.updateRef M {ref with args := vss} v = .none}
    | false, false, .skip => ∅
    | false, true, .goto label => ∅
    | false, false, .print e => {⟨σ, ε⟩ | ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
    | false, false, .assert e =>
      -- the set of all states that fail to reduce `e`
      {⟨σ, ε⟩ | ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      -- the set of all states that reduce `e` to something else than `TRUE`
      ∪ {⟨σ, ε⟩ | ∃ M T F v, v ≠ .bool true ∧ T ∪ M ⊢ e ⇒ v ∧ σ = .running M T F ∧ ε = []}
    | false, false, .send chan e =>
      {⟨σ, ε⟩ | ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      ∪ {⟨σ, ε⟩ | ∃ e ∈ chan.args, ∃ M T F, T ∪ M ⊢ e ↯ ∧ σ = .running M T F ∧ ε = []}
      ∪ {⟨σ, ε⟩ | ∃ M T F vs, List.Forall₂ (T ∪ M ⊢ · ⇒ ·) chan.args vs ∧
        F.lookup ⟨chan.name, vs⟩ = none ∧ σ = .running M T F ∧ ε = []}
    | false, false, .multicast chan filter e => sorry
    | false, false, .assign ref e =>
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

  instance instReduceStatement {b b' : Bool} : Reduce (Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) b b') (Set (LocalState false × List Behavior × LocalState b')) := ⟨Statement.reducing⟩
  instance instAbortStatement {b b' : Bool} : Abort (Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) b b') (Set (LocalState false × List Behavior)) := ⟨Statement.aborting⟩
  instance instDivergeStatement {b b' : Bool} : Diverge (Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) b b') (Set (LocalState false × List Behavior)) := ⟨Statement.diverging⟩

  /-! # Reduction of blocks -/

  def Block.reducing {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (B : Block α b) : Set (β false × γ × β b) :=
    match _h : B.begin with
    | [] => f B.last
    | x :: xs => f x ∘ᵣ₂ Block.reducing f {B with begin := xs}
  termination_by B.begin
  decreasing_by
    all_goals simp_wf
    · rw [_h]; decreasing_trivial

  def Block.aborting {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} (f : ⦃b : Bool⦄ → α b → Set (β false × γ)) (g : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (B : Block α b) : Set (β false × γ) :=
    match _h : B.begin with
    | [] => f B.last
    | x :: xs => f x ∪ g x ∘ᵣ₁ Block.aborting f g {B with begin := xs}
  termination_by B.begin
  decreasing_by
    all_goals simp_wf
    · rw [_h]; decreasing_trivial

  def Block.diverging {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} (f : ⦃b : Bool⦄ → α b → Set (β false × γ)) (g : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (B : Block α b) : Set (β false × γ) :=
    match _h : B.begin with
    | [] => f B.last
    | x :: xs => f x ∪ g x ∘ᵣ₁ Block.diverging f g {B with begin := xs}
  termination_by B.begin
  decreasing_by
    all_goals simp_wf
    · rw [_h]; decreasing_trivial

  instance instReduceBlock {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} [reduceα : ⦃b : Bool⦄ → Reduce (α b) (Set (β false × γ × β b))] : Reduce (Block α b) (Set (β false × γ × β b)) where
    reducing := Block.reducing λ ⦃b⦄ ↦ reduceα (b := b) |>.reducing
  instance instAbortBlock {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} [abortα : ⦃b : Bool⦄ → Abort (α b) (Set (β false × γ))] [reduceα : ⦃b : Bool⦄ → Reduce (α b) (Set (β false × γ × β b))] :
    Abort (Block α b) (Set (β false × γ)) where
      abort := Block.aborting (λ ⦃b⦄ ↦ abortα (b := b) |>.abort) (λ ⦃b⦄ ↦ reduceα (b := b) |>.reducing)
  instance instDivergeBlock {α β : Bool → Type _} {γ : Type _} [Monoid γ] {b : Bool} [divα : ⦃b : Bool⦄ → Diverge (α b) (Set (β false × γ))] [reduceα : ⦃b : Bool⦄ → Reduce (α b) (Set (β false × γ × β b))] :
    Diverge (Block α b) (Set (β false × γ)) where
      div := Block.diverging (λ ⦃b⦄ ↦ divα (b := b) |>.div) (λ ⦃b⦄ ↦ reduceα (b := b) |>.reducing)

  instance instReduceAtomicBranch : Reduce (AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) (Set (LocalState false × List Behavior × LocalState true)) where
    reducing B := B.precondition.elim {⟨x, e, y⟩ | x = y ∧ e = 1} (⟦·⟧*) ∘ᵣ₂ ⟦B.action⟧*
  instance instAbortAtomicBranch : Abort (AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) (Set (LocalState false × List Behavior)) where
    abort B := match B.precondition with
      | .none => ⟦B.action⟧⊥
      | .some B' => ⟦B'⟧⊥ ∪ ⟦B'⟧* ∘ᵣ₁ ⟦B.action⟧⊥
  instance instDivergeAtomicBranch : Diverge (AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) (Set (LocalState false × List Behavior)) where
    div B := match B.precondition with
      | .none => ⟦B.action⟧∞
      | .some B' => ⟦B'⟧∞ ∪ ⟦B'⟧* ∘ᵣ₁ ⟦B.action⟧∞

  -- /-! # Reduction of processes -/

  -- structure ProcessState.{u} : Type u where
  --   /-- A view of the local variables of a process. -/
  --   localMemory : Memory.{u}
  --   /-- The process identifier -/
  --   self : Value.{u}
  --   /-- All the labels to be concurrently executing in a single process. -/
  --   labels : Multiset String
  --   deriving DecidableEq

  -- def Process.reducing.{u, v} (Ξ : AList λ _ : String ↦ List (AtomicBranch.{u} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ))) (F : FIFOs.{v}) : Set (ProcessState.{v} × List Behavior.{v} × ProcessState.{v} × FIFOs.{v}) :=
  --   {⟨⟨M, self, L⟩, ε, ⟨M', self', L'⟩, F'⟩ | ∃ T', ∃ l ∈ L, ∃ h : l ∈ Ξ, ∃ B ∈ Ξ.get l h, ∃ l',
  --     ⟨.running M (AList.singleton "self" self) F, ε, .done M' T' F' l'⟩ ∈ ⟦B⟧* ∧
  --     L' = (l' ::ₘ (L - {l})).filter (· ≠ "Done") ∧
  --     self' = self
  --   }

  -- def Process.aborting (Ξ : AList λ _ : String ↦ List (AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ))) (F : FIFOs) : Set (ProcessState × List Behavior) :=
  --   {⟨⟨M, self, L⟩, ε⟩ | ∃ l ∈ L, ∃ h : l ∈ Ξ, ∃ B ∈ Ξ.get l h, ⟨.running M (AList.singleton "self" self) F, ε⟩ ∈ ⟦B⟧⊥}

  -- def Process.diverging (Ξ : AList λ _ : String ↦ List (AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ))) (F : FIFOs) : Set (ProcessState × List Behavior) :=
  --   {⟨⟨M, self, L⟩, ε⟩ | ∃ l ∈ L, ∃ h : l ∈ Ξ, ∃ B ∈ Ξ.get l h, ⟨.running M (AList.singleton "self" self) F, ε⟩ ∈ ⟦B⟧∞}

  -- /-! # Global ("distributed") reduction -/

  -- structure GlobalState.{u, v} : Type (max u v) where
  --   procs : Multiset ProcessState.{u}
  --   /-- The state of all FIFOs of the system. -/
  --   fifos : FIFOs.{u}
  --   /-- A mapping from (globally unique) labels to branches to be executed. -/
  --   code : AList λ _ : String ↦ List (AtomicBranch.{v} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ))

  -- -- the parameter `f` in `reducing` and `diverging` is there for fixed point construction

  -- def GlobalState.reducing'.{u, v} (f : Set (GlobalState.{u, v} × List Behavior.{u} × GlobalState.{u, v})) : Set (GlobalState.{u, v} × List Behavior.{u} × GlobalState.{u, v}) :=
  --   {⟨⟨Ps, F, Ξ⟩, ε, ⟨Ps', F', Ξ'⟩⟩ : GlobalState × _ × GlobalState | ∃ P ∈ Ps, ∃ P',
  --     ⟨P, ε, P', F'⟩ ∈ Process.reducing Ξ F ∧ Ps' = Ps - {P} + {P'} ∧ Ξ' = Ξ} ∘ᵣ₂ f
  -- def GlobalState.reducing : Set (GlobalState × List Behavior × GlobalState) := OrderHom.lfp {
  --   toFun := GlobalState.reducing'
  --   monotone' := by intros _ _ _; unfold GlobalState.reducing'; mono
  -- }

  -- /-- A `GlobalState` is aborting if, after any number of reductions, one of its processes aborts. -/
  -- def GlobalState.aborting : Set (GlobalState × List Behavior) :=
  --   GlobalState.reducing ∘ᵣ₁ {⟨⟨Ps, F, Ξ⟩, ε⟩ : GlobalState × _ | ∃ P ∈ Ps, ⟨P, ε⟩ ∈ Process.aborting Ξ F}

  -- def GlobalState.diverging' (f : Set (GlobalState × List Behavior)) : Set (GlobalState × List Behavior) :=
  --   GlobalState.reducing ∘ᵣ₁ f
  -- def GlobalState.diverging : Set (GlobalState × List Behavior) := OrderHom.gfp {
  --   toFun := GlobalState.diverging'
  --   monotone' := by intros _ _ _; unfold GlobalState.diverging'; mono
  -- }
