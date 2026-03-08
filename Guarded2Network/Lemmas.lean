import Guarded2Network.PlusCal
import Core.GuardedPlusCal.Semantics.Denotational
import Core.TypedSetTheory.Semantics.Lemmas
import Core.TypedSetTheory.Syntax.WellScopedness
import Core.GuardedPlusCal.Semantics.Lemmas
import Core.GuardedPlusCal.Syntax.Lemmas
import Core.GuardedPlusCal.Syntax.WellScopedness
import Core.NetworkPlusCal.Semantics.Denotational
import Core.NetworkPlusCal.Semantics.Lemmas
import VerifiedCompiler.Denotational.StrongRefinement
import Mathlib.Algebra.Ring.Parity
import Extra.List
import Extra.Nat
import Extra.String
import Extra.Option

open Std.Do
set_option mvcgen.warning false

instance {α : Type _} : Trace (List α) where
  -- mul_left_cancel _ _ _ := List.append_cancel_left
  -- mul_right_cancel _ _ _ := List.append_cancel_right
  le := (· <+: ·)
  le_refl x := List.prefix_rfl
  le_trans x y z := List.IsPrefix.trans
  le_antisymm x y h₁ h₂ := by
    apply List.IsPrefix.eq_of_length_le
    · exact h₁
    · exact List.IsPrefix.length_le h₂
  le_mul_right_inj x y z x_le_y := by
    unfold_projs at x_le_y ⊢
    erwa [List.prefix_append_right_inj]
  le_extend_mul x y z x_le_y := by
    obtain ⟨w, rfl⟩ := x_le_y
    exists w ++ z
    erw [← List.append_assoc]
    rfl

open TypedSetTheory (Expression Typ Value)

namespace GuardedPlusCal
  protected structure AtomicBranch.wellFormed.{u}
      (inbox : String) (mailbox : Option (Expression Typ)) (procName : String)
      (fifos : Std.HashMap String (Typ.{u} × List (Expression Typ)))
      (Br : AtomicBranch.{u} Typ (Expression Typ)) : Prop where
    precond_wf : match Br.precondition with
      | .some B => ∀ S ∈ B.toList, match S with
        -- Every `receive` does so from its mailbox (there must be one) which is well-typed.
        | .receive c _ => ∃ v, mailbox = .some v ∧ match v with
          | .var x (.channel τ) => c.name = x ∧ c.τ = .channel τ ∧ c.args = [] ∧ Prod.fst <$> fifos.find? c.name = .some (.channel τ)
          | .funcall (.var x (.function .address (.channel τ))) [.var "self" .address] => c.name = x ∧ c.τ = .function .address (.channel τ) ∧ c.args = [.var "self" .address] ∧ Prod.fst <$> fifos.find? c.name = .some (.function .address (.channel τ))
          | _ => False
        | .await _ => True
        | .let _ _ _ _ => True
      | .none => True

  protected structure Process.wellFormed
      (P : Process Typ (Expression Typ)) (inbox : String)
      (fifos : Std.HashMap String (Typ × List (Expression Typ))) : Prop where
    -- If there is a mailbox, then it must be of the form `c[self]` or just `c`.
    mailbox_shape : match P.mailbox with
      | .some (.var _ _) | .some (.funcall (.var _ _) [.var "self" _]) => True
      | _ => False
    -- All branches of all blocks of all threads of all processes are well formed.
    blocks_wf : ∀ T ∈ P.threads, ∀ B ∈ T, ∀ Br ∈ B.branches, Br.wellFormed inbox P.mailbox P.name fifos

  protected structure Algorithm.wellFormed (A : Algorithm Typ (Expression Typ)) («Σ» : Scope) (inbox : String) : Prop where
    «Σ_contains_prims» : TypedSetTheory.prims.keys.toFinset ⊆ «Σ»
    -- `inbox ++ proc_name` is fresh in the whole process, ONLY if the process has a mailbox
    inbox_fresh : ∀ P ∈ A.procs, match P.mailbox with
      | .none => True
      | .some _ => inbox ++ P.name ∉ «Σ» ∧ Process.FreshIn Expression.FreshIn P (inbox ++ P.name)
    A_wellscoped : A.WellScoped (flip Expression.WellScoped) «Σ»
    -- All processes in the algorithm are well formed.
    procs_wf : ∀ P ∈ A.procs, P.wellFormed inbox (A.channels.mergeWith (λ _ v _ ↦ v) A.fifos)






  abbrev LocalState'.{u} := TypedSetTheory.Memory.{u} × TypedSetTheory.Memory.{u} × FIFOs.{u} × Option String
  abbrev LocalState'.mk.{u} (w x : TypedSetTheory.Memory.{u}) (y : FIFOs.{u}) (z : Option String) : LocalState'.{u} := ⟨w, x, y, z⟩

  instance instReduceStatement' {b b' : Bool} : Reduce (Statement Typ (Expression Typ) b b') (Set (LocalState' × List Behavior × LocalState')) where
    reducing S := {⟨⟨M, T, F, l⟩, ε, ⟨M', T', F', l'⟩⟩ | ∃ (σ' : LocalState b'), l = .none ∧ ⟨.running M T F, ε, σ'⟩ ∈ ⟦S⟧* ∧ match b' with | true => ∃ l'', σ' = .done M' T' F' l'' ∧ l' = .some l'' | false => σ' = .running M' T' F' ∧ l' = .none}
  instance instAbortStatement' {b b' : Bool} : Abort (Statement Typ (Expression Typ) b b') (Set (LocalState' × List Behavior)) where
    abort S := {⟨⟨M, T, F, l⟩, ε⟩ | l = .none ∧ ⟨.running M T F, ε⟩ ∈ ⟦S⟧⊥}
  instance instDivergeStatement' {b b' : Bool} : Diverge (Statement Typ (Expression Typ) b b') (Set (LocalState' × List Behavior)) where
    div S := {⟨⟨M, T, F, l⟩, ε⟩ | l = .none ∧ ⟨.running M T F, ε⟩ ∈ ⟦S⟧∞}

  instance instReduceBlock' {α : Bool → Type _} {β γ : Type _} [Monoid γ] {b : Bool} [reduceα : ⦃b : Bool⦄ → Reduce (α b) (Set (β × γ × β))] : Reduce (Block α b) (Set (β × γ × β)) where
    reducing B := instReduceBlock (β := λ _ ↦ β) |>.reducing B
  instance instAbortBlock' {α : Bool → Type _} {β γ : Type _} [Monoid γ] {b : Bool} [abortα : ⦃b : Bool⦄ → Abort (α b) (Set (β × γ))] [reduceα : ⦃b : Bool⦄ → Reduce (α b) (Set (β × γ × β))] :
    Abort (Block α b) (Set (β × γ)) where
      abort B := instAbortBlock (β := λ _ ↦ β) |>.abort B
  instance instDivergeBlock' {α : Bool → Type _} {β γ : Type _} [Monoid γ] {b : Bool} [divα : ⦃b : Bool⦄ → Diverge (α b) (Set (β × γ))] [reduceα : ⦃b : Bool⦄ → Reduce (α b) (Set (β × γ × β))] :
    Diverge (Block α b) (Set (β × γ)) where
      div B := instDivergeBlock (β := λ _ ↦ β) |>.div B

  instance instReduceAtomicBranch' : Reduce (AtomicBranch Typ (Expression Typ)) (Set (LocalState' × List Behavior × LocalState')) where
    reducing Br := {⟨⟨M, T, F, l⟩, ε, ⟨M', T', F', l'⟩⟩ | ∃ l'', ⟨.running M T F, ε, .done M' T' F' l''⟩ ∈ ⟦Br⟧* ∧ l = .none ∧ l' = .some l''}
  instance instAbortAtomicBranch' : Abort (AtomicBranch Typ (Expression Typ)) (Set (LocalState' × List Behavior)) where
    abort Br := {⟨⟨M, T, F, l⟩, ε⟩ | l = .none ∧ ⟨.running M T F, ε⟩ ∈ ⟦Br⟧⊥}
  instance instDivergeAtomicBranch' : Diverge (AtomicBranch Typ (Expression Typ)) (Set (LocalState' × List Behavior)) where
    div Br := {⟨⟨M, T, F, l⟩, ε⟩ | l = .none ∧ ⟨.running M T F, ε⟩ ∈ ⟦Br⟧∞}

  attribute [-instance] instReduceStatement instAbortStatement instDivergeStatement instReduceBlock instAbortBlock instDivergeBlock instReduceAtomicBranch instAbortAtomicBranch instDivergeAtomicBranch

  instance : Reduce (AtomicBlock Typ (Expression Typ)) (Set (LocalState' × List Behavior × LocalState')) where
    reducing B := {⟨st, ε, st'⟩ | ∃ Br ∈ B.branches, ⟨st, ε, st'⟩ ∈ ⟦Br⟧*}
  instance : Abort (GuardedPlusCal.AtomicBlock Typ (Expression Typ)) (Set (LocalState' × List Behavior)) where
    abort B := {⟨st, ε⟩ | ∃ Br ∈ B.branches, ⟨st, ε⟩ ∈ ⟦Br⟧⊥}
  instance : Diverge (GuardedPlusCal.AtomicBlock Typ (Expression Typ)) (Set (LocalState' × List Behavior)) where
    div B := {⟨st, ε⟩ | ∃ Br ∈ B.branches, ⟨st, ε⟩ ∈ ⟦Br⟧∞}

  -----------------

  private theorem mem_sem_iff.{u} (σₜ σₜ' : LocalState'.{u}) (ε : List GuardedPlusCal.Behavior.{u})
    (S : Statement.{u} Typ (Expression Typ) false true)
    : (σₜ, ε, σₜ') ∈ ⟦S⟧* ↔ ∃ M T F M' T' F' l', σₜ = ⟨M, T, F, .none⟩ ∧ σₜ' = ⟨M', T', F', .some l'⟩ ∧ ⟨.running M T F, ε, .done M' T' F' l'⟩ ∈ instReduceStatement.reducing S where
      mp := by
        rintro ⟨_, σₜ_l_eq, _, l, rfl, σₜ'_l_eq⟩
        exists σₜ.fst, σₜ.snd.fst, σₜ.snd.snd.fst, σₜ'.fst, σₜ'.snd.fst, σₜ'.snd.snd.fst, l
        and_intros
        · rw [← σₜ_l_eq]
        · rw [← σₜ'_l_eq]
        · assumption
      mpr := by
        rintro ⟨_, _, _, M', T', F', l, rfl, rfl, _⟩
        exists .done M' T' F' l
        and_intros
        · rfl
        · assumption
        · split
          · exists l
          · contradiction

  private theorem Block.sem_left_append_eq_comp'
    {b : Bool} {α β} {F : Bool → Type _} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))]
    {A : List (F false)} {B : Block F b} :
    ⟦{ B with begin := A ++ B.begin }⟧* = List.foldl (fun sem x ↦ sem ∘ᵣ₂ ⟦x⟧*) {(x, e, y) | x = y ∧ e = 1} A ∘ᵣ₂ ⟦B⟧* :=
      Block.sem_left_append_eq_comp

  private theorem Block.sem_prepend_eq_comp'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))]
    {A : List (F false)} {B : Block F b} :
    ⟦B.prepend A⟧* = A.foldl (init := {⟨x, e, y⟩ | x = y ∧ e = 1}) (λ sem x ↦ sem ∘ᵣ₂ ⟦x⟧*) ∘ᵣ₂ ⟦B⟧* :=
      Block.sem_left_append_eq_comp

  private theorem Block.sem_end'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))]
    {S : F b} : ⟦«end» S⟧* = ⟦S⟧* :=
      Block.sem_end

  private theorem Block.sem_cons'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))]
    {B : Block F b} {S : F false} : ⟦cons S B⟧* = ⟦S⟧* ∘ᵣ₂ ⟦B⟧* :=
      Block.sem_cons

  private theorem Block.abort_end'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))] [⦃b : Bool⦄ → Abort (F b) (Set (α × β))]
    {S : F b} : ⟦«end» S⟧⊥ = ⟦S⟧⊥ :=
      Block.abort_end

  theorem Block.abort_cons'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))] [⦃b : Bool⦄ → Abort (F b) (Set (α × β))]
    {S : F false} {B : Block F b} :
    ⟦cons S B⟧⊥ = ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ ⟦B⟧⊥ :=
      Block.abort_cons

  private theorem Block.div_end'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))] [⦃b : Bool⦄ → Diverge (F b) (Set (α × β))]
    {S : F b} : ⟦«end» S⟧∞ = ⟦S⟧∞ :=
      Block.div_end

  theorem Block.div_cons'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))] [⦃b : Bool⦄ → Diverge (F b) (Set (α × β))]
    {S : F false} {B : Block F b} :
    ⟦cons S B⟧∞ = ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ ⟦B⟧∞ :=
      Block.div_cons

  theorem Block.sem_eq_foldr'
    {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))]
    {B : Block F false} :
    ⟦B⟧* = List.foldr (⟦·⟧* ∘ᵣ₂ ·) {⟨x, e, y⟩ | x = y ∧ e = 1} B.toList :=
      Block.sem_eq_foldr

  theorem Block.abort_eq_foldr'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))] [⦃b : Bool⦄ → Abort (F b) (Set (α × β))]
    {B : Block F b} :
    ⟦B⟧⊥ = List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ⟦B.last⟧⊥ B.begin :=
      Block.abort_eq_foldr

  theorem Block.div_eq_foldr'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))] [⦃b : Bool⦄ → Diverge (F b) (Set (α × β))]
    {B : Block F b} :
    ⟦B⟧∞ = List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ⟦B.last⟧∞ B.begin :=
      Block.div_eq_foldr

  theorem Block.abort_eq_foldr_toList'
    {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))] [⦃b : Bool⦄ → Abort (F b) (Set (α × β))]
    {B : Block F false} :
    ⟦B⟧⊥ = List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ B.toList :=
      Block.abort_eq_foldr_toList

  theorem Block.sem_concat'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [reduceF : ⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))]
    {B : Block F false} {S : F b} :
    ⟦B.concat S⟧* = ⟦B⟧* ∘ᵣ₂ ⟦S⟧* :=
      Block.sem_concat

  theorem Block.abort_concat'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))] [⦃b : Bool⦄ → Abort (F b) (Set (α × β))]
    {S : F b} {B : Block F false} :
    ⟦B.concat S⟧⊥ = ⟦B⟧⊥ ∪ ⟦B⟧* ∘ᵣ₁ ⟦S⟧⊥ :=
      Block.abort_concat

  theorem Block.div_concat'
    {b : Bool} {F : Bool → Type _}
    {α β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))] [⦃b : Bool⦄ → Diverge (F b) (Set (α × β))]
    {S : F b} {B : Block F false} :
    ⟦B.concat S⟧∞ = ⟦B⟧∞ ∪ ⟦B⟧* ∘ᵣ₁ ⟦S⟧∞ :=
      Block.div_concat

  private theorem Block.abort_left_append_eq_comp'
    {b : Bool} {α β} {F : Bool → Type _} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))] [⦃b : Bool⦄ → Abort (F b) (Set (α × β))]
    {A : List (F false)} {B : Block F b} :
    ⟦{ B with begin := A ++ B.begin }⟧⊥ = List.foldr (fun x sem ↦ ⟦x⟧⊥ ∪ ⟦x⟧* ∘ᵣ₁ sem) ⟦B⟧⊥ A :=
      Block.abort_left_append_eq_comp

  private theorem Block.div_left_append_eq_comp'
    {b : Bool} {α β} {F : Bool → Type _} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α × β × α))] [⦃b : Bool⦄ → Diverge (F b) (Set (α × β))]
    {A : List (F false)} {B : Block F b} :
    ⟦{ B with begin := A ++ B.begin }⟧∞ = List.foldr (fun x sem ↦ ⟦x⟧∞ ∪ ⟦x⟧* ∘ᵣ₁ sem) ⟦B⟧∞ A :=
      Block.div_left_append_eq_comp
end GuardedPlusCal

attribute [-instance] GuardedPlusCal.instReduceStatement GuardedPlusCal.instAbortStatement GuardedPlusCal.instDivergeStatement GuardedPlusCal.instReduceBlock GuardedPlusCal.instAbortBlock GuardedPlusCal.instDivergeBlock GuardedPlusCal.instReduceAtomicBranch GuardedPlusCal.instAbortAtomicBranch GuardedPlusCal.instDivergeAtomicBranch

namespace NetworkPlusCal
  abbrev LocalState'.{u} := TypedSetTheory.Memory.{u} × TypedSetTheory.Memory.{u} × FIFOs.{u} × Option String

  instance instReduceAtomicBlock : Reduce (AtomicBlock Typ (Expression Typ)) (Set (LocalState' × List Behavior × LocalState')) where
    reducing B := {⟨⟨M, T, F, l⟩, ε, ⟨M', T', F', l'⟩⟩ | ∃ Br ∈ B.branches, ∃ l'', ⟨.running M T F, ε, .done M' T' F' l''⟩ ∈ ⟦Br⟧* ∧ l = .none ∧ l' = .some l''}
  instance instAbortAtomicBlock : Abort (AtomicBlock Typ (Expression Typ)) (Set (LocalState' × List Behavior)) where
    abort B := {⟨⟨M, T, F, l⟩, ε⟩ | ∃ Br ∈ B.branches, ⟨.running M T F, ε⟩ ∈ ⟦Br⟧⊥ ∧ l = .none}
  instance instDivergeAtomicBlock : Diverge (AtomicBlock Typ (Expression Typ)) (Set (LocalState' × List Behavior)) where
    div B := {⟨⟨M, T, F, l⟩, ε⟩ | ∃ Br ∈ B.branches, ⟨.running M T F, ε⟩ ∈ ⟦Br⟧∞ ∧ l = .none}

  @[reducible] instance instReduceStatement'.{u} {b b' : Bool} : Reduce (Statement.{u} Typ (Expression Typ) b b') (Set (LocalState'.{u} × List Behavior.{u} × LocalState'.{u})) where
    reducing S := {⟨⟨M, T, F, l⟩, ε, ⟨M', T', F', l'⟩⟩ | ∃ (σ' : LocalState b'), l = .none ∧ ⟨.running M T F, ε, σ'⟩ ∈ ⟦S⟧* ∧ match b' with | true => ∃ l'', σ' = .done M' T' F' l'' ∧ l' = .some l'' | false => σ' = .running M' T' F' ∧ l' = .none}
  @[reducible] instance instAbortStatement'.{u} {b b' : Bool} : Abort (Statement.{u} Typ (Expression Typ) b b') (Set (LocalState'.{u} × List Behavior.{u})) where
    abort S := {⟨⟨M, T, F, l⟩, ε⟩ | l = .none ∧ ⟨.running M T F, ε⟩ ∈ ⟦S⟧⊥}
  @[reducible] instance instDivergeStatement'.{u} {b b' : Bool} : Diverge (Statement.{u} Typ (Expression Typ) b b') (Set (LocalState'.{u} × List Behavior.{u})) where
    div S := {⟨⟨M, T, F, l⟩, ε⟩ | l = .none ∧ ⟨.running M T F, ε⟩ ∈ ⟦S⟧∞}

  instance instReduceAtomicBranch'.{u} : Reduce (AtomicBranch.{u} Typ (Expression Typ)) (Set (LocalState'.{u} × List Behavior.{u} × LocalState'.{u})) where
    reducing Br := {⟨⟨M, T, F, l⟩, ε, ⟨M', T', F', l'⟩⟩ | ∃ l'', ⟨.running M T F, ε, .done M' T' F' l''⟩ ∈ ⟦Br⟧* ∧ l = .none ∧ l' = .some l''}
  instance instAbortAtomicBranch'.{u} : Abort (AtomicBranch.{u} Typ (Expression Typ)) (Set (LocalState'.{u} × List Behavior.{u})) where
    abort Br := {⟨⟨M, T, F, l⟩, ε⟩ | l = .none ∧ ⟨.running M T F, ε⟩ ∈ ⟦Br⟧⊥}
  instance instDivergeAtomicBranch'.{u} : Diverge (AtomicBranch.{u} Typ (Expression Typ)) (Set (LocalState'.{u} × List Behavior.{u})) where
    div Br := {⟨⟨M, T, F, l⟩, ε⟩ | l = .none ∧ ⟨.running M T F, ε⟩ ∈ ⟦Br⟧∞}

  attribute [-instance] instReduceStatement instAbortStatement instDivergeStatement instReduceAtomicBranch instAbortAtomicBranch instDivergeAtomicBranch

  -- Ignore RX threads for now
  def Thread.toBlocks.{u} {Typ Expr : Type u} : Thread Typ Expr → List (AtomicBlock Typ Expr)
    | .code blocks => blocks
    | .rx .. => []

  @[simp] theorem Thread.toBlocks.code.{u} {Typ Expr : Type u} {Bs : List (AtomicBlock Typ Expr)} : (Thread.code Bs).toBlocks = Bs := rfl

  def Thread.isRx.{u} {Typ Expr : Type u} : Thread Typ Expr → Prop
    | .rx .. => True
    | .code .. => False

  ----------

  private theorem mem_sem_iff₁.{u} (σₜ σₜ' : LocalState'.{u}) (ε : List GuardedPlusCal.Behavior)
    {b} (S : Statement.{u} Typ (Expression Typ) b true) :
    (σₜ, ε, σₜ') ∈ ⟦S⟧* ↔ ∃ M T F M' T' F' l', σₜ = ⟨M, T, F, .none⟩ ∧ σₜ' = ⟨M', T', F', .some l'⟩ ∧ ⟨.running M T F, ε, .done M' T' F' l'⟩ ∈ instReduceStatement.reducing S where
      mp := by
        rintro ⟨_, σₜ_l_eq, _, l, rfl, σₜ'_l_eq⟩
        exists σₜ.fst, σₜ.snd.fst, σₜ.snd.snd.fst, σₜ'.fst, σₜ'.snd.fst, σₜ'.snd.snd.fst, l
        and_intros
        · rw [← σₜ_l_eq]
        · rw [← σₜ'_l_eq]
        · assumption
      mpr := by
        rintro ⟨_, _, _, M', T', F', l, rfl, rfl, _⟩
        exists .done M' T' F' l
        and_intros
        · rfl
        · assumption
        · split
          · exists l
          · contradiction

  private theorem mem_sem_iff₂.{u} (σₜ σₜ' : LocalState'.{u}) (ε : List GuardedPlusCal.Behavior)
    {b} (S : Statement.{u} Typ (Expression Typ) b false) :
    (σₜ, ε, σₜ') ∈ ⟦S⟧* ↔ ∃ M T F M' T' F', σₜ = ⟨M, T, F, .none⟩ ∧ σₜ' = ⟨M', T', F', .none⟩ ∧ ⟨.running M T F, ε, .running M' T' F'⟩ ∈ instReduceStatement.reducing S where
      mp := by
        rintro ⟨_|_, σₜ_l_eq, _, _|_, σₜ'_l_eq⟩
        exists σₜ.1, σₜ.2.1, σₜ.2.2.1, σₜ'.1, σₜ'.2.1, σₜ'.2.2.1
        and_intros
        · rw [← σₜ_l_eq]
        · rw [← σₜ'_l_eq]
        · assumption
      mpr := by
        rintro ⟨_, _, _, M', T', F', rfl, rfl, _⟩
        exists .running M' T' F'
end NetworkPlusCal

attribute [-instance] NetworkPlusCal.instReduceStatement NetworkPlusCal.instAbortStatement NetworkPlusCal.instReduceAtomicBranch NetworkPlusCal.instAbortAtomicBranch

private def NetworkPlusCal.LocalState.toLocalState' : {b : Bool} → NetworkPlusCal.LocalState b → NetworkPlusCal.LocalState'
  | false, .running M T F => ⟨M, T, F, .none⟩
  | true, .done M T F l => ⟨M, T, F, .some l⟩

private def GuardedPlusCal.LocalState.toLocalState' : {b : Bool} → GuardedPlusCal.LocalState b → GuardedPlusCal.LocalState'
  | false, .running M T F => ⟨M, T, F, .none⟩
  | true, .done M T F l => ⟨M, T, F, .some l⟩

theorem NetworkPlusCal.LocalState.toLocalState'_inj ⦃b⦄ : Function.Injective (@NetworkPlusCal.LocalState.toLocalState' b) := by
  cases b with
  | false => rintro ⟨M, T, F⟩ ⟨M', T', F'⟩ (_|_); rfl
  | true => rintro (_|⟨M, T, F, l⟩) (_|⟨M', T', F', l'⟩) (_|_); rfl

theorem GuardedPlusCal.LocalState.toLocalState'_inj ⦃b⦄ : Function.Injective (@GuardedPlusCal.LocalState.toLocalState' b) := by
  cases b with
  | false => rintro ⟨M, T, F⟩ ⟨M', T', F'⟩ (_|_); rfl
  | true => rintro (_|⟨M, T, F, l⟩) (_|⟨M', T', F', l'⟩) (_|_); rfl

theorem GuardedPlusCal.Block.reducing_map {α β δ : Bool → Type _} {γ} [Monoid γ] {b} {B : GuardedPlusCal.Block α b}
  (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (g : ⦃b : Bool⦄ → β b → δ b) (g_inj : ∀ ⦃b⦄, Function.Injective (@g b)) :
  Prod.map₃ (@g _) id (@g _) '' GuardedPlusCal.Block.reducing f B = GuardedPlusCal.Block.reducing (λ ⦃_⦄ x ↦ Prod.map₃ (@g _) id (@g _) '' f x) B := by
    induction B using GuardedPlusCal.Block.reducing.induct with
    | case1 B _ =>
      let ⟨[], _⟩ := B
      repeat rw [GuardedPlusCal.Block.reducing]
    | case2 B S Ss h IH =>
      let ⟨_ :: _, _⟩ := B
      cases h
      repeat rw [GuardedPlusCal.Block.reducing]
      dsimp at IH ⊢
      rw [← IH]

      ext ⟨a', e, c'⟩
      constructor
      · rintro ⟨⟨a, e, c⟩, ⟨b, e₁, e₂, _, _, rfl⟩, _|_⟩
        exists g b, e₁, e₂
        and_intros
        · exists ⟨a, e₁, b⟩
        · exists ⟨b, e₂, c⟩
        · rfl
      · rintro ⟨b', e₁, e₂, ⟨⟨a, e₁', b⟩, _, h₁⟩, ⟨⟨b'', e₂', c⟩, _, h₂⟩, rfl⟩

        have : g a = a' ∧ e₁' = e₁ ∧ g b = b' := by cases h₁; trivial
        obtain ⟨_, _, _⟩ := this
        have : g b'' = b' ∧ e₂' = e₂ ∧ g c = c' := by cases h₂; trivial
        obtain ⟨h₃, _, _⟩ := this
        subst a' e₁' b' e₂' c'

        have : b'' = b := g_inj h₃
        subst b''

        exists ⟨a, e₁ * e₂, c⟩
        and_intros
        · exists b, e₁, e₂
        · rfl

theorem NetworkPlusCal.Block.sem_eq_map₃.{u}
  {b b' : Bool} {B : GuardedPlusCal.Block.{u} (NetworkPlusCal.Statement Typ (Expression Typ) b) b'} :
  ⟦B⟧* = Prod.map₃ NetworkPlusCal.LocalState.toLocalState' id NetworkPlusCal.LocalState.toLocalState' '' (GuardedPlusCal.instReduceBlock (reduceα := λ ⦃_⦄ ↦ NetworkPlusCal.instReduceStatement)).reducing B := by
    change GuardedPlusCal.Block.reducing _ _ = Prod.map₃ _ _ _ '' GuardedPlusCal.Block.reducing _ _
    rw [GuardedPlusCal.Block.reducing_map _ _ NetworkPlusCal.LocalState.toLocalState'_inj]

    have : ∀ {b b' : Bool} (S : NetworkPlusCal.Statement.{u} _ _ b b'), NetworkPlusCal.instReduceStatement'.reducing S = Prod.map₃ NetworkPlusCal.LocalState.toLocalState' id NetworkPlusCal.LocalState.toLocalState' '' NetworkPlusCal.instReduceStatement.reducing S := by
      intros b b' S
      ext ⟨⟨M, T, F, l⟩, e, ⟨M', T', F', l'⟩⟩
      constructor
      · cases b' with
        | false =>
          rintro ⟨⟨M'', T'', F''⟩, rfl, sem, _|_, rfl⟩
          exists _, sem
        | true =>
          rintro ⟨⟨M'', T'', F'', l''⟩, rfl, sem, _, _|_, rfl, rfl⟩
          exists _, sem
      · cases b' with
        | false =>
          rintro ⟨⟨⟨_, _, _⟩, _, ⟨_, _, _⟩⟩, sem, _|_⟩
          exists _, rfl, sem
        | true =>
          rintro ⟨⟨⟨_, _, _⟩, _, _|⟨_, _, _, l⟩⟩, sem, _|_⟩
          exists _, rfl, sem, l
    conv_rhs => enter [1, b, S]; rw [← this S]

theorem GuardedPlusCal.Block.sem_eq_map₃.{u}
  {b b' : Bool} {B : GuardedPlusCal.Block.{u} (GuardedPlusCal.Statement Typ (Expression Typ) b) b'} :
  ⟦B⟧* = Prod.map₃ GuardedPlusCal.LocalState.toLocalState' id GuardedPlusCal.LocalState.toLocalState' '' (GuardedPlusCal.instReduceBlock (reduceα := λ ⦃_⦄ ↦ GuardedPlusCal.instReduceStatement)).reducing B := by
    change GuardedPlusCal.Block.reducing _ _ = Prod.map₃ _ _ _ '' GuardedPlusCal.Block.reducing _ _
    rw [GuardedPlusCal.Block.reducing_map _ _ GuardedPlusCal.LocalState.toLocalState'_inj]

    have : ∀ {b b' : Bool} (S : GuardedPlusCal.Statement.{u} _ _ b b'), GuardedPlusCal.instReduceStatement'.reducing S = Prod.map₃ GuardedPlusCal.LocalState.toLocalState' id GuardedPlusCal.LocalState.toLocalState' '' GuardedPlusCal.instReduceStatement.reducing S := by
      intros b b' S
      ext ⟨⟨M, T, F, l⟩, e, ⟨M', T', F', l'⟩⟩
      constructor
      · cases b' with
        | false =>
          rintro ⟨⟨M'', T'', F''⟩, rfl, sem, _|_, rfl⟩
          exists _, sem
        | true =>
          rintro ⟨⟨M'', T'', F'', l''⟩, rfl, sem, _, _|_, rfl⟩
          exists _, sem
      · cases b' with
        | false =>
          rintro ⟨⟨⟨_, _, _⟩, _, ⟨_, _, _⟩⟩, sem, _|_⟩
          exists _, rfl, sem
        | true =>
          rintro ⟨⟨⟨_, _, _⟩, _, _|⟨_, _, _, l⟩⟩, sem, _|_⟩
          exists _, rfl, sem, l
    conv_rhs => enter [1, b, S]; rw [← this S]

theorem GuardedPlusCal.Block.aborting_map {α β δ : Bool → Type _} {γ} [Monoid γ] {b} {B : GuardedPlusCal.Block α b}
  (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (g : ⦃b : Bool⦄ → α b → Set (β false × γ)) (h : ⦃b : Bool⦄ → β b → δ b) (h_inj : ∀ ⦃b⦄, Function.Injective (@h b)) :
  Prod.map (@h _) id '' GuardedPlusCal.Block.aborting g f B = GuardedPlusCal.Block.aborting (λ ⦃_⦄ x ↦ Prod.map (@h _) id '' g x) (λ ⦃_⦄ x ↦ Prod.map₃ (@h _) id (@h _) '' f x) B := by
    induction B using GuardedPlusCal.Block.reducing.induct with
    | case1 B _ =>
      let ⟨[], _⟩ := B
      repeat rw [GuardedPlusCal.Block.aborting]
    | case2 B S Ss h' IH =>
      let ⟨_ :: _, _⟩ := B
      obtain _|_ := h'
      repeat rw [GuardedPlusCal.Block.aborting]
      rw [Set.image_union]
      dsimp at IH ⊢
      congr

      ext ⟨x, e⟩
      constructor
      · rintro ⟨⟨a, e⟩, ⟨b, e₁, e₂, _, sem, rfl⟩, _|_⟩
        exists h b, e₁, e₂
        and_intros
        · exists ⟨a, e₁, b⟩
        · rw [← IH]
          exists ⟨b, e₂⟩
        · rfl
      · rw [← IH]
        rintro ⟨y, e₁, e₂, ⟨⟨a, e₁, b⟩, _, _|_⟩, ⟨⟨b', e₂'⟩, _, eq⟩, rfl⟩
        exists ⟨a, e₁ * e₂⟩
        and_intros
        · have : b' = b := by
            rw [Prod.map, Prod.mk.injEq] at eq
            exact h_inj eq.left

          have : e₂' = e₂ := by
            rw [Prod.map, Prod.mk.injEq] at eq
            exact eq.right

          subst b' e₂'
          exists b, e₁, e₂
        · rfl

theorem GuardedPlusCal.Block.diverging_map {α β δ : Bool → Type _} {γ} [Monoid γ] {b} {B : GuardedPlusCal.Block α b}
  (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (g : ⦃b : Bool⦄ → α b → Set (β false × γ)) (h : ⦃b : Bool⦄ → β b → δ b) (h_inj : ∀ ⦃b⦄, Function.Injective (@h b)) :
  Prod.map (@h _) id '' GuardedPlusCal.Block.diverging g f B = GuardedPlusCal.Block.diverging (λ ⦃_⦄ x ↦ Prod.map (@h _) id '' g x) (λ ⦃_⦄ x ↦ Prod.map₃ (@h _) id (@h _) '' f x) B := by
    induction B using GuardedPlusCal.Block.reducing.induct with
    | case1 B _ =>
      let ⟨[], _⟩ := B
      repeat rw [GuardedPlusCal.Block.diverging]
    | case2 B S Ss h' IH =>
      let ⟨_ :: _, _⟩ := B
      obtain _|_ := h'
      repeat rw [GuardedPlusCal.Block.diverging]
      rw [Set.image_union]
      dsimp at IH ⊢
      congr

      ext ⟨x, e⟩
      constructor
      · rintro ⟨⟨a, e⟩, ⟨b, e₁, e₂, _, sem, rfl⟩, _|_⟩
        exists h b, e₁, e₂
        and_intros
        · exists ⟨a, e₁, b⟩
        · rw [← IH]
          exists ⟨b, e₂⟩
        · rfl
      · rw [← IH]
        rintro ⟨y, e₁, e₂, ⟨⟨a, e₁, b⟩, _, _|_⟩, ⟨⟨b', e₂'⟩, _, eq⟩, rfl⟩
        exists ⟨a, e₁ * e₂⟩
        and_intros
        · have : b' = b := by
            rw [Prod.map, Prod.mk.injEq] at eq
            exact h_inj eq.left

          have : e₂' = e₂ := by
            rw [Prod.map, Prod.mk.injEq] at eq
            exact eq.right

          subst b' e₂'
          exists b, e₁, e₂
        · rfl

theorem GuardedPlusCal.Block.abort_eq_map.{u}
  {b b' : Bool} {B : GuardedPlusCal.Block.{u} (GuardedPlusCal.Statement Typ (Expression Typ) b) b'} :
  ⟦B⟧⊥ = Prod.map GuardedPlusCal.LocalState.toLocalState' id '' (GuardedPlusCal.instAbortBlock (reduceα := λ ⦃_⦄ ↦ GuardedPlusCal.instReduceStatement) (abortα := λ ⦃_⦄ ↦ GuardedPlusCal.instAbortStatement)).abort B := by
    change GuardedPlusCal.Block.aborting _ _ _ = Prod.map _ _ '' GuardedPlusCal.Block.aborting _ _ _
    rw [GuardedPlusCal.Block.aborting_map _ _ _ GuardedPlusCal.LocalState.toLocalState'_inj]

    have abort : ∀ {b b' : Bool} (S : GuardedPlusCal.Statement.{u} _ _ b b'), GuardedPlusCal.instAbortStatement'.abort S = Prod.map GuardedPlusCal.LocalState.toLocalState' id '' GuardedPlusCal.instAbortStatement.abort S := by
      intros b b' S
      ext ⟨⟨M, T, F, l⟩, e⟩
      constructor
      · cases b' with
        | false =>
          rintro ⟨rfl, sem⟩
          exists _, sem
        | true =>
          rintro ⟨rfl, sem⟩
          exists _, sem
      · cases b' with
        | false =>
          rintro ⟨⟨⟨_, _⟩, _⟩, _, _|_⟩
          trivial
        | true =>
          rintro ⟨⟨⟨_, _⟩, _⟩, _, _|_⟩
          trivial
    have red : ∀ {b b' : Bool} (S : GuardedPlusCal.Statement.{u} _ _ b b'), GuardedPlusCal.instReduceStatement'.reducing S = Prod.map₃ GuardedPlusCal.LocalState.toLocalState' id GuardedPlusCal.LocalState.toLocalState' '' GuardedPlusCal.instReduceStatement.reducing S := by
      intros b b' S
      ext ⟨⟨M, T, F, l⟩, e, ⟨M', T', F', l'⟩⟩
      constructor
      · cases b' with
        | false =>
          rintro ⟨⟨M'', T'', F''⟩, rfl, sem, _|_, rfl⟩
          exists _, sem
        | true =>
          rintro ⟨⟨M'', T'', F'', l''⟩, rfl, sem, _, _|_, rfl⟩
          exists _, sem
      · cases b' with
        | false =>
          rintro ⟨⟨⟨_, _, _⟩, _, ⟨_, _, _⟩⟩, sem, _|_⟩
          exists _, rfl, sem
        | true =>
          rintro ⟨⟨⟨_, _, _⟩, _, _|⟨_, _, _, l⟩⟩, sem, _|_⟩
          exists _, rfl, sem, l

    conv_rhs => enter [1, b, S]; rw [← abort S]
    conv_rhs => enter [2, b, S]; rw [← red S]

theorem GuardedPlusCal.Block.div_eq_map.{u}
  {b b' : Bool} {B : GuardedPlusCal.Block.{u} (GuardedPlusCal.Statement Typ (Expression Typ) b) b'} :
  ⟦B⟧∞ = Prod.map GuardedPlusCal.LocalState.toLocalState' id '' (GuardedPlusCal.instDivergeBlock (reduceα := λ ⦃_⦄ ↦ GuardedPlusCal.instReduceStatement) (divα := λ ⦃_⦄ ↦ GuardedPlusCal.instDivergeStatement)).div B := by
    change GuardedPlusCal.Block.diverging _ _ _ = Prod.map _ _ '' GuardedPlusCal.Block.diverging _ _ _
    rw [GuardedPlusCal.Block.diverging_map _ _ _ GuardedPlusCal.LocalState.toLocalState'_inj]

    have div : ∀ {b b' : Bool} (S : GuardedPlusCal.Statement.{u} _ _ b b'), GuardedPlusCal.instDivergeStatement'.div S = Prod.map GuardedPlusCal.LocalState.toLocalState' id '' GuardedPlusCal.instDivergeStatement.div S := by
      intros b b' S
      ext ⟨⟨M, T, F, l⟩, e⟩
      constructor
      · cases b' with
        | false =>
          rintro ⟨rfl, sem⟩
          exists _, sem
        | true =>
          rintro ⟨rfl, sem⟩
          exists _, sem
      · cases b' with
        | false =>
          rintro ⟨⟨⟨_, _⟩, _⟩, _, _|_⟩
          trivial
        | true =>
          rintro ⟨⟨⟨_, _⟩, _⟩, _, _|_⟩
          trivial
    have red : ∀ {b b' : Bool} (S : GuardedPlusCal.Statement.{u} _ _ b b'), GuardedPlusCal.instReduceStatement'.reducing S = Prod.map₃ GuardedPlusCal.LocalState.toLocalState' id GuardedPlusCal.LocalState.toLocalState' '' GuardedPlusCal.instReduceStatement.reducing S := by
      intros b b' S
      ext ⟨⟨M, T, F, l⟩, e, ⟨M', T', F', l'⟩⟩
      constructor
      · cases b' with
        | false =>
          rintro ⟨⟨M'', T'', F''⟩, rfl, sem, _|_, rfl⟩
          exists _, sem
        | true =>
          rintro ⟨⟨M'', T'', F'', l''⟩, rfl, sem, _, _|_, rfl⟩
          exists _, sem
      · cases b' with
        | false =>
          rintro ⟨⟨⟨_, _, _⟩, _, ⟨_, _, _⟩⟩, sem, _|_⟩
          exists _, rfl, sem
        | true =>
          rintro ⟨⟨⟨_, _, _⟩, _, _|⟨_, _, _, l⟩⟩, sem, _|_⟩
          exists _, rfl, sem, l

    conv_rhs => enter [1, b, S]; rw [← div S]
    conv_rhs => enter [2, b, S]; rw [← red S]

theorem NetworkPlusCal.Block.abort_eq_map.{u}
  {b b' : Bool} {B : GuardedPlusCal.Block.{u} (NetworkPlusCal.Statement Typ (Expression Typ) b) b'} :
  ⟦B⟧⊥ = Prod.map NetworkPlusCal.LocalState.toLocalState' id '' (GuardedPlusCal.instAbortBlock (reduceα := λ ⦃_⦄ ↦ NetworkPlusCal.instReduceStatement) (abortα := λ ⦃_⦄ ↦ NetworkPlusCal.instAbortStatement)).abort B := by
    change GuardedPlusCal.Block.aborting _ _ _ = Prod.map _ _ '' GuardedPlusCal.Block.aborting _ _ _
    rw [GuardedPlusCal.Block.aborting_map _ _ _ NetworkPlusCal.LocalState.toLocalState'_inj]

    have abort : ∀ {b b' : Bool} (S : NetworkPlusCal.Statement.{u} _ _ b b'), NetworkPlusCal.instAbortStatement'.abort S = Prod.map NetworkPlusCal.LocalState.toLocalState' id '' NetworkPlusCal.instAbortStatement.abort S := by
      intros b b' S
      ext ⟨⟨M, T, F, l⟩, e⟩
      constructor
      · cases b' with
        | false =>
          rintro ⟨rfl, sem⟩
          exists _, sem
        | true =>
          rintro ⟨rfl, sem⟩
          exists _, sem
      · cases b' with
        | false =>
          rintro ⟨⟨⟨_, _⟩, _⟩, _, _|_⟩
          trivial
        | true =>
          rintro ⟨⟨⟨_, _⟩, _⟩, _, _|_⟩
          trivial
    have red : ∀ {b b' : Bool} (S : NetworkPlusCal.Statement.{u} _ _ b b'), NetworkPlusCal.instReduceStatement'.reducing S = Prod.map₃ NetworkPlusCal.LocalState.toLocalState' id NetworkPlusCal.LocalState.toLocalState' '' NetworkPlusCal.instReduceStatement.reducing S := by
      intros b b' S
      ext ⟨⟨M, T, F, l⟩, e, ⟨M', T', F', l'⟩⟩
      constructor
      · cases b' with
        | false =>
          rintro ⟨⟨M'', T'', F''⟩, rfl, sem, _|_, rfl⟩
          exists _, sem
        | true =>
          rintro ⟨⟨M'', T'', F'', l''⟩, rfl, sem, _, _|_, rfl⟩
          exists _, sem
      · cases b' with
        | false =>
          rintro ⟨⟨⟨_, _, _⟩, _, ⟨_, _, _⟩⟩, sem, _|_⟩
          exists _, rfl, sem
        | true =>
          rintro ⟨⟨⟨_, _, _⟩, _, _|⟨_, _, _, l⟩⟩, sem, _|_⟩
          exists _, rfl, sem, l

    conv_rhs => enter [1, b, S]; rw [← abort S]
    conv_rhs => enter [2, b, S]; rw [← red S]

theorem NetworkPlusCal.Block.div_eq_map.{u}
  {b b' : Bool} {B : GuardedPlusCal.Block.{u} (NetworkPlusCal.Statement Typ (Expression Typ) b) b'} :
  ⟦B⟧∞ = Prod.map NetworkPlusCal.LocalState.toLocalState' id '' (GuardedPlusCal.instDivergeBlock (reduceα := λ ⦃_⦄ ↦ NetworkPlusCal.instReduceStatement) (divα := λ ⦃_⦄ ↦ NetworkPlusCal.instDivergeStatement)).div B := by
    change GuardedPlusCal.Block.diverging _ _ _ = Prod.map _ _ '' GuardedPlusCal.Block.diverging _ _ _
    rw [GuardedPlusCal.Block.diverging_map _ _ _ NetworkPlusCal.LocalState.toLocalState'_inj]

    have abort : ∀ {b b' : Bool} (S : NetworkPlusCal.Statement.{u} _ _ b b'), NetworkPlusCal.instDivergeStatement'.div S = Prod.map NetworkPlusCal.LocalState.toLocalState' id '' NetworkPlusCal.instDivergeStatement.div S := by
      intros b b' S
      ext ⟨⟨M, T, F, l⟩, e⟩
      constructor
      · cases b' with
        | false =>
          rintro ⟨rfl, sem⟩
          exists _, sem
        | true =>
          rintro ⟨rfl, sem⟩
          exists _, sem
      · cases b' with
        | false =>
          rintro ⟨⟨⟨_, _⟩, _⟩, _, _|_⟩
          trivial
        | true =>
          rintro ⟨⟨⟨_, _⟩, _⟩, _, _|_⟩
          trivial
    have red : ∀ {b b' : Bool} (S : NetworkPlusCal.Statement.{u} _ _ b b'), NetworkPlusCal.instReduceStatement'.reducing S = Prod.map₃ NetworkPlusCal.LocalState.toLocalState' id NetworkPlusCal.LocalState.toLocalState' '' NetworkPlusCal.instReduceStatement.reducing S := by
      intros b b' S
      ext ⟨⟨M, T, F, l⟩, e, ⟨M', T', F', l'⟩⟩
      constructor
      · cases b' with
        | false =>
          rintro ⟨⟨M'', T'', F''⟩, rfl, sem, _|_, rfl⟩
          exists _, sem
        | true =>
          rintro ⟨⟨M'', T'', F'', l''⟩, rfl, sem, _, _|_, rfl⟩
          exists _, sem
      · cases b' with
        | false =>
          rintro ⟨⟨⟨_, _, _⟩, _, ⟨_, _, _⟩⟩, sem, _|_⟩
          exists _, rfl, sem
        | true =>
          rintro ⟨⟨⟨_, _, _⟩, _, _|⟨_, _, _, l⟩⟩, sem, _|_⟩
          exists _, rfl, sem, l

    conv_rhs => enter [1, b, S]; rw [← abort S]
    conv_rhs => enter [2, b, S]; rw [← red S]

theorem NetworkPlusCal.LocalState.sem_glue₁.{u}
  {Mₜ₁ Mₜ₂ Tₜ₁ Tₜ₂ : TypedSetTheory.Memory.{u}} {Fₜ₁ Fₜ₂ : NetworkPlusCal.FIFOs.{u}} {l : String} {ε₂ : List GuardedPlusCal.Behavior.{u}}
  {B : GuardedPlusCal.Block (NetworkPlusCal.Statement Typ (Expression Typ) false) true} :
  ⟨NetworkPlusCal.LocalState.running Mₜ₁ Tₜ₁ Fₜ₁, ε₂, NetworkPlusCal.LocalState.done Mₜ₂ Tₜ₂ Fₜ₂ l⟩ ∈ (GuardedPlusCal.instReduceBlock (reduceα := λ ⦃_⦄ ↦ NetworkPlusCal.instReduceStatement)).reducing B ↔
    ((Mₜ₁, Tₜ₁, Fₜ₁, none), ε₂, (Mₜ₂, Tₜ₂, Fₜ₂, some l)) ∈ (GuardedPlusCal.instReduceBlock' (reduceα := λ ⦃_⦄ ↦ NetworkPlusCal.instReduceStatement')).reducing B := by
      rw [NetworkPlusCal.Block.sem_eq_map₃, Set.mem_image]
      constructor
      · intro sem; exists _, sem
      · rintro ⟨⟨⟨_, _⟩, _, _|⟨_, _, _⟩⟩, sem, _|_⟩; exact sem

theorem NetworkPlusCal.LocalState.sem_glue₂.{u}
  {Mₜ₁ Mₜ₂ Tₜ₁ Tₜ₂ : TypedSetTheory.Memory.{u}} {Fₜ₁ Fₜ₂ : NetworkPlusCal.FIFOs.{u}} {ε₂ : List GuardedPlusCal.Behavior.{u}}
  {B : GuardedPlusCal.Block (NetworkPlusCal.Statement Typ (Expression Typ) true) false} :
  ⟨NetworkPlusCal.LocalState.running Mₜ₁ Tₜ₁ Fₜ₁, ε₂, NetworkPlusCal.LocalState.running Mₜ₂ Tₜ₂ Fₜ₂⟩ ∈ (GuardedPlusCal.instReduceBlock (reduceα := λ ⦃_⦄ ↦ NetworkPlusCal.instReduceStatement)).reducing B ↔
    ((Mₜ₁, Tₜ₁, Fₜ₁, none), ε₂, (Mₜ₂, Tₜ₂, Fₜ₂, none)) ∈ (GuardedPlusCal.instReduceBlock' (reduceα := λ ⦃_⦄ ↦ NetworkPlusCal.instReduceStatement')).reducing B := by
      rw [NetworkPlusCal.Block.sem_eq_map₃, Set.mem_image]
      constructor
      · intro sem; exists _, sem
      · rintro ⟨⟨⟨_, _⟩, _, ⟨_, _⟩⟩, sem, _|_⟩; exact sem

theorem GuardedPlusCal.LocalState.sem_glue₁.{u}
  {b : Bool} {Mₜ₁ Mₜ₂ Tₜ₁ Tₜ₂ : TypedSetTheory.Memory.{u}} {Fₜ₁ Fₜ₂ : NetworkPlusCal.FIFOs.{u}} {l : String} {ε₂ : List GuardedPlusCal.Behavior.{u}}
  {B : GuardedPlusCal.Block (GuardedPlusCal.Statement Typ (Expression Typ) b) true} :
  ⟨GuardedPlusCal.LocalState.running Mₜ₁ Tₜ₁ Fₜ₁, ε₂, GuardedPlusCal.LocalState.done Mₜ₂ Tₜ₂ Fₜ₂ l⟩ ∈ (GuardedPlusCal.instReduceBlock (reduceα := λ ⦃_⦄ ↦ GuardedPlusCal.instReduceStatement)).reducing B ↔
    ((Mₜ₁, Tₜ₁, Fₜ₁, none), ε₂, (Mₜ₂, Tₜ₂, Fₜ₂, some l)) ∈ (GuardedPlusCal.instReduceBlock' (reduceα := λ ⦃_⦄ ↦ GuardedPlusCal.instReduceStatement')).reducing B := by
      rw [GuardedPlusCal.Block.sem_eq_map₃, Set.mem_image]
      constructor
      · intro sem; exists _, sem
      · rintro ⟨⟨⟨_, _⟩, _, _|⟨_, _, _⟩⟩, sem, _|_⟩; exact sem

theorem GuardedPlusCal.LocalState.sem_glue₂.{u}
  {b : Bool} {Mₜ₁ Mₜ₂ Tₜ₁ Tₜ₂ : TypedSetTheory.Memory.{u}} {Fₜ₁ Fₜ₂ : NetworkPlusCal.FIFOs.{u}} {ε₂ : List GuardedPlusCal.Behavior.{u}}
  {B : GuardedPlusCal.Block (GuardedPlusCal.Statement Typ (Expression Typ) b) false} :
  ⟨GuardedPlusCal.LocalState.running Mₜ₁ Tₜ₁ Fₜ₁, ε₂, GuardedPlusCal.LocalState.running Mₜ₂ Tₜ₂ Fₜ₂⟩ ∈ (GuardedPlusCal.instReduceBlock (reduceα := λ ⦃_⦄ ↦ GuardedPlusCal.instReduceStatement)).reducing B ↔
    ((Mₜ₁, Tₜ₁, Fₜ₁, none), ε₂, (Mₜ₂, Tₜ₂, Fₜ₂, none)) ∈ (GuardedPlusCal.instReduceBlock' (reduceα := λ ⦃_⦄ ↦ GuardedPlusCal.instReduceStatement')).reducing B := by
      rw [GuardedPlusCal.Block.sem_eq_map₃, Set.mem_image]
      constructor
      · intro sem; exists _, sem
      · rintro ⟨⟨⟨_, _⟩, _, _|⟨_, _, _⟩⟩, sem, _|_⟩; exact sem

theorem GuardedPlusCal.LocalState.abort_glue.{u}
  {Mₛ₁ Tₛ₁ : TypedSetTheory.Memory.{u}} {Fₛ₁ : GuardedPlusCal.FIFOs.{u}} {ε : List GuardedPlusCal.Behavior.{u}}
  {b b'} {B : GuardedPlusCal.Block (GuardedPlusCal.Statement Typ (Expression Typ) b) b'} :
  (GuardedPlusCal.LocalState.running Mₛ₁ Tₛ₁ Fₛ₁, ε) ∈ (GuardedPlusCal.instAbortBlock (reduceα := λ ⦃_⦄ ↦ GuardedPlusCal.instReduceStatement) (abortα := λ ⦃_⦄ ↦ GuardedPlusCal.instAbortStatement)).abort B ↔
    ((Mₛ₁, Tₛ₁, Fₛ₁, none), ε) ∈ (GuardedPlusCal.instAbortBlock' (reduceα := λ ⦃_⦄ ↦ GuardedPlusCal.instReduceStatement') (abortα := λ ⦃_⦄ ↦ GuardedPlusCal.instAbortStatement')).abort B := by
      rw [GuardedPlusCal.Block.abort_eq_map, Set.mem_image]
      constructor
      · intro sem; exists _, sem
      · rintro ⟨⟨⟨_, _⟩, _⟩, sem, _|_⟩; exact sem

theorem NetworkPlusCal.LocalState.abort_glue.{u}
  {Mₛ₁ Tₛ₁ : TypedSetTheory.Memory.{u}} {Fₛ₁ : NetworkPlusCal.FIFOs.{u}} {ε : List NetworkPlusCal.Behavior.{u}}
  {b b'} {B : GuardedPlusCal.Block (NetworkPlusCal.Statement Typ (Expression Typ) b) b'} :
  (NetworkPlusCal.LocalState.running Mₛ₁ Tₛ₁ Fₛ₁, ε) ∈ (GuardedPlusCal.instAbortBlock (reduceα := λ ⦃_⦄ ↦ NetworkPlusCal.instReduceStatement) (abortα := λ ⦃_⦄ ↦ NetworkPlusCal.instAbortStatement)).abort B ↔
    ((Mₛ₁, Tₛ₁, Fₛ₁, none), ε) ∈ (GuardedPlusCal.instAbortBlock' (reduceα := λ ⦃_⦄ ↦ NetworkPlusCal.instReduceStatement') (abortα := λ ⦃_⦄ ↦ NetworkPlusCal.instAbortStatement')).abort B := by
      rw [NetworkPlusCal.Block.abort_eq_map, Set.mem_image]
      constructor
      · intro sem; exists _, sem
      · rintro ⟨⟨⟨_, _⟩, _⟩, sem, _|_⟩; exact sem

theorem NetworkPlusCal.LocalState.div_glue.{u}
  {Mₛ₁ Tₛ₁ : TypedSetTheory.Memory.{u}} {Fₛ₁ : NetworkPlusCal.FIFOs.{u}} {ε : List NetworkPlusCal.Behavior.{u}}
  {b b'} {B : GuardedPlusCal.Block (NetworkPlusCal.Statement Typ (Expression Typ) b) b'} :
  (NetworkPlusCal.LocalState.running Mₛ₁ Tₛ₁ Fₛ₁, ε) ∈ (GuardedPlusCal.instDivergeBlock (reduceα := λ ⦃_⦄ ↦ NetworkPlusCal.instReduceStatement) (divα := λ ⦃_⦄ ↦ NetworkPlusCal.instDivergeStatement)).div B ↔
    ((Mₛ₁, Tₛ₁, Fₛ₁, none), ε) ∈ (GuardedPlusCal.instDivergeBlock' (reduceα := λ ⦃_⦄ ↦ NetworkPlusCal.instReduceStatement') (divα := λ ⦃_⦄ ↦ NetworkPlusCal.instDivergeStatement')).div B := by
      rw [NetworkPlusCal.Block.div_eq_map, Set.mem_image]
      constructor
      · intro sem; exists _, sem
      · rintro ⟨⟨⟨_, _⟩, _⟩, sem, _|_⟩; exact sem

theorem GuardedPlusCal.AtomicBranch.sem_eq {Br : AtomicBranch Typ (Expression Typ)} :
    ⟦Br⟧* = (Br.precondition.elim {⟨x, ε, y⟩ | x = y ∧ ε = Trace.τ} (⟦·⟧*)) ∘ᵣ₂ ⟦Br.action⟧* := by
  simp_rw [GuardedPlusCal.Block.sem_eq_map₃]
  obtain ⟨_|pre, act⟩ := Br
  · erw [Relation.lcomp₂.left_id_eq]
    ext ⟨⟨M, T, F, l⟩, _, ⟨M', T', F', l'⟩⟩
    constructor
    · rintro ⟨_, ⟨⟨⟩, _, _, ⟨_|_, rfl⟩, red_act, rfl⟩, rfl, rfl⟩
      exists _, red_act
    · rintro ⟨⟨⟨⟩, _, _|⟨_, _, _, l⟩⟩, _, _|_⟩
      exists l
      and_intros <;> try rfl
      change _ ∈ {⟨x, e, y⟩ : LocalState false × List Behavior × LocalState false | x = y ∧ e = Trace.τ} ∘ᵣ₂ _
      erwa [Relation.lcomp₂.left_id_eq]
  · ext ⟨⟨M, T, F, l⟩, _, ⟨M', T', F', l'⟩⟩
    constructor
    · rintro ⟨_, ⟨⟨M'', T'', F''⟩, ε₁, ε₂, red_pre, red_act, rfl⟩, rfl, rfl⟩
      exists ⟨M'', T'', F'', .none⟩, ε₁, ε₂
      and_intros <;> try rfl
      · exists _, red_pre
      · exists _, red_act
    · rintro ⟨⟨⟩, ε₁, ε₂, ⟨⟨⟨⟩, _, ⟨⟩⟩, red_pre, _|_⟩, ⟨⟨⟨⟩, _, _|⟨_, _, _, l⟩⟩, red_act, _|_⟩, rfl⟩
      exists l
      and_intros <;> try rfl
      exists _, _, _, red_pre, red_act

theorem GuardedPlusCal.AtomicBranch.abort_eq.{u} {Br : AtomicBranch.{u} Typ (Expression Typ)} :
    ⟦Br⟧⊥ = (Br.precondition.elim ∅ (⟦·⟧⊥)) ∪ (Br.precondition.elim {⟨x, ε, y⟩ | x = y ∧ ε = Trace.τ} (⟦·⟧*)) ∘ᵣ₁ ⟦Br.action⟧⊥ := by
  simp_rw [GuardedPlusCal.Block.abort_eq_map, GuardedPlusCal.Block.sem_eq_map₃]
  obtain ⟨_|pre, act⟩ := Br
  · erw [Set.empty_union, Relation.lcomp₁.left_id_eq]
    ext ⟨⟨M, T, F, l⟩, ε⟩
    constructor
    · rintro ⟨rfl, _⟩
      exists ⟨.running M T F, ε⟩
    · rintro ⟨⟨⟨M, T, F⟩, ε⟩, _, _|_⟩
      trivial
  · ext ⟨⟨M, T, F, l⟩, ε⟩
    constructor
    · rintro ⟨rfl, abort|⟨⟨M'', T'', F''⟩, ε₁, ε₂, red_pre, red_act, rfl⟩⟩
      · left
        exists ⟨.running M T F, ε⟩
      · right
        exists ⟨M'', T'', F'', .none⟩, ε₁, ε₂
        and_intros <;> try trivial
        · exists ⟨.running M T F, ε₁, .running M'' T'' F''⟩
        · exists ⟨.running M'' T'' F'', ε₂⟩
    · rintro (⟨⟨⟨_, _⟩, ε⟩, abort, _|_⟩|⟨⟨M', T', F', _⟩, ε₁, ε₂, ⟨⟨⟨_, _⟩, ε₁, ⟨_, _⟩⟩, red_pre, _|_⟩, ⟨⟨⟨_, _⟩, ε₂⟩, red_act, _|_⟩, rfl⟩)
      · constructor
        · rfl
        · left
          assumption
      · constructor
        · rfl
        · right
          exists .running M' T' F', ε₁, ε₂

theorem GuardedPlusCal.AtomicBranch.div_eq.{u} {Br : AtomicBranch.{u} Typ (Expression Typ)} :
    ⟦Br⟧∞ = (Br.precondition.elim ∅ (⟦·⟧∞)) ∪ (Br.precondition.elim {⟨x, ε, y⟩ | x = y ∧ ε = Trace.τ} (⟦·⟧*)) ∘ᵣ₁ ⟦Br.action⟧∞ := by
  simp_rw [GuardedPlusCal.Block.div_eq_map, GuardedPlusCal.Block.sem_eq_map₃]
  obtain ⟨_|pre, act⟩ := Br
  · erw [Set.empty_union, Relation.lcomp₁.left_id_eq]
    ext ⟨⟨M, T, F, l⟩, ε⟩
    constructor
    · rintro ⟨rfl, _⟩
      exists ⟨.running M T F, ε⟩
    · rintro ⟨⟨⟨M, T, F⟩, ε⟩, _, _|_⟩
      trivial
  · ext ⟨⟨M, T, F, l⟩, ε⟩
    constructor
    · rintro ⟨rfl, abort|⟨⟨M'', T'', F''⟩, ε₁, ε₂, red_pre, red_act, rfl⟩⟩
      · left
        exists ⟨.running M T F, ε⟩
      · right
        exists ⟨M'', T'', F'', .none⟩, ε₁, ε₂
        and_intros <;> try trivial
        · exists ⟨.running M T F, ε₁, .running M'' T'' F''⟩
        · exists ⟨.running M'' T'' F'', ε₂⟩
    · rintro (⟨⟨⟨_, _⟩, ε⟩, abort, _|_⟩|⟨⟨M', T', F', _⟩, ε₁, ε₂, ⟨⟨⟨_, _⟩, ε₁, ⟨_, _⟩⟩, red_pre, _|_⟩, ⟨⟨⟨_, _⟩, ε₂⟩, red_act, _|_⟩, rfl⟩)
      · constructor
        · rfl
        · left
          assumption
      · constructor
        · rfl
        · right
          exists .running M' T' F', ε₁, ε₂

theorem NetworkPlusCal.AtomicBranch.sem_eq {Br : AtomicBranch Typ (Expression Typ)} :
    ⟦Br⟧* = (Br.precondition.elim {⟨x, ε, y⟩ | x = y ∧ ε = Trace.τ} (⟦·⟧*)) ∘ᵣ₂ ⟦Br.action⟧* := by
  ext ⟨st, ε, st'⟩
  constructor
  · rintro ⟨_, ⟨⟨M'', T'', F''⟩, ε₁, ε₂, red_pre, red_act, rfl⟩, st_2_2_eq_none, st'_2_2_eq_some⟩
    dsimp at *
    exists ⟨M'', T'', F'', .none⟩, ε₁, ε₂
    and_intros <;> try trivial
    · cases pre_eq : Br.precondition with
      | none =>
        rw [pre_eq] at red_pre
        obtain ⟨_, _, _, _|_, _|_, rfl⟩ := red_pre
        constructor
        · rw [← st_2_2_eq_none]
        · rfl
      | some pre =>
        erwa (config := {occs := .pos [1]}) [pre_eq, NetworkPlusCal.LocalState.sem_glue₂, ← st_2_2_eq_none] at red_pre
    · rwa [NetworkPlusCal.LocalState.sem_glue₁, ← st'_2_2_eq_some] at red_act
  · rintro ⟨⟨M'', T'', F'', l''⟩, ε₁, ε₂, red_pre, red_act, rfl⟩
    rw [NetworkPlusCal.Block.sem_eq_map₃, Set.mem_image] at red_act
    obtain ⟨⟨⟨_, _⟩|_, ε₂, _|⟨_, _, _, l'⟩⟩, red_act, _|_⟩ := red_act
    exists l'
    and_intros <;> try rfl
    · exists .running M'' T'' F'', ε₁, ε₂
      and_intros <;> try trivial
      cases pre_eq : Br.precondition with
      | none =>
        rw [pre_eq] at red_pre
        obtain ⟨rfl, rfl⟩ := red_pre
        exists M'', T'', F''
      | some pre =>
        rw [pre_eq] at red_pre
        dsimp at red_pre
        rw [NetworkPlusCal.Block.sem_eq_map₃, Set.mem_image] at red_pre
        obtain ⟨⟨⟨_, _⟩|_, ε₂, ⟨_, _⟩|_⟩, red_pre, _|_⟩ := red_pre
        exact red_pre
    · cases pre_eq : Br.precondition with
      | none =>
        rw [pre_eq] at red_pre
        obtain ⟨_, _⟩ := red_pre
        subst st
        rfl
      | some pre =>
        rw [pre_eq] at red_pre
        dsimp at red_pre
        rw [NetworkPlusCal.Block.sem_eq_map₃, Set.mem_image] at red_pre
        obtain ⟨⟨⟨_, _⟩|_, _, ⟨_, _⟩|_⟩, _, _|_⟩ := red_pre
        rfl

theorem NetworkPlusCal.AtomicBranch.abort_eq.{u} {Br : AtomicBranch.{u} Typ (Expression Typ)} :
    ⟦Br⟧⊥ = (Br.precondition.elim ∅ (⟦·⟧⊥)) ∪ (Br.precondition.elim {⟨x, ε, y⟩ | x = y ∧ ε = Trace.τ} (⟦·⟧*)) ∘ᵣ₁ ⟦Br.action⟧⊥ := by
  simp_rw [NetworkPlusCal.Block.abort_eq_map, NetworkPlusCal.Block.sem_eq_map₃]
  obtain ⟨_|pre, act⟩ := Br
  · erw [Set.empty_union, Relation.lcomp₁.left_id_eq]
    ext ⟨⟨M, T, F, l⟩, ε⟩
    constructor
    · rintro ⟨rfl, _⟩
      exists ⟨.running M T F, ε⟩
    · rintro ⟨⟨⟨M, T, F⟩, ε⟩, _, _|_⟩
      trivial
  · ext ⟨⟨M, T, F, l⟩, ε⟩
    constructor
    · rintro ⟨rfl, abort|⟨⟨M'', T'', F''⟩, ε₁, ε₂, red_pre, red_act, rfl⟩⟩
      · left
        exists ⟨.running M T F, ε⟩
      · right
        exists ⟨M'', T'', F'', .none⟩, ε₁, ε₂
        and_intros <;> try trivial
        · exists ⟨.running M T F, ε₁, .running M'' T'' F''⟩
        · exists ⟨.running M'' T'' F'', ε₂⟩
    · rintro (⟨⟨⟨_, _⟩, ε⟩, abort, _|_⟩|⟨⟨M', T', F', _⟩, ε₁, ε₂, ⟨⟨⟨_, _⟩, ε₁, ⟨_, _⟩⟩, red_pre, _|_⟩, ⟨⟨⟨_, _⟩, ε₂⟩, red_act, _|_⟩, rfl⟩)
      · constructor
        · rfl
        · left
          assumption
      · constructor
        · rfl
        · right
          exists .running M' T' F', ε₁, ε₂

theorem NetworkPlusCal.AtomicBranch.div_eq.{u} {Br : AtomicBranch.{u} Typ (Expression Typ)} :
    ⟦Br⟧∞ = (Br.precondition.elim ∅ (⟦·⟧∞)) ∪ (Br.precondition.elim {⟨x, ε, y⟩ | x = y ∧ ε = Trace.τ} (⟦·⟧*)) ∘ᵣ₁ ⟦Br.action⟧∞ := by
  simp_rw [NetworkPlusCal.Block.div_eq_map, NetworkPlusCal.Block.sem_eq_map₃]
  obtain ⟨_|pre, act⟩ := Br
  · erw [Set.empty_union, Relation.lcomp₁.left_id_eq]
    ext ⟨⟨M, T, F, l⟩, ε⟩
    constructor
    · rintro ⟨rfl, _⟩
      exists ⟨.running M T F, ε⟩
    · rintro ⟨⟨⟨M, T, F⟩, ε⟩, _, _|_⟩
      trivial
  · ext ⟨⟨M, T, F, l⟩, ε⟩
    constructor
    · rintro ⟨rfl, abort|⟨⟨M'', T'', F''⟩, ε₁, ε₂, red_pre, red_act, rfl⟩⟩
      · left
        exists ⟨.running M T F, ε⟩
      · right
        exists ⟨M'', T'', F'', .none⟩, ε₁, ε₂
        and_intros <;> try trivial
        · exists ⟨.running M T F, ε₁, .running M'' T'' F''⟩
        · exists ⟨.running M'' T'' F'', ε₂⟩
    · rintro (⟨⟨⟨_, _⟩, ε⟩, abort, _|_⟩|⟨⟨M', T', F', _⟩, ε₁, ε₂, ⟨⟨⟨_, _⟩, ε₁, ⟨_, _⟩⟩, red_pre, _|_⟩, ⟨⟨⟨_, _⟩, ε₂⟩, red_act, _|_⟩, rfl⟩)
      · constructor
        · rfl
        · left
          assumption
      · constructor
        · rfl
        · right
          exists .running M' T' F', ε₁, ε₂

theorem NetworkPlusCal.LocalState.sem_glue₃.{u} {st : NetworkPlusCal.LocalState.{u} false} {st' : NetworkPlusCal.LocalState.{u} true} {ε} {Br : NetworkPlusCal.AtomicBranch.{u} Typ (Expression Typ)} :
    (st.toLocalState', ε, st'.toLocalState') ∈ ⟦Br⟧* ↔ (st, ε, st') ∈ NetworkPlusCal.instReduceAtomicBranch.reducing Br := by
  rcases st, st' with ⟨⟨M, T, F⟩, _|⟨M', T', F', l'⟩⟩
  constructor <;> rw [NetworkPlusCal.AtomicBranch.sem_eq]
  · rintro ⟨st'', ε₁, ε₂, red_pre, red_act, rfl⟩
    exists .running st''.1 st''.2.1 st''.2.2.1, ε₁, ε₂
    and_intros <;> try rfl
    · simp_rw [NetworkPlusCal.Block.sem_eq_map₃] at red_pre
      cases pre_eq : Br.precondition with
      | none =>
        rw [pre_eq] at red_pre
        obtain ⟨_|_, _|_⟩ := red_pre
        exists M, T, F
      | some pre =>
        erw [pre_eq, Set.mem_image] at red_pre
        obtain ⟨⟨⟨⟩, _, _|⟨⟩⟩, red_pre, _|_⟩ := red_pre
        assumption
    · rw [NetworkPlusCal.Block.sem_eq_map₃, Set.mem_image] at red_act
      obtain ⟨⟨⟨⟩, _, _|⟨⟩⟩, red_act, _|_⟩ := red_act
      assumption
  · rintro ⟨⟨M'', T'', F''⟩, ε₁, ε₂, red_pre, red_act, rfl⟩
    exists NetworkPlusCal.LocalState.toLocalState' (.running M'' T'' F''), ε₁, ε₂
    and_intros <;> try rfl
    · cases pre_eq : Br.precondition with
      | none =>
        rw [pre_eq] at red_pre
        obtain ⟨_, _, _, _|_, _|_, rfl⟩ := red_pre
        constructor <;> rfl
      | some pre =>
        rw [pre_eq] at red_pre
        dsimp at red_pre ⊢
        rw [NetworkPlusCal.Block.sem_eq_map₃, Set.mem_image]
        exists _, red_pre
    · rwa [NetworkPlusCal.LocalState.sem_glue₁] at red_act

theorem NetworkPlusCal.LocalState.abort_glue₂.{u} {st : NetworkPlusCal.LocalState.{u} false} {ε} {Br : NetworkPlusCal.AtomicBranch.{u} Typ (Expression Typ)} :
    (st.toLocalState', ε) ∈ ⟦Br⟧⊥ ↔ (st, ε) ∈ NetworkPlusCal.instAbortAtomicBranch.abort Br := by
  rcases st, Br with ⟨⟨M, T, F⟩, ⟨precond, action⟩⟩
  iff_intro h h
  · rw [AtomicBranch.abort_eq, toLocalState'] at h
    cases precond with
    | none =>
      erwa [Set.empty_union, Relation.lcomp₁.left_id_eq, ← abort_glue] at h
    | some precond =>
      obtain h|⟨⟨M', T', F', l⟩, ε₁, ε₂, h₁, h₂, rfl⟩ := h
      · left
        rwa [abort_glue]
      · right

        obtain rfl : l = none := by
          dsimp at h₁
          simp_rw [Block.sem_eq_map₃, Set.mem_image, Prod.exists, Prod.map₃] at h₁
          obtain ⟨_|_, _, _|_, _, _|_⟩ := h₁
          rfl

        exists .running M' T' F', ε₁, ε₂, ?_, ?_
        · rwa [sem_glue₂]
        · rwa [abort_glue]
        · rfl
  · rw [AtomicBranch.abort_eq, toLocalState']
    cases precond with
    | none =>
      erwa [Set.empty_union, Relation.lcomp₁.left_id_eq, ← abort_glue]
    | some precond =>
      obtain h|⟨⟨M', F', T'⟩, ε₁, ε₂, _, _, rfl⟩ := h
      · left
        rwa [abort_glue] at h
      · right
        exists ⟨M', F', T', none⟩, ε₁, ε₂, ?_, ?_
        · erwa [← sem_glue₂]
        · rwa [← abort_glue]
        · rfl

theorem NetworkPlusCal.AtomicBlock.div_eq.{u} {B : AtomicBlock.{u} Typ (Expression Typ)} :
    ⟦B⟧∞ = ⋃ Br ∈ B.branches, ⟦Br⟧∞ := by
  ext ⟨⟨M, T, F, l⟩, ε⟩
  iff_rintro h h
  · rw [Set.mem_iUnion₂]
    erw [exists₂_congr (λ _ _ ↦ And.comm)]
    -- why doesn't `exact h` work here?
    obtain ⟨Br, Br_in, _⟩ := h
    exists Br, Br_in
  · rw [Set.mem_iUnion₂] at h
    erw [exists₂_congr (λ _ _ ↦ And.comm)] at h
    -- why doesn't `exact h` work here?
    obtain ⟨Br, Br_in, _⟩ := h
    exists Br, Br_in

lemma NetworkPlusCal.LocalState'.sem_label_eq.{u} (B : Block.{u} (Statement Typ (Expression Typ) true) false)
  {σ σ' : NetworkPlusCal.LocalState'} {ε} (h : (σ, ε, σ') ∈ ⟦B⟧*) :
    σ.2.2.2 = none ∧ σ'.2.2.2 = none := by
  rcases σ, σ' with ⟨⟨M, T, F, l⟩, ⟨M', T', F', l'⟩⟩
  rw [Block.sem_eq_map₃, Set.mem_image] at h
  obtain ⟨⟨⟨M, T, F⟩, ε, ⟨M', T', F'⟩⟩, h, _|_⟩ := h
  constructor <;> rfl

theorem NetworkPlusCal.LocalState.div_glue₃.{u} {st : NetworkPlusCal.LocalState.{u} false} {ε} {Br : NetworkPlusCal.AtomicBranch.{u} Typ (Expression Typ)} :
    (st.toLocalState', ε) ∈ ⟦Br⟧∞ ↔ (st, ε) ∈ NetworkPlusCal.instDivergeAtomicBranch.div Br := by
  rcases st, Br with ⟨⟨M, T, F⟩, ⟨precond, action⟩⟩
  iff_intro h h
  · rw [AtomicBranch.div_eq] at h
    cases precond with
    | none =>
      erw [Set.empty_union, Relation.lcomp₁.left_id_eq] at h
      erw [NetworkPlusCal.LocalState.div_glue]
      assumption
    | some precond =>
      obtain sem_precond|⟨⟨M', T', F', l'⟩, ε₁, ε₂, _, _, rfl⟩ := h
      · left
        erwa [NetworkPlusCal.LocalState.div_glue]
      · right

        have : l' = none := by
          apply And.right
          apply NetworkPlusCal.LocalState'.sem_label_eq (σ' := ⟨M', T', F', l'⟩)
          assumption
        subst l'

        exists .running M' T' F', ε₁, ε₂, ?_, ?_ <;> try trivial
        · erwa [NetworkPlusCal.LocalState.sem_glue₂]
        · erwa [NetworkPlusCal.LocalState.div_glue]
  · rw [AtomicBranch.div_eq]
    cases precond with
    | none =>
      erw [Set.empty_union, Relation.lcomp₁.left_id_eq]
      erw [NetworkPlusCal.LocalState.div_glue] at h
      assumption
    | some precond =>
      obtain sem_precond|⟨⟨M', T', F'⟩, ε₁, ε₂, _, _, rfl⟩ := h
      · left
        erwa [← NetworkPlusCal.LocalState.div_glue]
      · right

        exists ⟨M', T', F', none⟩, ε₁, ε₂, ?_, ?_ <;> try trivial
        · erwa [← NetworkPlusCal.LocalState.sem_glue₂]
        · erwa [← NetworkPlusCal.LocalState.div_glue]

theorem NetworkPlusCal.LocalState.div_glue₂.{u} {st : NetworkPlusCal.LocalState.{u} false} {ε} {Br : NetworkPlusCal.AtomicBlock.{u} Typ (Expression Typ)} :
    (st.toLocalState', ε) ∈ ⟦Br⟧∞ ↔ ∃ B ∈ Br.branches, (st, ε) ∈ NetworkPlusCal.instDivergeAtomicBranch.div B := by
  rcases st with ⟨M, T, F⟩
  iff_intro h h
  · rw [AtomicBlock.div_eq, toLocalState', Set.mem_iUnion₂] at h
    obtain ⟨Br, Br_in, h⟩ := h
    exists Br, Br_in
    rwa [← NetworkPlusCal.LocalState.div_glue₃]
  · rw [AtomicBlock.div_eq, toLocalState', Set.mem_iUnion₂]
    obtain ⟨Br, Br_in, h⟩ := h
    use Br, Br_in
    rwa [← NetworkPlusCal.LocalState.div_glue₃] at h

-- subscript `ₛ` denotes "source", while subscript `ₜ` denotes "target"
namespace GuardedToNetwork
  variable (inbox : String)

  /-- Relates a state from GuardedPlusCal to a state from NetworkPlusCal, given an optional mailbox. -/
  def relatesTo.{u} (mbox : Option (Expression.{u} Typ × String)) : Rel GuardedPlusCal.LocalState'.{u} NetworkPlusCal.LocalState'.{u} :=
    λ ⟨M₁, T₁, F₁, l₁⟩ ⟨M₂, T₂, F₂, l₂⟩ ↦
      -- Blocks end in the same labels (or not)
      l₁ = l₂ ∧
      match mbox with
      | .none =>
        -- Memories exactly match
        M₁ = M₂ ∧ T₁ = T₂ ∧
        -- FIFOs match
        F₁ = F₂
      | .some (.funcall (.var c _) [e@(.var "self" _)], inbox) =>
        -- Memories exactly match on everything but the inbox
        (∀ v ≠ inbox, M₁.lookup v = M₂.lookup v) ∧ T₁ = T₂ ∧
        (∃ vs,
          -- Inbox is a sequence in the shared memory
          M₂.lookup inbox = Value.seq vs ∧
          T₂.lookup inbox = none ∧
          ∃ v : Value.{u},
            -- Indices of the mailbox may not depend on the local state, hence the empty memory
            (T₁ ∪ M₁) ⊢ e ⇒ v ∧
            -- FIFOs match (except for ` [c, es]`)
            (∀ c' ≠ c, ∀ es', F₁.lookup ⟨c', es'⟩ = F₂.lookup ⟨c', es'⟩) ∧
            (∀ es' ≠ [v], F₁.lookup ⟨c, es'⟩ = F₂.lookup ⟨c, es'⟩) ∧
            -- F₁[c, _] contains `inbox ++ F₂[c, _]`
            F₁.lookup ⟨c, [v]⟩ = do
              let vs' ← F₂.lookup ⟨c, [v]⟩
              return vs ++ vs')
      | .some (.var c _, inbox) =>
        -- Memories exactly match on everything but the inbox
        (∀ v ≠ inbox, M₁.lookup v = M₂.lookup v) ∧ T₁ = T₂ ∧
        (∃ vs,
          -- Inbox is a sequence in the shared memory
          M₂.lookup inbox = Value.seq vs ∧
          T₂.lookup inbox = none ∧
          -- FIFOs match (except for ` [c, []]`)
          (∀ c' ≠ c, ∀ es', F₁.lookup ⟨c', es'⟩ = F₂.lookup ⟨c', es'⟩) ∧
          (∀ es' ≠ [], F₁.lookup ⟨c, es'⟩ = F₂.lookup ⟨c, es'⟩) ∧
          -- F₁[c, []] contains `inbox ++ F₂[c, []]`
          F₁.lookup ⟨c, []⟩ = do
            let vs' ← F₂.lookup ⟨c, []⟩
            return vs ++ vs')
      | .some _ => False
  @[inherit_doc] local notation:60 σₛ:60 " ∼[" mbox:0 "] " σₜ:60 => relatesTo mbox σₛ σₜ

  variable {inbox}

  private theorem relatesTo_mailbox_shape {σₛ σₜ} {v : Expression Typ} {x : String} (h : σₛ ∼[.some (v, x)] σₜ) :
    (∃ c τ, v = .var c τ) ∨ (∃ c τ₁ τ₂, v = .funcall (.var c τ₁) [.var "self" τ₂]) := by
      --unfold relatesTo at h
      dsimp [relatesTo] at h
      obtain ⟨-, h⟩ := h
      split at h using _ | h' | h' <;> first | contradiction | cases h'
      · right
        refine ⟨_, _, _, rfl⟩
      · left
        refine ⟨_, _, rfl⟩

  private theorem relatesTo_eq_label {σₛ σₜ} {v} (h : σₛ ∼[v] σₜ) : σₛ.2.2.2 = σₜ.2.2.2 := by
    obtain ⟨_, -⟩ := h
    assumption

  private theorem GuardedPlusCal.Thread.toNetwork.proc_name_eq
    (Pₜ : NetworkPlusCal.Process Typ (Expression Typ))
    (Pₛ : GuardedPlusCal.Process Typ (Expression Typ))
    (chans : Std.HashMap String (Typ × List (Expression Typ)))
    (compileSuccess : Pₛ.toNetwork inbox chans = Pₜ) :
    Pₛ.name = Pₜ.name := by
      obtain ⟨⟩ := Pₛ
      obtain ⟨⟩ := Pₜ
      injection compileSuccess

  private theorem GuardedPlusCal.Thread.toNetwork.mailbox_eq
    (Pₜ : NetworkPlusCal.Process Typ (Expression Typ))
    (Pₛ : GuardedPlusCal.Process Typ (Expression Typ))
    (chans : Std.HashMap String (Typ × List (Expression Typ)))
    (compileSuccess : Pₛ.toNetwork inbox chans = Pₜ) :
    Pₛ.mailbox = Pₜ.mailbox := by
      obtain ⟨⟩ := Pₛ
      obtain ⟨⟩ := Pₜ
      injection compileSuccess

  private theorem GuardedPlusCal.Thread.toNetwork.processPrecondition_spec₁ {nameₛ} {fifosₛ : Std.HashMap String (Typ × List (Expression Typ))}
    {B : Option (GuardedPlusCal.Block _ _)} :
    ⦃⌜True⌝⦄
    GuardedPlusCal.Thread.toNetwork.processPrecondition inbox nameₛ fifosₛ B
    ⦃⇓ (_, _, _) => ⌜True⌝⦄ := id

  private theorem GuardedPlusCal.Thread.toNetwork_spec₁ {nameₛ} {fifosₛ : Std.HashMap String (Typ × List (Expression Typ))}
    {Tₛ : GuardedPlusCal.Thread Typ (Expression Typ)} :
    ⦃⌜True⌝⦄
    GuardedPlusCal.Thread.toNetwork inbox nameₛ fifosₛ Tₛ
    ⦃⇓ (_, rxs, _) => ⌜∀ t ∈ rxs, t.isRx⌝⦄ := by
      unfold GuardedPlusCal.Thread.toNetwork
      mintro -

      mvcgen

      case inv1 => exact (⇓ (_, ⟨_, _, rxs⟩) => ⌜∀ t ∈ rxs, t.isRx⌝)
      case inv2 => exact (⇓ (_, ⟨_, _, rxs⟩) => ⌜∀ t ∈ rxs, t.isRx⌝)

      case vc4.pre =>
        rintro _ (_|_)

      case post.success =>
        assumption

      case vc2.step.pre =>
        assumption

      case vc5.post.success =>
        assumption

      case vc1.step =>
        mstart
        mspec GuardedPlusCal.Thread.toNetwork.processPrecondition_spec₁
        rename Option _ × _ × _ => r
        obtain _|⟨⟨_, _, _⟩, _⟩ := r.2.2
        · mspec Std.Do.Spec.pure
        · conv => simp_match
          split
          · mspec Std.Do.Spec.pure
            mspec Std.Do.Spec.pure
            mspec Std.Do.Spec.pure
            mpure_intro
            intros t t_in
            rw [List.mem_concat] at t_in
            obtain _|rfl := t_in
            · simp_all
              rename_i IH _ t_in
              exact IH _ t_in
            · trivial
          · mspec Std.Do.Spec.pure

  -- TODO: also consider `rx` threads
  abbrev ProcRefine.{u}
    (Pₛ : GuardedPlusCal.Process.{u} Typ (Expression Typ))
    (Pₜ : NetworkPlusCal.Process.{u} Typ (Expression Typ))
    : Prop :=
      ∀ Bₜ ∈ Pₜ.threads >>= (·.toBlocks), ∃ Bₛ ∈ Pₛ.threads.flatten,
        StrongRefinement (· ∼[Pₛ.mailbox.map λ x ↦ (x, inbox ++ Pₛ.name)] ·) ⟦Bₛ⟧* ⟦Bₛ⟧⊥ ⟦Bₛ⟧∞ ⟦Bₜ⟧* ⟦Bₜ⟧⊥ ⟦Bₜ⟧∞

  theorem GuardedPlusCal.Thread.toNetwork.processPrecondition_spec₂
    {channelsₛ : Std.HashMap String (Typ × List (Expression Typ))}
    {nameₛ : String} {precond} :
      ⦃⌜True⌝⦄
      GuardedPlusCal.Thread.toNetwork.processPrecondition inbox nameₛ channelsₛ precond
      ⦃⇓ (x, Ss, _) => ⌜match x with | .none => Ss = [] ∧ precond = .none | .some _ => precond.isSome⌝⦄ := by
    mintro -
    unfold GuardedPlusCal.Thread.toNetwork.processPrecondition
    match precond with
    | none =>
      mspec Std.Do.Spec.pure
    | some ⟨Ss, S⟩ =>
      mspec Std.Do.Spec.forIn_list ⟨λ (⟨a, _, _⟩, r) ↦ ⌜a = [] ∨ r.fst.isSome⌝, .false⟩ ?_
      · rintro _ S _ _ ⟨B, _, _, _⟩
        mintro h
        cases S with
        | «let» | await =>
          mspec Std.Do.Spec.pure
          mpure_intro
          right
          cases B <;> trivial
        | receive chan ref =>
          conv => simp_match
          split <;> {
            mspec Std.Do.Spec.pure
            mspec Std.Do.Spec.pure
            mspec Std.Do.Spec.pure
            mpure_intro
            right
            split <;> rfl
          }
      · mrename_i h
        mpure h
        obtain h|h := h
        · simp at h
        · mpure_intro
          obtain ⟨B, r_eq⟩ := Option.isSome_iff_exists.mp h
          rw [r_eq]
          trivial

  theorem GuardedPlusCal.Thread.toNetwork.processBlock.last_eq
    {actionₛ : GuardedPlusCal.Block (GuardedPlusCal.Statement Typ (Expression Typ) false) true} :
    (GuardedPlusCal.Thread.toNetwork.processBlock actionₛ).last = match_source actionₛ.last with | .goto label, pos => .goto label @@ pos := by
      rfl

  theorem GuardedPlusCal.Thread.toNetwork.processBlock.begin_empty_if
    {actionₛ : GuardedPlusCal.Block (GuardedPlusCal.Statement Typ (Expression Typ) false) true}
    (h : (GuardedPlusCal.Thread.toNetwork.processBlock actionₛ).begin = []) :
    actionₛ.begin = [] := by
      erwa [List.map_eq_nil_iff] at h

  theorem GuardedPlusCal.Thread.toNetwork.processBlock.begin_eq_cons_if
    {actionₛ : GuardedPlusCal.Block (GuardedPlusCal.Statement Typ (Expression Typ) false) true} {S Ss}
    (h : (GuardedPlusCal.Thread.toNetwork.processBlock actionₛ).begin = S :: Ss) :
      ∃ S' Ss', actionₛ.begin = S' :: Ss' ∧ S = (match_source S' with
        | .skip, pos => .skip @@ pos
        | .print e, pos => .print e @@ pos
        | .assert e, pos => .assert e @@ pos
        | .send chan e, pos => .send chan e @@ pos
        | .multicast chan bs e, pos => .multicast chan bs e @@ pos
        | .assign ref e, pos => .assign ref e @@ pos) ∧ Ss = Ss'.map λ S' ↦ match_source S' with
          | .skip, pos => .skip @@ pos
          | .print e, pos => .print e @@ pos
          | .assert e, pos => .assert e @@ pos
          | .send chan e, pos => .send chan e @@ pos
          | .multicast chan bs e, pos => .multicast chan bs e @@ pos
          | .assign ref e, pos => .assign ref e @@ pos := by
    erw [List.map_eq_cons_iff] at h
    obtain ⟨S, Ss, _, rfl, rfl⟩ := h
    exists S, Ss

  theorem GuardedPlusCal.Thread.toNetwork.processBlock.end_eq_end {label} :
    GuardedPlusCal.Thread.toNetwork.processBlock (.end (.goto label)) = .end (.goto label) := by
      rfl

  theorem GuardedPlusCal.Thread.toNetwork.processBlock.cons_eq_cons {S} {B} : GuardedPlusCal.Thread.toNetwork.processBlock (.cons S B) = .cons (match_source S with
    | .skip, pos => .skip @@ pos
    | .print e, pos => .print e @@ pos
    | .assert e, pos => .assert e @@ pos
    | .send chan e, pos => .send chan e @@ pos
    | .multicast chan bs e, pos => .multicast chan bs e @@ pos
    | .assign ref e, pos => .assign ref e @@ pos) (GuardedPlusCal.Thread.toNetwork.processBlock B) := by
      rfl

  -- TODO: move into TypedSetTheory
  theorem eval_ext {M₁ M₂ : TypedSetTheory.Memory} {e : Expression Typ} (ys : List String)
    (mem_ext : ∀ x ∉ ys, M₁.lookup x = M₂.lookup x) (ys_not_in_freevars : List.Disjoint ys e.freeVars) :
    TypedSetTheory.eval M₁ e = TypedSetTheory.eval M₂ e := by
      trans TypedSetTheory.eval (M₁.removeAll ys) e
      · clear mem_ext
        induction ys with
        | nil => rw [AList.removeAll_nil]
        | cons y ys IH =>
          rw [AList.removeAll_cons', IH]
          · apply TypedSetTheory.eval_not_fv_irrel
            simp_all
          · simp_all
      · trans TypedSetTheory.eval (M₂.removeAll ys) e
        · apply TypedSetTheory.eval_mem_ext
          intro x
          by_cases x_in : x ∈ ys
          · repeat rw [AList.lookup_removeAll_mem]
            · assumption
            · assumption
          · repeat rw [AList.lookup_removeAll_not_mem]
            · apply mem_ext _ x_in
            · assumption
            · assumption
        · clear mem_ext
          induction ys with
          | nil => rw [AList.removeAll_nil]
          | cons y ys IH =>
            rw [AList.removeAll_cons', ← IH]
            · symm
              apply TypedSetTheory.eval_not_fv_irrel
              simp_all
            · simp_all

  theorem not_mem_of_fresh {Typ} {e : Expression Typ} {x} (h : e.FreshIn x) :
      x ∉ e.freeVars := by
    fun_induction e.FreshIn x <;> (
      -- unfold Expression.FreshIn at h
      unfold Expression.freeVars
    )
    case case1 => rwa [List.not_mem_singleton]
    case case2 => apply List.not_mem_nil
    case case3 => apply List.not_mem_nil
    case case4 => apply List.not_mem_nil
    case case5 _ IH =>
      simp_rw [List.mem_flatMap, not_exists, not_and]
      rintro ⟨_, _⟩ _
      apply_rules [IH]
    case case6 _ IH =>
      simp_rw [List.mem_flatMap, not_exists, not_and]
      rintro ⟨_, _⟩ _
      apply_rules [IH]
    case case7 _ _ IH =>
      apply_rules [IH]
    case case8 _ _ _ IH₁ IH₂ =>
      obtain ⟨_, _⟩ := h
      rw [List.not_mem_union_iff]
      constructor <;> apply_rules [IH₁, IH₂]
    case case9 _ _ IH₁ IH₂ =>
      obtain ⟨_, _⟩ := h
      simp_rw [List.not_mem_union_iff, List.mem_flatMap, not_exists, not_and]
      constructor
      · apply_rules [IH₁]
      · rintro ⟨_, _⟩ _
        apply_rules [IH₂]
    case case10 _ _ IH =>
      apply_rules [IH]
    case case11 _ IH =>
      simp_rw [List.mem_flatMap, not_exists, not_and]
      rintro ⟨_, _⟩ _
      apply_rules [IH]
    case case12 _ _ IH₁ IH₂ =>
      obtain ⟨_, _⟩ := h
      simp_rw [List.not_mem_union_iff, List.mem_flatMap, not_exists, not_and]
      constructor
      · apply_rules [IH₁]
      · rintro ⟨_, _⟩ _
        apply_rules [IH₂]
    case case13 _ _ IH₁ IH₂ IH₃ =>
      obtain ⟨_, h⟩ := h
      simp_rw [List.not_mem_union_iff, List.mem_flatMap, not_exists, not_and]
      constructor
      · apply_rules [IH₁]
      · rintro ⟨upd, upd_in⟩ _
        obtain ⟨_, h⟩ := h upd upd_in
        simp_rw [List.not_mem_union_iff, List.mem_flatMap, not_exists, not_and]
        constructor
        · rintro ⟨idx, idx_in⟩ _
          split
          · specialize h idx idx_in
            injections; subst idx
            simp_rw [List.mem_flatMap, not_exists, not_and]
            rintro ⟨_, _⟩ _
            apply_rules [IH₃]
          · apply List.not_mem_nil
        · apply_rules [IH₂]

  theorem fresh_of_wellscoped_of_not_mem {Typ} {e : Expression Typ} {x} {Γ : Scope} (h : e.WellScoped Γ) (h' : x ∉ Γ) : e.FreshIn x := by
    fun_induction Expression.WellScoped e Γ <;> (
      -- unfold Expression.WellScoped at h
      unfold Expression.FreshIn
    )
    case case1 => exact Ne.symm (ne_of_mem_of_not_mem h h')
    case case2 | case3 | case4 => apply True.intro
    case case5 _ IH =>
      intros e e_in
      apply_rules [IH]
    case case6 _ IH =>
      rintro ⟨_, _, e⟩ f_in
      apply_rules [IH]
    case case7 _ _ IH =>
      apply_rules [IH]
    case case8 _ _ _ IH₁ IH₂ =>
      obtain ⟨_, _⟩ := h
      apply_rules [And.intro, IH₁, IH₂]
    case case9 _ _ IH₁ IH₂ =>
      obtain ⟨_, _⟩ := h
      constructor
      · apply_rules [IH₁]
      · intros _ _
        apply_rules [IH₂]
    case case10 _ _ IH =>
      apply_rules [IH]
    case case11 _ IH =>
      intros _ _
      apply_rules [IH]
    case case12 _ _ IH₁ IH₂ =>
      obtain ⟨_, _⟩ := h
      constructor
      · apply_rules [IH₁]
      · intros _ _
        apply_rules [IH₂]
    case case13 _ _ IH₁ IH₂ IH₃ =>
      obtain ⟨_, h⟩ := h
      constructor
      · apply_rules [IH₁]
      · intros upd upd_in
        obtain ⟨_, h⟩ := h upd upd_in
        constructor
        · apply_rules [IH₂]
        · intros idx idx_in
          specialize h idx idx_in
          split <;> [
              apply True.intro
            | (intros _ _; apply_rules [IH₃])
          ]

  theorem wellscoped_mono_of_subset {Typ} {e : Expression Typ} {Γ Γ' : Scope} (h : e.WellScoped Γ) (h' : Γ ⊆ Γ') : e.WellScoped Γ' := by
    fun_induction Expression.WellScoped e Γ <;> unfold Expression.WellScoped at ⊢
    case case1 =>
      apply_rules [h']
    case case2 => apply True.intro
    case case3 => apply True.intro
    case case4 => apply True.intro
    case case5 _ IH =>
      intros _ _
      apply_rules [IH]
    case case6 _ IH =>
      intros _ _
      apply_rules [IH]
    case case7 _ _ IH =>
      apply_rules [IH]
    case case8 _ _ _ IH₁ IH₂ =>
      obtain ⟨_, _⟩ := h
      constructor <;> apply_rules [IH₁, IH₂]
    case case9 _ _ IH₁ IH₂ =>
      obtain ⟨_, _⟩ := h
      constructor
      · apply_rules [IH₁]
      · intros _ _
        apply_rules [IH₂]
    case case10 _ _ IH =>
      apply_rules [IH]
    case case11 _ IH =>
      intros _ _
      apply_rules [IH]
    case case12 _ _ IH₁ IH₂ =>
      obtain ⟨_, _⟩ := h
      constructor
      · apply_rules [IH₁]
      · intros _ _
        apply_rules [IH₂]
    case case13 _ _ IH₁ IH₂ IH₃ =>
      obtain ⟨_, h⟩ := h
      constructor
      · apply_rules [IH₁]
      · intros arg arg_in
        obtain ⟨_, h⟩ := h arg arg_in
        constructor
        · apply_rules [IH₂]
        · intros idx idx_in
          specialize h idx idx_in
          split <;> [
              apply True.intro
            | (intros _ _; apply_rules [IH₃])
          ]

  section
    open Lean Parser Tactic

    /--
      Tries to instantiate a semantic configuration on all levels based on the given terms.
      Must be given either 4 or 3 arguments depending on whether the state to be instantiated is final or not.
    -/
    syntax "sem_exists " term (" ⤳ " term)? ", " term (" ⤳ " term)? ", " term (" ⤳ " term)? (", " term)? : tactic
    macro_rules
    | `(tactic| sem_exists $w₁ $[⤳ $w₂]?, $x₁ $[⤳ $x₂]?, $y₁ $[⤳ $y₂]? $[, $z]?) => do
      let z' ← z.elim `(Option.none) λ z ↦ `(Option.some $z)
      `(tactic|
        refine ⟨GuardedPlusCal.LocalState'.mk $(w₂.getD w₁) $(x₂.getD x₁) $(y₂.getD y₁) $z', ?_, ?_⟩;
        2: sem_redg $w₁ $[⤳ $w₂]?, $x₁ $[⤳ $x₂]?, $y₁ $[⤳ $y₂]? $[, $z]?
      )
  end

  lemma NetworkPlusCal.Statement.div_empty.{u} {b b'} {S : NetworkPlusCal.Statement.{u} Typ (Expression Typ) b b'} :
      ⟦S⟧∞ = ∅ := by
    ext ⟨⟨M, T, F, l⟩, ε⟩
    iff_rintro ⟨rfl, _, _⟩ (_|_)

  lemma NetworkPlusCal.Block.div_empty.{u} {b b'} {B : GuardedPlusCal.Block.{u} (NetworkPlusCal.Statement Typ (Expression Typ) b) b'} :
      ⟦B⟧∞ = ∅ := by
    ext ⟨⟨M, T, F, l⟩, ε⟩
    iff_rintro h (_|_)
    · unfold_projs at h
      unfold GuardedPlusCal.Block.diverging at h

      generalize B.begin = Ss at h
      generalize ((M, T, F, l), ε) = σ at h ⊢
      induction Ss generalizing σ with
      | nil =>
        let ⟨(_, _, _, _), _⟩ := σ
        obtain ⟨rfl, _, _⟩ := h
      | cons S Ss IH =>
        dsimp at h
        obtain h|h := h
        · let ⟨(_, _, _, _), _⟩ := σ
          obtain ⟨rfl, _, _⟩ := h
        · let ⟨(_, _, _, _), _⟩ := σ
          obtain ⟨σ', ε₁, ε₂, h₁, h₂, rfl⟩ := h
          unfold GuardedPlusCal.Block.diverging at h₂
          apply IH _ h₂

  lemma NetworkPlusCal.AtomicBranch.div_empty.{u} {Br : NetworkPlusCal.AtomicBranch.{u} Typ (Expression Typ)} :
      ⟦Br⟧∞ = ∅ := by
    ext ⟨⟨M, T, F, l⟩, ε⟩
    iff_rintro h (_|_)
    · rw [NetworkPlusCal.AtomicBranch.div_eq] at h
      obtain div_precond|⟨_, _, _, red_precond, div_action, rfl⟩ := h
      · cases h : Br.precondition with
        | none =>
          rwa [h] at div_precond
        | some precond =>
          rw [h] at div_precond
          dsimp at div_precond
          rwa [NetworkPlusCal.Block.div_empty (B := precond)] at div_precond
      · rw [NetworkPlusCal.Block.div_empty] at div_action
        assumption

  -- set_option pp.universes true in
  lemma NetworkPlusCal.AtomicBlock.div_empty.{u} {Br : NetworkPlusCal.AtomicBlock.{u} Typ (Expression Typ)} :
      (⟦Br⟧∞ : Set.{u} _) = ∅ := by
    ext ⟨⟨M, T, F, l⟩, ε⟩
    iff_rintro h (_|_)
    · change ∃ _, _ at h
      obtain ⟨B, _, h, rfl⟩ := h
      rw [← NetworkPlusCal.LocalState.div_glue₃, AtomicBranch.div_empty] at h
      assumption

  lemma NetworkPlusCal.Statement.abort_skip.{u} :
      ⟦@NetworkPlusCal.Statement.skip.{u} Typ (Expression Typ)⟧⊥ = ∅ := by
    ext ⟨⟨M, T, F, l⟩, ε⟩
    iff_rintro ⟨rfl, _, _⟩ (_|_)

  lemma GuardedPlusCal.Statement.strong_refinement.skip.{u} {mailbox : Option (Expression.{u} Typ × String)} :
      StrongRefinement (· ∼[mailbox] ·)
        ⟦@GuardedPlusCal.Statement.skip.{u} Typ (Expression Typ)⟧*
        ⟦@GuardedPlusCal.Statement.skip Typ (Expression Typ)⟧⊥
        ⟦@GuardedPlusCal.Statement.skip.{u} Typ (Expression Typ)⟧∞
        ⟦@NetworkPlusCal.Statement.skip.{u} Typ (Expression Typ)⟧*
        ⟦@NetworkPlusCal.Statement.skip Typ (Expression Typ)⟧⊥
        ⟦@NetworkPlusCal.Statement.skip Typ (Expression Typ)⟧∞ := by
    rw [NetworkPlusCal.Statement.abort_skip, NetworkPlusCal.Statement.div_empty]
    apply StrongRefinement.ofTerminating
    rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ⟨Mₜ', Tₜ', Fₜ', lₜ'⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim sem_Sₜ
    obtain ⟨_, rfl, ⟨_, _, _, _|_, _|_, _|_⟩, _|_, rfl⟩ := sem_Sₜ
    left
    sem_exists Mₛ, Tₛ, Fₛ
    · conv at sim => enter [2, 2, 2, 2]; apply relatesTo_eq_label sim
      exact sim
    · exact relatesTo_eq_label sim

  lemma GuardedPlusCal.Statement.strong_refinement.print.{u}
    {mailbox : Option (Expression.{u} Typ × String)}
    {e : Expression.{u} Typ}
    (wf : match mailbox with | .none => True | .some ⟨_, inbox⟩ => e.FreshIn inbox) :
      StrongRefinement (· ∼[mailbox] ·)
        ⟦@GuardedPlusCal.Statement.print.{u} Typ _ e⟧*
        ⟦@GuardedPlusCal.Statement.print Typ _ e⟧⊥
        ⟦@GuardedPlusCal.Statement.print Typ _ e⟧∞
        ⟦@NetworkPlusCal.Statement.print.{u} Typ _ e⟧*
        ⟦@NetworkPlusCal.Statement.print Typ _ e⟧⊥
        ⟦@NetworkPlusCal.Statement.print Typ _ e⟧∞ := by
    rw [NetworkPlusCal.Statement.div_empty]
    apply StrongRefinement.ofNonDiverging
    · rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ⟨Mₜ', Tₜ', Fₜ', lₜ'⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim sem_Sₜ
      obtain ⟨_, rfl, ⟨_, _, _, v, _|_, rfl, eval_e_eq_v, rfl⟩, _|_, rfl⟩ := sem_Sₜ
      left
      sem_exists Mₛ, Tₛ, Fₛ
      · conv at sim => enter [2, 2, 2, 2]; apply relatesTo_eq_label sim
        exact sim
      · exact relatesTo_eq_label sim
      · match mailbox with
        | .none => rwa [sim.right.left, sim.right.right.left]
        | .some (_, inbox) =>
          rw [← eval_e_eq_v]
          apply eval_ext [inbox]
          · intros v v_not_in
            rw [List.not_mem_singleton] at v_not_in
            obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
              obtain ⟨_, mem_ext, rfl, _⟩ := sim
              simp_rw [AList.lookup_union, mem_ext _ v_not_in]
            }
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            exact wf
    · rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim ⟨rfl, _, _, _, eval_e_eq_v, _|_, rfl⟩
      exists [], le_rfl
      -- abort_redg?
      use ?_, Mₛ, Tₛ, Fₛ, ?_, rfl
      · exact relatesTo_eq_label sim
      · match mailbox with
        | .none => rwa [sim.right.left, sim.right.right.left]
        | .some (_, inbox) =>
          rw [← eval_e_eq_v]
          apply eval_ext [inbox]
          · intros v v_not_in
            rw [List.not_mem_singleton] at v_not_in
            obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
              obtain ⟨_, mem_ext, rfl, _⟩ := sim
              simp_rw [AList.lookup_union, mem_ext _ v_not_in]
            }
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            exact wf

  lemma GuardedPlusCal.Statement.strong_refinement.assert.{u}
    {mailbox : Option (Expression.{u} Typ × String)}
    {e : Expression.{u} Typ}
    (wf : match mailbox with | .none => True | .some ⟨_, inbox⟩ => e.FreshIn inbox) :
      StrongRefinement (· ∼[mailbox] ·)
        ⟦@GuardedPlusCal.Statement.assert.{u} Typ _ e⟧*
      ⟦@GuardedPlusCal.Statement.assert Typ _ e⟧⊥
      ⟦@GuardedPlusCal.Statement.assert Typ _ e⟧∞
        ⟦@NetworkPlusCal.Statement.assert.{u} Typ _ e⟧*
        ⟦@NetworkPlusCal.Statement.assert Typ _ e⟧⊥
        ⟦@NetworkPlusCal.Statement.assert Typ _ e⟧∞ := by
    rw [NetworkPlusCal.Statement.div_empty]
    apply StrongRefinement.ofNonDiverging
    · rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ⟨Mₜ', Tₜ', Fₜ', lₜ'⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim sem_Sₜ
      obtain ⟨_, rfl, ⟨_, _, _, _|_, rfl, eval_e_eq_v, rfl⟩, _|_, rfl⟩ := sem_Sₜ
      left
      sem_exists Mₛ, Tₛ, Fₛ
      · conv at sim => enter [2, 2, 2, 2]; apply relatesTo_eq_label sim
        exact sim
      · exact relatesTo_eq_label sim
      · match mailbox with
        | .none => rwa [sim.right.left, sim.right.right.left]
        | .some (_, inbox) =>
          rw [← eval_e_eq_v]
          apply eval_ext [inbox]
          · intros v v_not_in
            rw [List.not_mem_singleton] at v_not_in
            obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
              obtain ⟨_, mem_ext, rfl, _⟩ := sim
              simp_rw [AList.lookup_union, mem_ext _ v_not_in]
            }
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            assumption
    · rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim ⟨rfl, ⟨_, _, _, eval_e_eq_v, _|_, rfl⟩|⟨_, _, _, v, v_not_bool, eval_e_eq_v, _|_, rfl⟩⟩
        <;> exists [], le_rfl, relatesTo_eq_label sim
        <;> [ (left; use Mₛ, Tₛ, Fₛ, ?_, rfl)
            | (right; use Mₛ, Tₛ, Fₛ, v, v_not_bool, ?_, rfl) ]
        <;> {
          match mailbox with
          | .none => rwa [sim.right.left, sim.right.right.left]
          | .some (_, inbox) =>
            rw [← eval_e_eq_v]
            apply eval_ext [inbox]
            · intros v v_not_in
              rw [List.not_mem_singleton] at v_not_in
              obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
                obtain ⟨_, mem_ext, rfl, _⟩ := sim
                simp_rw [AList.lookup_union, mem_ext _ v_not_in]
              }
            · rw [List.singleton_disjoint]
              apply not_mem_of_fresh
              exact wf
        }

  lemma GuardedPlusCal.Statement.strong_refinement.send.{u}
    {chan} {mailbox : Option (Expression.{u} Typ × String)}
    {e : Expression.{u} Typ}
    (wf : match mailbox with | .none => True | .some ⟨_, inbox⟩ => chan.name ≠ inbox ∧ (∀ arg ∈ chan.args, arg.FreshIn inbox) ∧ e.FreshIn inbox) :
      StrongRefinement (· ∼[mailbox] ·)
        ⟦@GuardedPlusCal.Statement.send.{u} Typ _ chan e⟧*
        ⟦@GuardedPlusCal.Statement.send Typ _ chan e⟧⊥
        ⟦@GuardedPlusCal.Statement.send Typ _ chan e⟧∞
        ⟦@NetworkPlusCal.Statement.send.{u} Typ _ chan e⟧*
        ⟦@NetworkPlusCal.Statement.send Typ _ chan e⟧⊥
        ⟦@NetworkPlusCal.Statement.send Typ _ chan e⟧∞ := by
    rw [NetworkPlusCal.Statement.div_empty]
    apply StrongRefinement.ofNonDiverging
    · rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ⟨Mₜ', Tₜ', Fₜ', lₜ'⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim sem_Sₜ
      left
      obtain ⟨_, rfl, ⟨_, _, _, v, vs, vs', eval_e_eq_v, chan_args_eval_vs, lookup_Fₜ, _|_, _|_, rfl⟩, _|_, rfl⟩ := sem_Sₜ
      -- Unfortunately, we have to match on the mailbox this far down, before instantiating the semantics
      match mailbox with
      | .none =>
        sem_exists Mₛ, Tₛ, Fₛ ⤳ Fₛ.map λ ⟨c, es⟩ vs' ↦ if c = chan.name ∧ es = vs then vs'.concat v else vs'
        · rw [sim.right.left, sim.right.right.left, sim.right.right.right, ← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
          · and_intros <;> try rfl
            congr
            simp [Prod.ext_iff]
          · assumption
        · exact relatesTo_eq_label sim
        -- · exact v
        · exact vs'
        -- · exact vs'
        · rwa [sim.right.left, sim.right.right.left]
        · rwa [sim.right.left, sim.right.right.left]
        · rwa [sim.right.right.right]
        · rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
          · congr
            simp [Prod.ext_iff]
          · rwa [sim.right.right.right]
      | .some (_, inbox) =>
        obtain ⟨c, _, rfl⟩|⟨c, _, _, rfl⟩ := relatesTo_mailbox_shape sim
        · obtain ⟨rfl, mem_ext, rfl, vs'', inbox_eq, inbox_not_in_Tₛ, fifos_ext₁, fifos_ext₂, lookup_Fₛ⟩ := sim
          by_cases h : c = chan.name ∧ vs = []
          · obtain ⟨rfl, rfl⟩ := h
            erw [lookup_Fₜ, pure_bind, Option.pure_def] at lookup_Fₛ
            sem_exists Mₛ, Tₛ, Fₛ ⤳ Fₛ.map λ ⟨c, es⟩ vs' ↦ if c = chan.name ∧ es = [] then vs'.concat v else vs'
            · and_intros <;> try trivial
              exists vs'', inbox_eq
              and_intros
              · assumption
              · refine forall_imp (λ c' ↦ ?_) fifos_ext₁
                refine forall_imp (λ c'_neq ↦ ?_)
                refine forall_imp (λ es' h ↦ ?_)
                rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  congr
                  simp [Prod.ext_iff]
                · assumption
              · refine forall_imp (λ es' ↦ ?_) fifos_ext₂
                refine forall_imp (λ es'_neq h ↦ ?_)
                rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  congr
                  simp [Prod.ext_iff]
                · assumption
              · rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  erw [bind_pure_comp, Functor.map_map, lookup_Fₛ, lookup_Fₜ]
                  repeat rw [Option.map_eq_map, Option.map_some]
                  congr
                  simp
                · assumption
            -- · exact v
            -- · exact []
            · exact vs'' ++ vs'
            · rw [← eval_e_eq_v]
              apply eval_ext [inbox]
              · intros x x_not_in
                rw [List.not_mem_singleton] at x_not_in
                simp_rw [AList.lookup_union, mem_ext _ x_not_in]
              · rw [List.singleton_disjoint]
                -- dsimp [GuardedPlusCal.Statement.freeVars] at wf
                obtain ⟨_, _, _⟩ := wf
                apply not_mem_of_fresh
                assumption
            · simp_all
              -- rw [← List.forall₂_iff_forall₂_attach] at chan_args_eval_vs ⊢
              -- refine List.Forall₂.imp ?_ chan_args_eval_vs
              -- rintro ⟨e, e_in⟩ ⟨v, v_in⟩ eval_e_eq
              -- rw [← eval_e_eq]
              -- apply eval_ext [inbox]
              -- · intros x x_not_in
              --   rw [List.not_mem_singleton] at x_not_in
              --   simp_rw [AList.lookup_union, mem_ext _ x_not_in]
              -- · rw [List.singleton_disjoint]
              --   dsimp [GuardedPlusCal.Statement.freeVars, GuardedPlusCal.ChanRef.freeVars] at wf
              --   obtain ⟨-, wf, -⟩ := wf
              --   --intros h
              --   --apply List.mem_flatMap_of_mem e_in at h
              --   contradiction
            · assumption
            · rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
              · congr
                simp [Prod.ext_iff]
              · assumption
            -- · rfl
          · rw [not_and_or] at h
            sem_exists Mₛ, Tₛ, Fₛ ⤳ Fₛ.map λ ⟨c, es⟩ vs' ↦ if c = chan.name ∧ es = vs then vs'.concat v else vs'
            · and_intros <;> try trivial
              exists vs'', inbox_eq
              and_intros
              · assumption
              · refine forall_imp (λ c' ↦ ?_) fifos_ext₁
                refine forall_imp (λ c'_neq ↦ ?_)
                refine forall_imp (λ es' h ↦ ?_)
                rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  congr
                  simp [Prod.ext_iff]
                · assumption
              · refine forall_imp (λ es' ↦ ?_) fifos_ext₂
                refine forall_imp (λ es'_neq h ↦ ?_)
                rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  congr
                  simp [Prod.ext_iff]
                · assumption
              · rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  rw [lookup_Fₛ]
                  repeat erw [bind_pure_comp, Functor.map_map]
                  congr
                  have h₁ : (c = chan.name ∧ vs = []) = False := eq_false <| by
                    rwa [← not_and_or] at h
                  simp [ite_cond_eq_false _ _ h₁]
                · assumption
            -- · exact v
            -- · exact vs
            · exact vs'
            · rw [← eval_e_eq_v]
              apply eval_ext [inbox]
              · intros x x_not_in
                rw [List.not_mem_singleton] at x_not_in
                simp_rw [AList.lookup_union, mem_ext _ x_not_in]
              · rw [List.singleton_disjoint]
                obtain ⟨_, _, _⟩ := wf
                apply not_mem_of_fresh
                assumption
            · rw [← List.forall₂_iff_forall₂_attach] at chan_args_eval_vs ⊢
              refine List.Forall₂.imp ?_ chan_args_eval_vs
              rintro ⟨e, e_in⟩ ⟨v, v_in⟩ eval_e_eq
              rw [← eval_e_eq]
              apply eval_ext [inbox]
              · intros x x_not_in
                rw [List.not_mem_singleton] at x_not_in
                simp_rw [AList.lookup_union, mem_ext _ x_not_in]
              · rw [List.singleton_disjoint]
                --dsimp [GuardedPlusCal.Statement.freeVars, GuardedPlusCal.ChanRef.freeVars] at wf
                --rw [List.not_mem_cons_iff, List.not_mem_append_iff] at wf
                obtain ⟨-, wf, -⟩ := wf
                specialize wf _ e_in
                apply not_mem_of_fresh
                assumption
            · rw [← lookup_Fₜ]
              obtain _|_ := h
              · apply fifos_ext₁
                symm
                assumption
              · by_cases h' : c = chan.name
                · subst c
                  apply fifos_ext₂
                  assumption
                · apply fifos_ext₁
                  symm
                  assumption
            · rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
              · congr
                simp [Prod.ext_iff]
              · rw [← lookup_Fₜ]
                obtain _|_ := h
                · apply fifos_ext₁
                  symm
                  assumption
                · by_cases h' : c = chan.name
                  · subst c
                    apply fifos_ext₂
                    assumption
                  · apply fifos_ext₁
                    symm
                    assumption
            -- · rfl
        · obtain ⟨rfl, mem_ext, rfl, vs'', inbox_eq, inbox_not_in_Tₛ, es, eval_es, fifos_ext₁, fifos_ext₂, lookup_Fₛ⟩ := sim
          by_cases h : c = chan.name ∧ vs = [es]
          · obtain ⟨rfl, rfl⟩ := h
            erw [lookup_Fₜ, pure_bind, Option.pure_def] at lookup_Fₛ
            sem_exists Mₛ, Tₛ, Fₛ ⤳ Fₛ.map λ ⟨c, es'⟩ vs' ↦ if c = chan.name ∧ es' = [es] then vs'.concat v else vs'
            · and_intros <;> try trivial
              exists vs'', inbox_eq, inbox_not_in_Tₛ, es, eval_es
              and_intros
              · refine forall_imp (λ c' ↦ ?_) fifos_ext₁
                refine forall_imp (λ c'_neq ↦ ?_)
                refine forall_imp (λ es' h ↦ ?_)
                rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  congr
                  simp [Prod.ext_iff]
                · assumption
              · refine forall_imp (λ es' ↦ ?_) fifos_ext₂
                refine forall_imp (λ es'_neq h ↦ ?_)
                rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  congr
                  simp [Prod.ext_iff]
                · assumption
              · rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  erw [bind_pure_comp, Functor.map_map, lookup_Fₛ, lookup_Fₜ]
                  repeat rw [Option.map_eq_map, Option.map_some]
                  congr
                  simp
                · assumption
            -- · exact v
            -- · exact [es]
            · exact vs'' ++ vs'
            · rw [← eval_e_eq_v]
              apply eval_ext [inbox]
              · intros x x_not_in
                rw [List.not_mem_singleton] at x_not_in
                simp_rw [AList.lookup_union, mem_ext _ x_not_in]
              · rw [List.singleton_disjoint]
                obtain ⟨_, _, _⟩ := wf
                apply not_mem_of_fresh
                assumption
            · rw [← List.forall₂_iff_forall₂_attach] at chan_args_eval_vs ⊢
              refine List.Forall₂.imp ?_ chan_args_eval_vs
              rintro ⟨e, e_in⟩ ⟨v, v_in⟩ eval_e_eq
              rw [← eval_e_eq]
              apply eval_ext [inbox]
              · intros x x_not_in
                rw [List.not_mem_singleton] at x_not_in
                simp_rw [AList.lookup_union, mem_ext _ x_not_in]
              · rw [List.singleton_disjoint]
                -- dsimp [GuardedPlusCal.Statement.freeVars, GuardedPlusCal.ChanRef.freeVars] at wf
                -- rw [List.not_mem_cons_iff, List.not_mem_append_iff] at wf
                obtain ⟨-, wf, -⟩ := wf
                specialize wf _ e_in
                apply not_mem_of_fresh
                assumption
            · assumption
            · rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
              · congr
                simp [Prod.ext_iff]
              · assumption
            -- · rfl
          · rw [not_and_or] at h
            sem_exists Mₛ, Tₛ, Fₛ ⤳ Fₛ.map λ ⟨c, es⟩ vs' ↦ if c = chan.name ∧ es = vs then vs'.concat v else vs'
            · and_intros <;> try trivial
              exists vs'', inbox_eq, inbox_not_in_Tₛ, es, eval_es
              and_intros
              · refine forall_imp (λ c' ↦ ?_) fifos_ext₁
                refine forall_imp (λ c'_neq ↦ ?_)
                refine forall_imp (λ es' h ↦ ?_)
                rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  congr
                  simp [Prod.ext_iff]
                · assumption
              · refine forall_imp (λ es' ↦ ?_) fifos_ext₂
                refine forall_imp (λ es'_neq h ↦ ?_)
                rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  congr
                  simp [Prod.ext_iff]
                · assumption
              · rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
                · repeat rw [AList.lookup_map]
                  rw [lookup_Fₛ]
                  repeat erw [bind_pure_comp, Functor.map_map]
                  congr
                  have h₁ : (c = chan.name ∧ [es] = vs) = False := eq_false <| by
                    rw [← not_and_or] at h
                    rintro ⟨h₁, h₂⟩
                    exact h ⟨h₁, Eq.symm h₂⟩
                  simp [ite_cond_eq_false _ _ h₁]
                · assumption
            -- · exact v
            -- · exact vs
            · exact vs'
            · rw [← eval_e_eq_v]
              apply eval_ext [inbox]
              · intros x x_not_in
                rw [List.not_mem_singleton] at x_not_in
                simp_rw [AList.lookup_union, mem_ext _ x_not_in]
              · rw [List.singleton_disjoint]
                obtain ⟨_, _, _⟩ := wf
                apply not_mem_of_fresh
                assumption
            · rw [← List.forall₂_iff_forall₂_attach] at chan_args_eval_vs ⊢
              refine List.Forall₂.imp ?_ chan_args_eval_vs
              rintro ⟨e, e_in⟩ ⟨v, v_in⟩ eval_e_eq
              rw [← eval_e_eq]
              apply eval_ext [inbox]
              · intros x x_not_in
                rw [List.not_mem_singleton] at x_not_in
                simp_rw [AList.lookup_union, mem_ext _ x_not_in]
              · rw [List.singleton_disjoint]
                --dsimp [GuardedPlusCal.Statement.freeVars, GuardedPlusCal.ChanRef.freeVars] at wf
                --rw [List.not_mem_cons_iff, List.not_mem_append_iff] at wf
                obtain ⟨-, wf, -⟩ := wf
                specialize wf _ e_in
                apply not_mem_of_fresh
                assumption
            · rw [← lookup_Fₜ]
              obtain _|_ := h
              · apply fifos_ext₁
                symm
                assumption
              · by_cases h' : c = chan.name
                · subst c
                  apply fifos_ext₂
                  assumption
                · apply fifos_ext₁
                  symm
                  assumption
            · rw [← AList.replace_eq_map (f := λ _ vs ↦ List.concat vs v)]
              · congr
                simp [Prod.ext_iff]
              · rw [← lookup_Fₜ]
                obtain _|_ := h
                · apply fifos_ext₁
                  symm
                  assumption
                · by_cases h' : c = chan.name
                  · subst c
                    apply fifos_ext₂
                    assumption
                  · apply fifos_ext₁
                    symm
                    assumption
            -- · rfl
    · rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim ⟨rfl, red⟩
      obtain (⟨_, _, _, eval_e, _|_, rfl⟩|⟨e, e_in, _, _, _, eval_e, _|_, rfl⟩)|⟨_, _, _, vs, eval_args, lookup_Fₜ, _|_, rfl⟩ := red
      · exists [], le_rfl
        constructor
        · exact relatesTo_eq_label sim
        · left; left
          exists Mₛ, Tₛ, Fₛ, ?_, ?_ <;> try rfl
          match mailbox with
          | .none => rwa [sim.right.left, sim.right.right.left]
          | .some (_, inbox) =>
            rw [← eval_e]
            apply eval_ext [inbox]
            · intros v v_not_in
              rw [List.not_mem_singleton] at v_not_in
              obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
                obtain ⟨_, mem_ext, rfl, _⟩ := sim
                simp_rw [AList.lookup_union, mem_ext _ v_not_in]
              }
            · rw [List.singleton_disjoint]
              apply not_mem_of_fresh
              exact wf.2.2
      · exists [], le_rfl
        constructor
        · exact relatesTo_eq_label sim
        · left; right
          exists e, e_in, Mₛ, Tₛ, Fₛ, ?_, ?_ <;> try trivial
          match mailbox with
          | .none => rwa [sim.right.left, sim.right.right.left]
          | .some (_, inbox) =>
            rw [← eval_e]
            apply eval_ext [inbox]
            · intros v v_not_in
              rw [List.not_mem_singleton] at v_not_in
              obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
                obtain ⟨_, mem_ext, rfl, _⟩ := sim
                simp_rw [AList.lookup_union, mem_ext _ v_not_in]
              }
            · rw [List.singleton_disjoint]
              apply not_mem_of_fresh
              exact wf.2.1 _ e_in
      · exists [], le_rfl
        constructor
        · exact relatesTo_eq_label sim
        · right
          exists Mₛ, Tₛ, Fₛ, vs, ?_, ?_, ?_ <;> try trivial
          · match mailbox with
            | none =>
              obtain ⟨rfl, rfl, rfl, rfl⟩ := sim
              assumption
            | some (_, inbox) =>
              rw [← List.forall₂_iff_forall₂_attach] at eval_args ⊢
              refine List.Forall₂.imp ?_ eval_args
              rintro ⟨e, e_in⟩ ⟨v, v_in⟩ eval_e_eq_v
              rw [← eval_e_eq_v]
              obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
                obtain ⟨_, mem_ext, rfl, _⟩ := sim
                apply eval_ext [inbox]
                · simp_rw [List.mem_singleton]
                  intros x x_neq
                  simp_rw [AList.lookup_union, mem_ext _ x_neq]
                · rw [List.singleton_disjoint]
                  obtain ⟨-, wf, -⟩ := wf
                  specialize wf _ e_in
                  apply not_mem_of_fresh
                  assumption
              }
          · match mailbox with
            | none =>
              obtain ⟨rfl, rfl, rfl, rfl⟩ := sim
              assumption
            | some (_, inbox) =>
              rw [← lookup_Fₜ]
              obtain ⟨c, _, rfl⟩|⟨c, _, _, rfl⟩ := relatesTo_mailbox_shape sim
              <;> [ (obtain ⟨rfl, mem_ext, rfl, _, _, _, fifos_ext, fifos_ext', inbox_eq⟩ := sim; let vs' : List Value := [])
                  | (obtain ⟨rfl, mem_ext, rfl, _, _, _, v, _, fifos_ext, fifos_ext', inbox_eq⟩ := sim; let vs' := [v]) ]
              <;> {
                by_cases c_eq : chan.name = c
                · subst c
                  by_cases vs_eq : vs = vs'
                  · subst vs vs'
                    rw [inbox_eq, lookup_Fₜ]
                    rfl
                  · apply fifos_ext' _ vs_eq
                · apply fifos_ext _ c_eq
              }

  lemma GuardedPlusCal.Statement.strong_refinement.assign.{u}
    {ref} {mailbox : Option (Expression.{u} Typ × String)}
    {e : Expression.{u} Typ}
    (wf : match mailbox with | .none => True | .some ⟨_, inbox⟩ => ref.name ≠ inbox ∧ (∀ arg ∈ ref.args, ∀ idx ∈ arg, idx.FreshIn inbox) ∧ e.FreshIn inbox)
    {«Σ» Γ Ξ : Scope}
    (self_in_Ξ : "self" ∈ Ξ) (Γ_disj_Ξ : Disjoint Γ Ξ)
    (wellscoped : e.WellScoped («Σ» ∪ Γ ∪ Ξ) ∧ ref.name ∈ Γ ∧ ∀ arg ∈ ref.args, ∀ idx ∈ arg, idx.WellScoped («Σ» ∪ Γ ∪ Ξ)) :
      StrongRefinement (· ∼[mailbox] ·)
        ⟦@GuardedPlusCal.Statement.assign.{u} Typ _ ref e⟧*
        ⟦@GuardedPlusCal.Statement.assign Typ _ ref e⟧⊥
        ⟦@GuardedPlusCal.Statement.assign Typ _ ref e⟧∞
        ⟦@NetworkPlusCal.Statement.assign.{u} Typ _ ref e⟧*
        ⟦@NetworkPlusCal.Statement.assign Typ _ ref e⟧⊥
        ⟦@NetworkPlusCal.Statement.assign Typ _ ref e⟧∞ := by
    rw [NetworkPlusCal.Statement.div_empty]
    apply StrongRefinement.ofNonDiverging
    · rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ⟨Mₜ', Tₜ', Fₜ', lₜ'⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim sem_Sₜ
      left
      obtain ⟨⟨Mₜ', Fₜ'⟩, rfl, ⟨_, _, _, _, v, vss, eval_e_eq_v, eval_args, upd_mem, _, _|_, _|_, rfl⟩, _|_, rfl⟩ := sem_Sₜ
      match mailbox with
      | .none =>
        obtain ⟨rfl, rfl, rfl, rfl⟩ := sim
        sem_exists Mₛ ⤳ Mₜ', Tₛ, Fₛ
        4-7:  assumption
        trivial
      | .some ⟨_, inbox⟩ =>
        have ref_name_ne : ref.name ≠ inbox := by
          obtain ⟨_, _, _⟩ := wf
          assumption

        obtain ⟨_, c, rfl⟩|⟨_, _, c, _, rfl⟩ := relatesTo_mailbox_shape sim
        · obtain ⟨rfl, mem_ext, rfl, vs, inbox_eq, inbox_not_in_Tₛ, _, _, _⟩ := sim
          simp_rw [GuardedPlusCal.Memory.updateRef, Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_mem
          obtain ⟨v', lookup_Mₜ, v'', upd_mem, _|_⟩ := upd_mem
          sem_exists Mₛ ⤳ AList.insert ref.name v'' Mₛ, Tₛ, Fₛ
          · and_intros <;> try rfl
            · intros y y_ne_inbox
              by_cases y_eq : y = ref.name
              · subst y
                repeat rw [AList.lookup_insert]
              · repeat erw [AList.lookup_insert_ne y_eq]
                apply mem_ext
                assumption
            · exists vs
              and_intros <;> try trivial
              · rwa [AList.lookup_insert_ne (Ne.symm ref_name_ne)]
          · exact v
          · exact vss
          · rw [← eval_e_eq_v]
            apply eval_ext [inbox]
            · simp_rw [List.mem_singleton]
              intros x x_neq
              simp_rw [AList.lookup_union, mem_ext _ x_neq]
            · rw [List.singleton_disjoint]
              obtain ⟨_, _, _⟩ := wf
              apply not_mem_of_fresh
              assumption
              -- simp_rw [GuardedPlusCal.Statement.freeVars, GuardedPlusCal.Ref.freeVars, List.mem_append, not_or] at wf
              -- exact wf.right
          · rw [← List.forall₂_iff_forall₂_attach] at eval_args ⊢
            refine List.Forall₂.imp ?_ eval_args
            rintro ⟨arg, arg_in⟩ ⟨vs, vs_in⟩ h
            rw [← List.forall₂_iff_forall₂_attach] at h ⊢
            refine List.Forall₂.imp ?_ h
            rintro ⟨e, e_in⟩ ⟨v, v_in⟩ eval_e_eq_v
            rw [← eval_e_eq_v]
            apply eval_ext [inbox]
            · simp_rw [List.mem_singleton]
              intros x x_neq
              simp_rw [AList.lookup_union, mem_ext _ x_neq]
            · rw [List.singleton_disjoint]
              obtain ⟨-, wf, -⟩ := wf
              specialize wf _ arg_in _ e_in
              apply not_mem_of_fresh
              assumption
          · simp_rw [GuardedPlusCal.Memory.updateRef, Option.bind_eq_bind, Option.bind_eq_some_iff]
            refine ⟨v', ?_, v'', ?_, ?_⟩
            · rw [← lookup_Mₜ, mem_ext _ ref_name_ne]
            · assumption
            · rfl
          · assumption
        · obtain ⟨rfl, mem_ext, rfl, vs, inbox_eq, inbox_not_in_Tₛ, es, eval_self, _, _, _⟩ := sim
          simp_rw [GuardedPlusCal.Memory.updateRef, Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_mem
          obtain ⟨v', lookup_Mₜ, v'', upd_mem, _|_⟩ := upd_mem
          sem_exists Mₛ ⤳ AList.insert ref.name v'' Mₛ, Tₛ, Fₛ
          · and_intros <;> try rfl
            · intros y y_ne_inbox
              by_cases y_eq : y = ref.name
              · subst y
                repeat rw [AList.lookup_insert]
              · repeat erw [AList.lookup_insert_ne y_eq]
                apply mem_ext
                assumption
            · exists vs
              and_intros <;> try trivial
              · rwa [AList.lookup_insert_ne (Ne.symm ref_name_ne)]
              · refine ⟨es, ?_, ?_, ?_, ?_⟩
                · rw [← eval_self, eval_ext [ref.name]]
                  · intros x x_neq
                    rw [List.not_mem_singleton] at x_neq
                    rw [AList.lookup_union, AList.lookup_insert_ne x_neq, AList.lookup_union]
                  · obtain ⟨_, ref_name_in, _⟩ := wellscoped
                    unfold Expression.freeVars
                    rw [List.disjoint_singleton, List.not_mem_singleton]
                    apply Disjoint.forall_ne_finset Γ_disj_Ξ.symm <;> assumption
                · assumption
                · assumption
                · assumption
          · exact v
          · exact vss
          · rw [← eval_e_eq_v]
            apply eval_ext [inbox]
            · simp_rw [List.mem_singleton]
              intros x x_neq
              simp_rw [AList.lookup_union, mem_ext _ x_neq]
            · rw [List.singleton_disjoint]
              -- simp_rw [GuardedPlusCal.Statement.freeVars, GuardedPlusCal.Ref.freeVars, List.mem_append, not_or] at wf
              -- exact wf.right
              obtain ⟨_, _, _⟩ := wf
              apply not_mem_of_fresh
              assumption
          · rw [← List.forall₂_iff_forall₂_attach] at eval_args ⊢
            refine List.Forall₂.imp ?_ eval_args
            rintro ⟨arg, arg_in⟩ ⟨vs, vs_in⟩ h
            rw [← List.forall₂_iff_forall₂_attach] at h ⊢
            refine List.Forall₂.imp ?_ h
            rintro ⟨e, e_in⟩ ⟨v, v_in⟩ eval_e_eq_v
            rw [← eval_e_eq_v]
            apply eval_ext [inbox]
            · simp_rw [List.mem_singleton]
              intros x x_neq
              simp_rw [AList.lookup_union, mem_ext _ x_neq]
            · rw [List.singleton_disjoint]
              -- simp_rw [GuardedPlusCal.Statement.freeVars, GuardedPlusCal.Ref.freeVars, List.mem_append, List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and, not_exists, not_and] at wf
              -- apply wf.left.right <;> assumption
              obtain ⟨-, wf, -⟩ := wf
              specialize wf _ arg_in _ e_in
              apply not_mem_of_fresh
              assumption
          · simp_rw [GuardedPlusCal.Memory.updateRef, Option.bind_eq_bind, Option.bind_eq_some_iff]
            refine ⟨v', ?_, v'', ?_, ?_⟩
            · rw [← lookup_Mₜ, mem_ext _ ref_name_ne]
            · assumption
            · rfl
          · assumption
    · rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim ⟨rfl, ((h|h)|h)|h⟩
      · obtain ⟨_, _, _, h, _|_, rfl⟩ := h
        exists [], le_rfl
        constructor
        · exact relatesTo_eq_label sim
        · left; left; left
          match mailbox with
          | none =>
            obtain ⟨rfl, rfl, rfl, rfl⟩ := sim
            exists Mₛ, Tₛ, Fₛ
          | some (v, inbox) =>
            obtain ⟨_, -, -⟩ := wf
            obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
              obtain ⟨rfl, mem_eq, rfl, _⟩ := sim
              use Mₛ, Tₛ, Fₛ, ?_, rfl
              obtain h|h := h
              · left
                rw [← AList.lookup_eq_none, mem_eq]
                · rwa [← AList.lookup_eq_none] at h
                · assumption
              · right
                assumption
            }
      · obtain ⟨_, _, _, eval_e, _|_, rfl⟩ := h
        exists [], le_rfl
        constructor
        · exact relatesTo_eq_label sim
        · left; left; right
          exists Mₛ, Tₛ, Fₛ, ?_, ?_ <;> try rfl
          match mailbox with
          | none =>
            obtain ⟨rfl, rfl, rfl, rfl⟩ := sim
            assumption
          | some (v, inbox) =>
            rw [← eval_e]
            obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
              obtain ⟨rfl, mem_ext, rfl, _⟩ := sim
              apply eval_ext [inbox]
              · simp_rw [List.mem_singleton]
                intros x x_neq
                simp_rw [AList.lookup_union, mem_ext _ x_neq]
              · rw [List.singleton_disjoint]
                obtain ⟨_, _, _⟩ := wf
                apply not_mem_of_fresh
                assumption
            }
      · obtain ⟨arg, arg_in, e', e'_in, _, _, _, eval_e', _|_, rfl⟩ := h
        exists [], le_rfl
        constructor
        · exact relatesTo_eq_label sim
        · left; right
          exists arg, arg_in, e', e'_in, Mₛ, Tₛ, Fₛ, ?_, ?_ <;> try rfl
          match mailbox with
          | none =>
            obtain ⟨rfl, rfl, rfl, rfl⟩ := sim
            assumption
          | some (v, inbox) =>
            rw [← eval_e']
            obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
              obtain ⟨rfl, mem_ext, rfl, _⟩ := sim
              apply eval_ext [inbox]
              · simp_rw [List.mem_singleton]
                intros x x_neq
                simp_rw [AList.lookup_union, mem_ext _ x_neq]
              · rw [List.singleton_disjoint]
                obtain ⟨_, wf, _⟩ := wf
                apply not_mem_of_fresh
                apply wf <;> assumption
            }
      · obtain ⟨_, _, _, v, vss, eval_e_eq_v, eval_args, upd_none, _, _|_, rfl⟩ := h
        exists [], le_rfl
        constructor
        · exact relatesTo_eq_label sim
        · right
          match mailbox with
          | none =>
            obtain ⟨rfl, rfl, rfl, rfl⟩ := sim
            exists Mₛ, Tₛ, Fₛ, v, vss
          | some (v, inbox) =>
            obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
              obtain ⟨rfl, mem_ext, rfl, _⟩ := sim
              exists Mₛ, Tₛ, Fₛ, v, vss, ?_, ?_, ?_, ?_ <;> try trivial
              · rw [← eval_e_eq_v]
                apply eval_ext [inbox]
                · simp_rw [List.mem_singleton]
                  intros x x_neq
                  simp_rw [AList.lookup_union, mem_ext _ x_neq]
                · rw [List.singleton_disjoint]
                  obtain ⟨_, _, _⟩ := wf
                  apply not_mem_of_fresh
                  assumption
              · rw [← List.forall₂_iff_forall₂_attach] at eval_args ⊢
                refine List.Forall₂.imp ?_ eval_args
                rintro ⟨arg, arg_in⟩ ⟨vs, vs_in⟩ h
                rw [← List.forall₂_iff_forall₂_attach] at h ⊢
                refine List.Forall₂.imp ?_ h
                rintro ⟨e, e_in⟩ ⟨v, v_in⟩ eval_e_eq_v
                rw [← eval_e_eq_v]
                apply eval_ext [inbox]
                · simp_rw [List.mem_singleton]
                  intros x x_neq
                  simp_rw [AList.lookup_union, mem_ext _ x_neq]
                · rw [List.singleton_disjoint]
                  obtain ⟨-, wf, -⟩ := wf
                  specialize wf _ arg_in _ e_in
                  apply not_mem_of_fresh
                  assumption
              · simp_rw [GuardedPlusCal.Memory.updateRef, Option.bind_eq_bind, Option.bind_eq_none_iff] at upd_none ⊢
                intros v' lookup_Mₛ_eq_v' v'' upd
                rw [mem_ext] at lookup_Mₛ_eq_v'
                · cases upd_none v' lookup_Mₛ_eq_v' v'' upd
                · exact wf.1
            }

  set_option linter.unnecessarySeqFocus false in
  theorem GuardedPlusCal.Statement.strong_refinement (S : GuardedPlusCal.Statement Typ (Expression Typ) false false)
    {mailbox : Option (Expression Typ × String)}
    {«Σ» Γ Δ Ξ : Scope}
    (self_in_Ξ : "self" ∈ Ξ) (Γ_disj_Ξ : Disjoint Γ Ξ)
    (wellscoped : match S with
      | .skip => True
      | .print e => Expression.WellScoped e («Σ» ∪ Γ ∪ Ξ)
      | .assert e => Expression.WellScoped e («Σ» ∪ Γ ∪ Ξ)
      | .send chan e =>
        Expression.WellScoped e («Σ» ∪ Γ ∪ Ξ) ∧ chan.name ∈ Δ ∧ (∀ idx ∈ chan.args, Expression.WellScoped idx («Σ» ∪ Γ ∪ Ξ))
      | .multicast chan bs e =>
        chan ∈ Δ ∧ (∀ r ∈ bs, Expression.WellScoped r.2.2.2 («Σ» ∪ Γ ∪ Ξ)) ∧ (∀ r ∈ bs, r.1 ∉ «Σ» ∧ r.1 ∉ Γ ∧ r.1 ∉ Ξ) ∧
        Expression.WellScoped e («Σ» ∪ Γ ∪ Ξ ∪ (bs.map Prod.fst).toFinset)
      | .assign ref e =>
        Expression.WellScoped e («Σ» ∪ Γ ∪ Ξ) ∧ ref.name ∈ Γ ∧ (∀ arg ∈ ref.args, ∀ idx ∈ arg, Expression.WellScoped idx («Σ» ∪ Γ ∪ Ξ)))
    (wf : match mailbox with | .none => True | .some ⟨_, inbox⟩ => S.FreshIn Expression.FreshIn inbox) :
      StrongRefinement (· ∼[mailbox] ·) ⟦S⟧* ⟦S⟧⊥ ⟦S⟧∞
        ⟦match_source S with
        | .skip, pos => NetworkPlusCal.Statement.skip @@ pos
        | .print e, pos => NetworkPlusCal.Statement.print e @@ pos
        | .assert e, pos => NetworkPlusCal.Statement.assert e @@ pos
        | .send chan e, pos => NetworkPlusCal.Statement.send chan e @@ pos
        | .multicast chan bs e, pos => NetworkPlusCal.Statement.multicast chan bs e @@ pos
        | .assign ref e, pos => NetworkPlusCal.Statement.assign ref e @@ pos⟧*
        ⟦match_source S with
        | .skip, pos => NetworkPlusCal.Statement.skip @@ pos
        | .print e, pos => NetworkPlusCal.Statement.print e @@ pos
        | .assert e, pos => NetworkPlusCal.Statement.assert e @@ pos
        | .send chan e, pos => NetworkPlusCal.Statement.send chan e @@ pos
        | .multicast chan bs e, pos => NetworkPlusCal.Statement.multicast chan bs e @@ pos
        | .assign ref e, pos => NetworkPlusCal.Statement.assign ref e @@ pos⟧⊥
        ⟦match_source S with
        | .skip, pos => NetworkPlusCal.Statement.skip @@ pos
        | .print e, pos => NetworkPlusCal.Statement.print e @@ pos
        | .assert e, pos => NetworkPlusCal.Statement.assert e @@ pos
        | .send chan e, pos => NetworkPlusCal.Statement.send chan e @@ pos
        | .multicast chan bs e, pos => NetworkPlusCal.Statement.multicast chan bs e @@ pos
        | .assign ref e, pos => NetworkPlusCal.Statement.assign ref e @@ pos⟧∞ := by
    cases S with
    | skip => apply strong_refinement.skip
    | print e => apply strong_refinement.print <;> assumption
    | assert e => apply strong_refinement.assert <;> assumption
    | send chan e => apply strong_refinement.send <;> assumption
    -- TODO: should be almost as painful as send
    | multicast chan filter e => sorry
    | assign ref e => apply strong_refinement.assign <;> assumption

  theorem doUpdate_eq_doUpdate {v₂ v' : Value} {vss : List (List Value)} :
      GuardedPlusCal.Memory.updateRef.doUpdate v₂ v' vss = TypedSetTheory.eval.doUpdate v' (Sum.inl <$> vss) v₂ := by
    induction vss generalizing v' with
    | nil =>
      unfold GuardedPlusCal.Memory.updateRef.doUpdate TypedSetTheory.eval.doUpdate
      rw [List.map_eq_map, List.map_nil]
      -- split <;> try contradiction
      -- split <;> try contradiction
      -- rfl
    | cons vs vss IH =>
      unfold GuardedPlusCal.Memory.updateRef.doUpdate TypedSetTheory.eval.doUpdate
      rw [List.map_eq_map, List.map_cons]
      split <;> try contradiction
      · injections
        subst_eqs
        extract_lets +lift tup
        dsimp
        split using h | h <;> try contradiction
        · unfold tup at h
          conv_rhs => enter [2]; apply h
          dsimp
          rw [IH]
          congr
        · split using h' <;> try contradiction
          · cases h _ _ h'
          · rfl
      · split using _ | _ | h <;> try contradiction
        · injections
        · injections
          subst_eqs
          cases h _ _ _ rfl rfl
        · rfl

  theorem NetworkPlusCal.Statement.reorder_let {r} {e e': Expression Typ} {name} {τ : Typ} {«=|∈»}
    (h₁ : e'.FreshIn name) (h₂ : r.name ∉ TypedSetTheory.prims) (h₃ : ∀ arg ∈ r.args, ∀ idx ∈ arg, idx.FreshIn name) (h₄ : r.name ≠ name) :
      ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧* ∘ᵣ₂ ⟦NetworkPlusCal.Statement.let name τ «=|∈» e⟧* =
      ⟦NetworkPlusCal.Statement.let name τ «=|∈» ((↿e.replace) <| r.substOf e')⟧* ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧* := by
    ext ⟨⟨Ma, Ta, Fa, _⟩, ε, ⟨Mc, Tc, Fc, _⟩⟩
    constructor
    · rintro ⟨⟨Mb, Tb, Fb, _⟩, ε₁, ε₂, ⟨⟨_, _, _⟩, rfl, red_assign, _|_, rfl⟩, ⟨⟨_, _, _⟩, -, red_let, _|_, rfl⟩, rfl⟩
      obtain ⟨_, _, _, _, v₂, vss, eval_e', eval_args_vss, upd_Ma_eq_Mc, r_name_not_in, _|_, _|_, rfl⟩ := red_assign
      obtain ⟨_, _, _, v, eval_e, lookup_name, _|_, rfl, h⟩ := red_let
      split at h using vs | _ | v' <;> try contradiction
      · obtain ⟨v', v'_in, _, _, _|_⟩ := h
        sem_compn Ma ⤳ Ma ⤳ Mc, Ta ⤳ AList.insert name v' Ta ⤳ AList.insert name v' Ta, Fa ⤳ Fa ⤳ Fa
        · exact .set vs
        · simp_rw [GuardedPlusCal.Memory.updateRef, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at upd_Ma_eq_Mc
          obtain ⟨v', lookup_Mₜ, v'', upd_Ma_eq_Mc, _|_⟩ := upd_Ma_eq_Mc
          change TypedSetTheory.eval _ (Expression.replace e _ _) = _
          rw [← eval_e, TypedSetTheory.eval_subst (v := v'')]
          · unfold GuardedPlusCal.Ref.substOf
            split_ifs with args_empty
            · rw [List.isEmpty_iff] at args_empty
              rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
              subst vss

              have : ∀ k, ((Ta ∪ Ma).insert r.name v'').lookup k = (Ta ∪ Ma.insert r.name v'').lookup k := by
                intro k
                rw [AList.union_insert_ext_of_not_mem ‹_› k]

              rw [TypedSetTheory.eval_mem_ext this]
            · apply TypedSetTheory.eval_mem_ext
              intros x
              rw [AList.union_insert_ext_of_not_mem r_name_not_in x]
          · unfold GuardedPlusCal.Ref.substOf
            split_ifs <;> assumption
          · unfold GuardedPlusCal.Ref.substOf
            split_ifs with args_empty
            · rw [List.isEmpty_iff] at args_empty
              rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
              subst vss

              unfold GuardedPlusCal.Memory.updateRef.doUpdate at upd_Ma_eq_Mc
              -- split at upd_Ma_eq_Mc <;> try contradiction
              injections
              subst v''
              assumption
            · -- TODO: extract_goal?
              rw [← upd_Ma_eq_Mc]
              clear args_empty lookup_name upd_Ma_eq_Mc
              generalize r.args = ess at eval_args_vss ⊢

              unfold TypedSetTheory.eval

              have eval_r_name_eq : TypedSetTheory.eval (Ta ∪ Ma) (Expression.var r.name r.τ) = .some v' := by
                unfold TypedSetTheory.eval
                conv_lhs => apply dite_cond_eq_false (eq_false h₂)
                rwa [AList.lookup_union_right r_name_not_in]

              conv_lhs =>
                enter [2, fn, 1, 1, x, 4, upd, e, property, 1, 1, x, 5, es, property', 2]
                apply List.traverse_attach_eq_traverse _

              conv_lhs => enter [2, fn, 1]; change ?x

              have : ?x = .some [(Sum.inl <$> vss, v₂)] := by
                rw [List.attach_singleton, List.traverse_singleton]
                dsimp
                simp_rw [Option.map_eq_some_iff, Option.bind_eq_some_iff]
                refine ⟨_, ⟨_, ?_, _, eval_e', rfl⟩, rfl⟩
                simp_rw [List.attach_map, List.traverse_map, Function.comp_def]
                conv_lhs =>
                  apply List.traverse_attach_eq_traverse' λ x ↦ Option.map Sum.inl (List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) x)

                induction eval_args_vss with
                | nil => rfl
                | @cons es vs _ _ eval_es_vs _ IH =>
                  erw [List.traverse_cons', List.map_cons, IH, seq_pure, Functor.map_map, Functor.map_map]

                  have : List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) es = .some vs := by
                    induction eval_es_vs with
                    | nil => rfl
                    | @cons _ _ _ _ h _ IH =>
                      erw [List.traverse_cons', IH, seq_pure, Functor.map_map, h, map_pure]
                      rfl

                  erw [this, map_pure]
                  rfl

              rw [eval_r_name_eq, this]
              simp_rw [Option.bind_eq_bind]
              change List.foldlM (λ fn x ↦ TypedSetTheory.eval.doUpdate fn x.1 x.2) v' [(Sum.inl <$> vss, v₂)] =
                     GuardedPlusCal.Memory.updateRef.doUpdate v₂ v' vss
              simp_rw [List.foldlM_cons, List.foldlM_nil, bind_pure]
              symm
              apply doUpdate_eq_doUpdate
        · unfold GuardedPlusCal.Memory.updateRef at upd_Ma_eq_Mc
          simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Ma_eq_Mc
          obtain ⟨_, _, _, _, _|_⟩ := upd_Ma_eq_Mc
          rw [AList.lookup_union, AList.lookup_insert_ne h₄.symm, Option.orElse_eq_none] at lookup_name
          rwa [AList.lookup_union, Option.orElse_eq_none]
        · exists _, v'_in
        · exact v₂
        · exact vss
        · rw [← eval_e']
          apply eval_ext [name]
          · intros x x_not_in
            rw [List.not_mem_singleton] at x_not_in
            rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            apply h₁
        · rw [← List.forall₂_iff_forall₂_attach] at eval_args_vss ⊢
          apply eval_args_vss.imp
          rintro ⟨arg, arg_in⟩ ⟨vs, vs_in⟩ eval_arg_vs
          rw [← List.forall₂_iff_forall₂_attach] at eval_arg_vs ⊢
          apply eval_arg_vs.imp
          rintro ⟨idx, idx_in⟩ ⟨v, v_in⟩ eval_arg_v
          rw [← eval_arg_v]
          apply eval_ext [name]
          · intros x x_not_in
            rw [List.not_mem_singleton] at x_not_in
            rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            exact h₃ _ arg_in _ idx_in
        · assumption
        · simp_all
      · obtain ⟨_, _, _|_⟩ := h
        sem_compn Ma ⤳ Ma ⤳ Mc, Ta ⤳ AList.insert name v Ta ⤳ AList.insert name v Ta, Fa ⤳ Fa ⤳ Fa
        -- · exact v
        · simp_rw [GuardedPlusCal.Memory.updateRef, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at upd_Ma_eq_Mc
          obtain ⟨v', lookup_Mₜ, v'', upd_Ma_eq_Mc, _|_⟩ := upd_Ma_eq_Mc
          change TypedSetTheory.eval _ (Expression.replace e _ _) = _
          rw [← eval_e, TypedSetTheory.eval_subst (v := v'')]
          · unfold GuardedPlusCal.Ref.substOf
            split_ifs with args_empty
            · rw [List.isEmpty_iff] at args_empty
              rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
              subst vss

              have : ∀ k, ((Ta ∪ Ma).insert r.name v'').lookup k = (Ta ∪ Ma.insert r.name v'').lookup k := by
                intro k
                rw [AList.union_insert_ext_of_not_mem ‹_› k]

              rw [TypedSetTheory.eval_mem_ext this]
            · apply TypedSetTheory.eval_mem_ext
              intros x
              rw [AList.union_insert_ext_of_not_mem r_name_not_in x]
          · unfold GuardedPlusCal.Ref.substOf
            split_ifs <;> assumption
          · unfold GuardedPlusCal.Ref.substOf
            split_ifs with args_empty
            · rw [List.isEmpty_iff] at args_empty
              rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
              subst vss

              unfold GuardedPlusCal.Memory.updateRef.doUpdate at upd_Ma_eq_Mc
              -- split at upd_Ma_eq_Mc <;> try contradiction
              injections
              subst v''
              assumption
            · -- TODO: extract goal?
              rw [← upd_Ma_eq_Mc]
              clear args_empty lookup_name upd_Ma_eq_Mc
              generalize r.args = ess at eval_args_vss ⊢

              unfold TypedSetTheory.eval

              have eval_r_name_eq : TypedSetTheory.eval (Ta ∪ Ma) (Expression.var r.name r.τ) = .some v' := by
                unfold TypedSetTheory.eval
                conv_lhs => apply dite_cond_eq_false (eq_false h₂)
                rwa [AList.lookup_union_right r_name_not_in]

              conv_lhs =>
                enter [2, fn, 1, 1, x, 4, upd, e, property, 1, 1, x, 5, es, property', 2]
                apply List.traverse_attach_eq_traverse _

              conv_lhs => enter [2, fn, 1]; change ?y

              have : ?y = .some [(Sum.inl <$> vss, v₂)] := by
                rw [List.attach_singleton, List.traverse_singleton]
                dsimp
                simp_rw [Option.map_eq_some_iff, Option.bind_eq_some_iff]
                refine ⟨_, ⟨_, ?_, _, eval_e', rfl⟩, rfl⟩
                simp_rw [List.attach_map, List.traverse_map, Function.comp_def]
                conv_lhs =>
                  apply List.traverse_attach_eq_traverse' λ x ↦ Option.map Sum.inl (List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) x)

                induction eval_args_vss with
                | nil => rfl
                | @cons es vs _ _ eval_es_vs _ IH =>
                  erw [List.traverse_cons', List.map_cons, IH, seq_pure, Functor.map_map, Functor.map_map]

                  have : List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) es = .some vs := by
                    induction eval_es_vs with
                    | nil => rfl
                    | @cons _ _ _ _ h _ IH =>
                      erw [List.traverse_cons', IH, seq_pure, Functor.map_map, h, map_pure]
                      rfl

                  erw [this, map_pure]
                  rfl

              rw [eval_r_name_eq, this]
              simp_rw [Option.bind_eq_bind]
              change List.foldlM (λ fn x ↦ TypedSetTheory.eval.doUpdate fn x.1 x.2) v' [(Sum.inl <$> vss, v₂)] =
                     GuardedPlusCal.Memory.updateRef.doUpdate v₂ v' vss
              simp_rw [List.foldlM_cons, List.foldlM_nil, bind_pure]
              symm
              apply doUpdate_eq_doUpdate
        · unfold GuardedPlusCal.Memory.updateRef at upd_Ma_eq_Mc
          simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Ma_eq_Mc
          obtain ⟨_, _, _, _, _|_⟩ := upd_Ma_eq_Mc
          rw [AList.lookup_union, AList.lookup_insert_ne h₄.symm, Option.orElse_eq_none] at lookup_name
          rwa [AList.lookup_union, Option.orElse_eq_none]
        -- · rfl
        · exact v₂
        · exact vss
        · rw [← eval_e']
          apply eval_ext [name]
          · intros x x_not_in
            rw [List.not_mem_singleton] at x_not_in
            rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            apply h₁
        · rw [← List.forall₂_iff_forall₂_attach] at eval_args_vss ⊢
          apply eval_args_vss.imp
          rintro ⟨arg, arg_in⟩ ⟨vs, vs_in⟩ eval_arg_vs
          rw [← List.forall₂_iff_forall₂_attach] at eval_arg_vs ⊢
          apply eval_arg_vs.imp
          rintro ⟨idx, idx_in⟩ ⟨v, v_in⟩ eval_arg_v
          rw [← eval_arg_v]
          apply eval_ext [name]
          · intros x x_not_in
            rw [List.not_mem_singleton] at x_not_in
            rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            exact h₃ _ arg_in _ idx_in
        · assumption
        · simp_all
    · rintro ⟨⟨Mb, Tb, Fb, _⟩, ε₁, ε₂, ⟨⟨_, _, _⟩, rfl, red_let, _|_, rfl⟩, ⟨⟨_, _, _⟩, -, red_assign, _|_, rfl⟩, rfl⟩
      obtain ⟨_, _, _, v₁, eval_e, lookup_name, _|_, rfl, h⟩ := red_let
      obtain ⟨_, _, _, _, v₂, vss, eval_e', eval_args_vss, upd_Ma_eq_Mc, r_name_not_in, _|_, _|_, rfl⟩ := red_assign
      split at h using vs | _ | v' <;> try contradiction
      · obtain ⟨v', v'_in, _, _, _|_⟩ := h
        sem_compn Ma ⤳ Mc ⤳ Mc, Ta ⤳ Ta ⤳ AList.insert name v' Ta, Fa ⤳ Fa ⤳ Fa
        · exact v₂
        · exact vss
        · rw [← eval_e']
          apply eval_ext [name]
          · intros x x_not_in
            rw [List.not_mem_singleton] at x_not_in
            rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            apply h₁
        · rw [← List.forall₂_iff_forall₂_attach] at eval_args_vss ⊢
          apply eval_args_vss.imp
          rintro ⟨arg, arg_in⟩ ⟨vs, vs_in⟩ eval_arg_vs
          rw [← List.forall₂_iff_forall₂_attach] at eval_arg_vs ⊢
          apply eval_arg_vs.imp
          rintro ⟨idx, idx_in⟩ ⟨v, v_in⟩ eval_arg_v
          rw [← eval_arg_v]
          apply eval_ext [name]
          · intros x x_not_in
            rw [List.not_mem_singleton] at x_not_in
            rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            exact h₃ _ arg_in _ idx_in
        · assumption
        · simp_all
        · exact .set vs
        · simp_rw [GuardedPlusCal.Memory.updateRef, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at upd_Ma_eq_Mc
          obtain ⟨v', lookup_Mₜ, v'', upd_Ma_eq_Mc, _|_⟩ := upd_Ma_eq_Mc
          change TypedSetTheory.eval _ (Expression.replace e _ _) = _ at eval_e
          rw [← eval_e, TypedSetTheory.eval_subst (v := v'')]
          · unfold GuardedPlusCal.Ref.substOf
            rw [← AList.lookup_eq_none, AList.lookup_insert_eq_none, AList.lookup_eq_none] at r_name_not_in
            split_ifs with args_empty
            · rw [List.isEmpty_iff] at args_empty
              rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
              subst vss

              have : ∀ k, ((Ta ∪ Ma).insert r.name v'').lookup k = (Ta ∪ Ma.insert r.name v'').lookup k := by
                intro k
                rw [AList.union_insert_ext_of_not_mem r_name_not_in.right k]

              rw [TypedSetTheory.eval_mem_ext this]
            · symm
              apply TypedSetTheory.eval_mem_ext
              intros x
              rw [AList.union_insert_ext_of_not_mem r_name_not_in.right x]
          · unfold GuardedPlusCal.Ref.substOf
            split_ifs <;> assumption
          · unfold GuardedPlusCal.Ref.substOf
            split_ifs with args_empty
            · rw [List.isEmpty_iff] at args_empty
              rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
              subst vss

              unfold GuardedPlusCal.Memory.updateRef.doUpdate at upd_Ma_eq_Mc
              -- split at upd_Ma_eq_Mc <;> try contradiction
              injections
              subst v''

              rw [← eval_e', ← AList.insert_union]
              apply eval_ext [name]
              · intros x x_not_in
                rw [List.not_mem_singleton] at x_not_in
                rw [AList.lookup_insert_ne x_not_in]
              · rw [List.singleton_disjoint]
                apply not_mem_of_fresh
                assumption
            · -- TODO: extract goal?
              replace eval_e' : TypedSetTheory.eval (Ta ∪ Ma) e' = some v₂ := by
                rw [← eval_e']
                apply eval_ext [name]
                · intros x x_not_in
                  rw [List.not_mem_singleton] at x_not_in
                  rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
                · rw [List.singleton_disjoint]
                  apply not_mem_of_fresh
                  assumption

              replace eval_args_vss : List.Forall₂ (List.Forall₂ λ e v ↦ TypedSetTheory.eval (Ta ∪ Ma) e = some v) r.args vss := by
                rw [← List.forall₂_iff_forall₂_attach] at eval_args_vss ⊢
                apply eval_args_vss.imp
                rintro ⟨arg, arg_in⟩ ⟨vs, vs_in⟩ eval_arg_vs
                rw [← List.forall₂_iff_forall₂_attach] at eval_arg_vs ⊢
                apply eval_arg_vs.imp
                rintro ⟨idx, idx_in⟩ ⟨v, v_in⟩ eval_arg_v
                rw [← eval_arg_v]
                apply eval_ext [name]
                · intros x x_not_in
                  rw [List.not_mem_singleton] at x_not_in
                  rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
                · rw [List.singleton_disjoint]
                  apply not_mem_of_fresh
                  exact h₃ _ arg_in _ idx_in

              rw [← AList.lookup_eq_none, AList.lookup_insert_eq_none, AList.lookup_eq_none] at r_name_not_in
              rw [← upd_Ma_eq_Mc]
              clear args_empty lookup_name upd_Ma_eq_Mc
              generalize r.args = ess at eval_args_vss ⊢

              unfold TypedSetTheory.eval

              have eval_r_name_eq : TypedSetTheory.eval (Ta ∪ Ma) (Expression.var r.name r.τ) = .some v' := by
                unfold TypedSetTheory.eval
                conv_lhs => apply dite_cond_eq_false (eq_false h₂)
                rwa [AList.lookup_union_right r_name_not_in.right]

              conv_lhs =>
                enter [2, fn, 1, 1, x, 4, upd, e, property, 1, 1, x, 5, es, property', 2]
                apply List.traverse_attach_eq_traverse _

              conv_lhs => enter [2, fn, 1]; change ?w

              have : ?w = .some [(Sum.inl <$> vss, v₂)] := by
                rw [List.attach_singleton, List.traverse_singleton]
                dsimp
                simp_rw [Option.map_eq_some_iff, Option.bind_eq_some_iff]
                refine ⟨_, ⟨_, ?_, _, eval_e', rfl⟩, rfl⟩
                simp_rw [List.attach_map, List.traverse_map, Function.comp_def]
                conv_lhs =>
                  apply List.traverse_attach_eq_traverse' λ x ↦ Option.map Sum.inl (List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) x)

                induction eval_args_vss with
                | nil => rfl
                | @cons es vs _ _ eval_es_vs _ IH =>
                  erw [List.traverse_cons', List.map_cons, IH, seq_pure, Functor.map_map, Functor.map_map]

                  have : List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) es = .some vs := by
                    induction eval_es_vs with
                    | nil => rfl
                    | @cons _ _ _ _ h _ IH =>
                      erw [List.traverse_cons', IH, seq_pure, Functor.map_map, h, map_pure]
                      rfl

                  erw [this, map_pure]
                  rfl

              rw [eval_r_name_eq, this]
              simp_rw [Option.bind_eq_bind]
              change List.foldlM (λ fn x ↦ TypedSetTheory.eval.doUpdate fn x.1 x.2) v' [(Sum.inl <$> vss, v₂)] =
                     GuardedPlusCal.Memory.updateRef.doUpdate v₂ v' vss
              simp_rw [List.foldlM_cons, List.foldlM_nil, bind_pure]
              symm
              apply doUpdate_eq_doUpdate
        · unfold GuardedPlusCal.Memory.updateRef at upd_Ma_eq_Mc
          simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Ma_eq_Mc
          obtain ⟨_, _, _, _, _|_⟩ := upd_Ma_eq_Mc
          rw [AList.lookup_union, Option.orElse_eq_none] at lookup_name
          rwa [AList.lookup_union, AList.lookup_insert_ne h₄.symm, Option.orElse_eq_none]
        · exists _, v'_in
      · obtain ⟨_, _, _|_⟩ := h
        sem_compn Ma ⤳ Mc ⤳ Mc, Ta ⤳ Ta ⤳ Ta.insert name v₁, Fa ⤳ Fa ⤳ Fa
        · exact v₂
        · exact vss
        · rw [← eval_e']
          apply eval_ext [name]
          · intros x x_not_in
            rw [List.not_mem_singleton] at x_not_in
            rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            apply h₁
        · rw [← List.forall₂_iff_forall₂_attach] at eval_args_vss ⊢
          apply eval_args_vss.imp
          rintro ⟨arg, arg_in⟩ ⟨vs, vs_in⟩ eval_arg_vs
          rw [← List.forall₂_iff_forall₂_attach] at eval_arg_vs ⊢
          apply eval_arg_vs.imp
          rintro ⟨idx, idx_in⟩ ⟨v, v_in⟩ eval_arg_v
          rw [← eval_arg_v]
          apply eval_ext [name]
          · intros x x_not_in
            rw [List.not_mem_singleton] at x_not_in
            rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            exact h₃ _ arg_in _ idx_in
        · rw [← upd_Ma_eq_Mc]
        · rwa [← AList.lookup_eq_none, AList.lookup_insert_ne h₄, AList.lookup_eq_none] at r_name_not_in
        -- · exact v₁
        · simp_rw [GuardedPlusCal.Memory.updateRef, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at upd_Ma_eq_Mc
          obtain ⟨v', lookup_Mₜ, v'', upd_Ma_eq_Mc, _|_⟩ := upd_Ma_eq_Mc
          change TypedSetTheory.eval _ (Expression.replace e _ _) = _ at eval_e
          rw [← eval_e, TypedSetTheory.eval_subst (v := v'')]
          · unfold GuardedPlusCal.Ref.substOf
            rw [← AList.lookup_eq_none, AList.lookup_insert_eq_none, AList.lookup_eq_none] at r_name_not_in
            split_ifs with args_empty
            · rw [List.isEmpty_iff] at args_empty
              rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
              subst vss

              have : ∀ k, ((Ta ∪ Ma).insert r.name v'').lookup k = (Ta ∪ Ma.insert r.name v'').lookup k := by
                intro k
                rw [AList.union_insert_ext_of_not_mem r_name_not_in.right k]

              rw [TypedSetTheory.eval_mem_ext this]
            · symm
              apply TypedSetTheory.eval_mem_ext
              intros x
              rw [AList.union_insert_ext_of_not_mem r_name_not_in.right x]
          · unfold GuardedPlusCal.Ref.substOf
            split_ifs <;> assumption
          · unfold GuardedPlusCal.Ref.substOf
            split_ifs with args_empty
            · rw [List.isEmpty_iff] at args_empty
              rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
              subst vss

              unfold GuardedPlusCal.Memory.updateRef.doUpdate at upd_Ma_eq_Mc
              -- split at upd_Ma_eq_Mc <;> try contradiction
              injections
              subst v''

              rw [← eval_e', ← AList.insert_union]
              apply eval_ext [name]
              · intros x x_not_in
                rw [List.not_mem_singleton] at x_not_in
                rw [AList.lookup_insert_ne x_not_in]
              · rw [List.singleton_disjoint]
                apply not_mem_of_fresh
                assumption
            · -- TODO: extract goal?
              replace eval_e' : TypedSetTheory.eval (Ta ∪ Ma) e' = some v₂ := by
                rw [← eval_e']
                apply eval_ext [name]
                · intros x x_not_in
                  rw [List.not_mem_singleton] at x_not_in
                  rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
                · rw [List.singleton_disjoint]
                  apply not_mem_of_fresh
                  assumption

              replace eval_args_vss : List.Forall₂ (List.Forall₂ λ e v ↦ TypedSetTheory.eval (Ta ∪ Ma) e = some v) r.args vss := by
                rw [← List.forall₂_iff_forall₂_attach] at eval_args_vss ⊢
                apply eval_args_vss.imp
                rintro ⟨arg, arg_in⟩ ⟨vs, vs_in⟩ eval_arg_vs
                rw [← List.forall₂_iff_forall₂_attach] at eval_arg_vs ⊢
                apply eval_arg_vs.imp
                rintro ⟨idx, idx_in⟩ ⟨v, v_in⟩ eval_arg_v
                rw [← eval_arg_v]
                apply eval_ext [name]
                · intros x x_not_in
                  rw [List.not_mem_singleton] at x_not_in
                  rw [← AList.insert_union, AList.lookup_insert_ne x_not_in]
                · rw [List.singleton_disjoint]
                  apply not_mem_of_fresh
                  exact h₃ _ arg_in _ idx_in

              rw [← AList.lookup_eq_none, AList.lookup_insert_eq_none, AList.lookup_eq_none] at r_name_not_in
              rw [← upd_Ma_eq_Mc]
              clear args_empty lookup_name upd_Ma_eq_Mc
              generalize r.args = ess at eval_args_vss ⊢

              unfold TypedSetTheory.eval

              have eval_r_name_eq : TypedSetTheory.eval (Ta ∪ Ma) (Expression.var r.name r.τ) = .some v' := by
                unfold TypedSetTheory.eval
                conv_lhs => apply dite_cond_eq_false (eq_false h₂)
                rwa [AList.lookup_union_right r_name_not_in.right]

              conv_lhs =>
                enter [2, fn, 1, 1, x, 4, upd, e, property, 1, 1, x, 5, es, property', 2]
                apply List.traverse_attach_eq_traverse _

              conv_lhs => enter [2, fn, 1]; change ?z

              have : ?z = .some [(Sum.inl <$> vss, v₂)] := by
                rw [List.attach_singleton, List.traverse_singleton]
                dsimp
                simp_rw [Option.map_eq_some_iff, Option.bind_eq_some_iff]
                refine ⟨_, ⟨_, ?_, _, eval_e', rfl⟩, rfl⟩
                simp_rw [List.attach_map, List.traverse_map, Function.comp_def]
                conv_lhs =>
                  apply List.traverse_attach_eq_traverse' λ x ↦ Option.map Sum.inl (List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) x)

                induction eval_args_vss with
                | nil => rfl
                | @cons es vs _ _ eval_es_vs _ IH =>
                  erw [List.traverse_cons', List.map_cons, IH, seq_pure, Functor.map_map, Functor.map_map]

                  have : List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) es = .some vs := by
                    induction eval_es_vs with
                    | nil => rfl
                    | @cons _ _ _ _ h _ IH =>
                      erw [List.traverse_cons', IH, seq_pure, Functor.map_map, h, map_pure]
                      rfl

                  erw [this, map_pure]
                  rfl

              rw [eval_r_name_eq, this]
              simp_rw [Option.bind_eq_bind]
              change List.foldlM (λ fn x ↦ TypedSetTheory.eval.doUpdate fn x.1 x.2) v' [(Sum.inl <$> vss, v₂)] =
                     GuardedPlusCal.Memory.updateRef.doUpdate v₂ v' vss
              simp_rw [List.foldlM_cons, List.foldlM_nil, bind_pure]
              symm
              apply doUpdate_eq_doUpdate
        · unfold GuardedPlusCal.Memory.updateRef at upd_Ma_eq_Mc
          simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Ma_eq_Mc
          obtain ⟨_, _, _, _, _|_⟩ := upd_Ma_eq_Mc
          rw [AList.lookup_union, Option.orElse_eq_none] at lookup_name
          rwa [AList.lookup_union, AList.lookup_insert_ne h₄.symm, Option.orElse_eq_none]
        -- · rfl

  theorem NetworkPlusCal.Statement.reorder_await {r} {e e': Expression.{0} Typ} (h' : r.name ∉ TypedSetTheory.prims.{0}) :
      ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧* ∘ᵣ₂ ⟦NetworkPlusCal.Statement.await (Typ := Typ) e⟧* =
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) ((↿e.replace) <| r.substOf e')⟧* ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧* := by
    ext ⟨⟨Ma, Ta, Fa, _⟩, ε, ⟨Mc, Tc, Fc, _⟩⟩
    constructor
    · rintro ⟨⟨Mb, Tb, Fb, _⟩, ε₁, ε₂, ⟨⟨⟩, rfl, red_assign, _|_, rfl⟩, ⟨⟨⟩, -, red_await, _|_, rfl⟩, rfl⟩
      obtain ⟨_, _, _, _, v, vss, eval_e', eval_args_vss, upd_Ma_eq_Mc, r_name_not_in, _|_, _|_, rfl⟩ := red_assign
      obtain ⟨_, _, _, _|_, _|_, eval_e, _|_, rfl⟩ := red_await
      sem_compn Ma ⤳ Ma ⤳ Mc, Ta ⤳ Ta ⤳ Ta, Fa ⤳ Fa ⤳ Fa
      · change TypedSetTheory.eval _ (Expression.replace e (GuardedPlusCal.Ref.substOf r e').1 (GuardedPlusCal.Ref.substOf r e').2) = _
        simp_rw [GuardedPlusCal.Memory.updateRef, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at upd_Ma_eq_Mc
        obtain ⟨v', lookup_Mₜ, v'', upd_Ma_eq_Mc, _|_⟩ := upd_Ma_eq_Mc
        rw [← eval_e, TypedSetTheory.eval_subst (v := v'')]
        · unfold GuardedPlusCal.Ref.substOf
          split_ifs with args_empty
          · rw [List.isEmpty_iff] at args_empty
            rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
            subst vss

            have : ∀ k, ((Ta ∪ Ma).insert r.name v'').lookup k = (Ta ∪ Ma.insert r.name v'').lookup k := by
              intro k
              rw [AList.union_insert_ext_of_not_mem ‹_› k]

            rw [TypedSetTheory.eval_mem_ext this]
          · apply TypedSetTheory.eval_mem_ext
            intros x
            rw [AList.union_insert_ext_of_not_mem r_name_not_in x]
        · unfold GuardedPlusCal.Ref.substOf
          split_ifs <;> assumption
        · -- from eval_e'?
          unfold GuardedPlusCal.Ref.substOf
          split_ifs with args_empty
          · rw [List.isEmpty_iff] at args_empty
            rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
            subst vss

            unfold GuardedPlusCal.Memory.updateRef.doUpdate at upd_Ma_eq_Mc
            -- split at upd_Ma_eq_Mc <;> try contradiction
            injections
            subst v''
            assumption
          · -- TODO: extract goal?
            rw [← upd_Ma_eq_Mc]
            clear args_empty upd_Ma_eq_Mc
            generalize r.args = ess at eval_args_vss ⊢

            unfold TypedSetTheory.eval

            have eval_r_name_eq : TypedSetTheory.eval (Ta ∪ Ma) (Expression.var r.name r.τ) = .some v' := by
              unfold TypedSetTheory.eval
              conv_lhs => apply dite_cond_eq_false (eq_false h')
              rwa [AList.lookup_union_right r_name_not_in]

            conv_lhs =>
              enter [2, fn, 1, 1, x, 4, upd, e, property, 1, 1, x, 5, es, property', 2]
              apply List.traverse_attach_eq_traverse _

            conv_lhs => enter [2, fn, 1]; change ?w

            have : ?w = .some [(Sum.inl <$> vss, v)] := by
              rw [List.attach_singleton, List.traverse_singleton]
              dsimp
              simp_rw [Option.map_eq_some_iff, Option.bind_eq_some_iff]
              refine ⟨_, ⟨_, ?_, _, eval_e', rfl⟩, rfl⟩
              simp_rw [List.attach_map, List.traverse_map, Function.comp_def]
              conv_lhs =>
                apply List.traverse_attach_eq_traverse' λ x ↦ Option.map Sum.inl (List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) x)

              induction eval_args_vss with
              | nil => rfl
              | @cons es vs _ _ eval_es_vs _ IH =>
                erw [List.traverse_cons', List.map_cons, IH, seq_pure, Functor.map_map, Functor.map_map]

                have : List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) es = .some vs := by
                  induction eval_es_vs with
                  | nil => rfl
                  | @cons _ _ _ _ h _ IH =>
                    erw [List.traverse_cons', IH, seq_pure, Functor.map_map, h, map_pure]
                    rfl

                erw [this, map_pure]
                rfl

            rw [eval_r_name_eq, this]
            simp_rw [Option.bind_eq_bind]
            change List.foldlM (λ fn x ↦ TypedSetTheory.eval.doUpdate fn x.1 x.2) v' [(Sum.inl <$> vss, v)] =
                    GuardedPlusCal.Memory.updateRef.doUpdate v v' vss
            simp_rw [List.foldlM_cons, List.foldlM_nil, bind_pure]
            symm
            apply doUpdate_eq_doUpdate
      · exact v
      · exact vss
      · assumption
      · assumption
      · assumption
      · assumption
    · rintro ⟨⟨Mb, Tb, Fb, _⟩, ε₁, ε₂, ⟨⟨⟩, rfl, red_await, _|_, rfl⟩, ⟨⟨⟩, -, red_assign, _|_, rfl⟩, rfl⟩
      obtain ⟨_, _, _, _|_, _|_, eval_e, rfl⟩ := red_await
      obtain ⟨_, _, _, _, v, vss, eval_e', eval_args_vss, upd_Ma_eq_Mc, r_name_not_in, _|_, _|_, rfl⟩ := red_assign
      sem_compn Ma ⤳ Mc ⤳ Mc, Ta ⤳ Ta ⤳ Ta, Fa ⤳ Fa ⤳ Fa
      · exact v
      · exact vss
      · assumption
      · assumption
      · assumption
      · assumption
      · rw [← eval_e]
        symm
        simp_rw [GuardedPlusCal.Memory.updateRef, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at upd_Ma_eq_Mc
        obtain ⟨v', lookup_Mₜ, v'', upd_Ma_eq_Mc, _|_⟩ := upd_Ma_eq_Mc
        change TypedSetTheory.eval _ (Expression.replace e _ _) = _
        rw [TypedSetTheory.eval_subst (v := v'')]
        · unfold GuardedPlusCal.Ref.substOf
          split_ifs with args_empty
          · rw [List.isEmpty_iff] at args_empty
            rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
            subst vss

            have : ∀ k, ((Ta ∪ Ma).insert r.name v'').lookup k = (Ta ∪ Ma.insert r.name v'').lookup k := by
              intro k
              rw [AList.union_insert_ext_of_not_mem ‹_› k]

            rw [TypedSetTheory.eval_mem_ext this]
          · apply TypedSetTheory.eval_mem_ext
            intros x
            rw [AList.union_insert_ext_of_not_mem r_name_not_in x]
        · unfold GuardedPlusCal.Ref.substOf
          split_ifs <;> exact h'
        · unfold GuardedPlusCal.Ref.substOf
          split_ifs with args_empty
          · rw [List.isEmpty_iff] at args_empty
            rw [args_empty, List.forall₂_nil_left_iff] at eval_args_vss
            subst vss

            unfold GuardedPlusCal.Memory.updateRef.doUpdate at upd_Ma_eq_Mc
            -- split at upd_Ma_eq_Mc <;> try contradiction
            injections
            subst v''
            assumption
          · -- TODO: extract goal?
            rw [← upd_Ma_eq_Mc]
            clear args_empty upd_Ma_eq_Mc
            generalize r.args = ess at eval_args_vss ⊢

            unfold TypedSetTheory.eval

            have eval_r_name_eq : TypedSetTheory.eval (Ta ∪ Ma) (Expression.var r.name r.τ) = .some v' := by
              unfold TypedSetTheory.eval
              conv_lhs => apply dite_cond_eq_false (eq_false h')
              rwa [AList.lookup_union_right r_name_not_in]

            conv_lhs =>
              enter [2, fn, 1, 1, x, 4, upd, e, property, 1, 1, x, 5, es, property', 2]
              apply List.traverse_attach_eq_traverse _

            conv_lhs => enter [2, fn, 1]; change ?y

            have : ?y = .some [(Sum.inl <$> vss, v)] := by
              rw [List.attach_singleton, List.traverse_singleton]
              dsimp
              simp_rw [Option.map_eq_some_iff, Option.bind_eq_some_iff]
              refine ⟨_, ⟨_, ?_, _, eval_e', rfl⟩, rfl⟩
              simp_rw [List.attach_map, List.traverse_map, Function.comp_def]
              conv_lhs =>
                apply List.traverse_attach_eq_traverse' λ x ↦ Option.map Sum.inl (List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) x)

              induction eval_args_vss with
              | nil => rfl
              | @cons es vs _ _ eval_es_vs _ IH =>
                erw [List.traverse_cons', List.map_cons, IH, seq_pure, Functor.map_map, Functor.map_map]

                have : List.traverse (TypedSetTheory.eval (Ta ∪ Ma)) es = .some vs := by
                  induction eval_es_vs with
                  | nil => rfl
                  | @cons _ _ _ _ h _ IH =>
                    erw [List.traverse_cons', IH, seq_pure, Functor.map_map, h, map_pure]
                    rfl

                erw [this, map_pure]
                rfl

            rw [eval_r_name_eq, this]
            simp_rw [Option.bind_eq_bind]
            change List.foldlM (λ fn x ↦ TypedSetTheory.eval.doUpdate fn x.1 x.2) v' [(Sum.inl <$> vss, v)] =
                    GuardedPlusCal.Memory.updateRef.doUpdate v v' vss
            simp_rw [List.foldlM_cons, List.foldlM_nil, bind_pure]
            symm
            apply doUpdate_eq_doUpdate

  theorem GuardedPlusCal.Memory.updateRef.doUpdate_empty_args.{u} {v v' : Value.{u}} : GuardedPlusCal.Memory.updateRef.doUpdate v v' [] = pure v := by
    unfold GuardedPlusCal.Memory.updateRef.doUpdate
    simp

  theorem eval.doUpdate_empty_args.{u} {v v' : Value.{u}} :
      TypedSetTheory.eval.doUpdate v [] v' = pure v' := by
    unfold TypedSetTheory.eval.doUpdate
    simp

  theorem NetworkPlusCal.Statement.reorder_await'.aux_neval_except.{u}
    {r : GuardedPlusCal.Ref.{u} Typ (Expression Typ)} {e' : Expression Typ}
    (M : TypedSetTheory.Memory.{u}) (neval_e' : TypedSetTheory.eval M e' = none) :
      TypedSetTheory.eval M (Expression.except (Expression.var r.name r.τ) [(List.map Sum.inl r.args, e')]) = none := by
    unfold TypedSetTheory.eval
    simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff, List.attach_singleton,
             List.traverse_singleton, Option.map_eq_map, Option.map_eq_some_iff, Option.bind_eq_some_iff]
    rintro v₁ eval_var vss ⟨⟨arg, v'⟩, ⟨_, eval_args, _, eval_e', _|_⟩, rfl⟩
    rw [neval_e'] at eval_e'
    contradiction

  theorem GuardedPlusCal.Memory.updateRef.doUpdate_cons.{u} {v v' v'' : Value.{u}} {vs vss}
    (h : GuardedPlusCal.Memory.updateRef.doUpdate v v'' (vs :: vss) = some v') :
      let tup := match (motive := _ → Value.{u}) vs with | [v] => v | _ => Value.tuple vs
      ∃ maps, v'' = .fn maps ∧ match (motive := _ → Prop) maps.find? λ ⟨k, _⟩ ↦ k == tup with
        | .some ⟨_, v''⟩ =>
          ∃ v''', GuardedPlusCal.Memory.updateRef.doUpdate v v'' vss = some v''' ∧
            v' = .fn (maps.replaceF λ ⟨k, _⟩ ↦ if k == tup then .some ⟨tup, v'''⟩ else .none)
        | none => v' = v'' := by
    unfold GuardedPlusCal.Memory.updateRef.doUpdate at h
    split at h using _ | maps _ _ h' <;> try contradiction
    exists maps, rfl
    dsimp at h ⊢
    split at h using heq' | heq'
    · simp_rw [Option.bind_eq_some_iff] at h
      obtain ⟨v'', upd_eq, _|_⟩ := h
      injection h' with h₁ h₂
      subst h₁ h₂
      conv in List.find? _ _ => apply heq'
      dsimp
      exists v''
    · erw [← Prod.forall (p := λ x ↦ _ = some x → False), ← Option.eq_none_iff_forall_ne_some] at heq'
      cases h
      injection h' with h₁ h₂
      subst h₁ h₂
      conv in List.find? _ _ => apply heq'

  theorem NetworkPlusCal.Statement.reorder_await'.aux_eval_except.{u}
    {r : GuardedPlusCal.Ref.{u} Typ (Expression Typ)} {e' : Expression Typ}
    {M T : TypedSetTheory.Memory} {v v' : Value} {vss : List (List Value)}
    (r_name_not_prim : r.name ∉ TypedSetTheory.prims.{u})
    (eval_args : List.traverse (List.traverse (TypedSetTheory.eval (T ∪ M))) r.args = some vss)
    (r_name_in_M : r.name ∈ M) (r_name_not_in_T : r.name ∉ T)
    (eval_e' : TypedSetTheory.eval (T ∪ M) e' = some v)
    (upd_eq : GuardedPlusCal.Memory.updateRef.doUpdate v (AList.get M r.name r_name_in_M) vss = some v') :
      TypedSetTheory.eval.{u, u} (T ∪ M) (Expression.except (Expression.var r.name r.τ) [(Sum.inl <$> r.args, e')]) = some v' := by
    simp_rw [List.traverse_eq_some] at eval_args
    generalize r.args = args at *
    generalize v''_eq : AList.get M r.name r_name_in_M = v'' at *

    have eval_r_name_eq : TypedSetTheory.eval (T ∪ M) (Expression.var r.name r.τ) = some v'' := by
      unfold TypedSetTheory.eval
      rw [← v''_eq, dif_neg r_name_not_prim, AList.lookup_union_right r_name_not_in_T,
          AList.lookup_eq_some_get_of_mem r_name_in_M]

    unfold TypedSetTheory.eval
    rw [eval_r_name_eq]

    clear v''_eq eval_r_name_eq

    induction eval_args generalizing v' v'' with
    | nil =>
      rw [GuardedPlusCal.Memory.updateRef.doUpdate_empty_args] at upd_eq
      cases upd_eq
      simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff, List.attach_singleton,
               List.traverse_singleton, Option.map_eq_map, Option.map_eq_some_iff,
               Option.bind_eq_some_iff, List.map_eq_map, List.map_nil, List.attach_nil,
               List.traverse_nil']
      exists v'', rfl
      exists [([], v)], ⟨([], v), ⟨[], rfl, v, ?_, rfl⟩, ?_⟩ <;> try trivial
      -- simp_rw [List.foldlM_cons, List.foldlM_nil, bind_pure, eval.doUpdate_empty_args]
      -- rfl
    | @cons arg vs args vss eval_arg eval_args IH =>
      apply GuardedPlusCal.Memory.updateRef.doUpdate_cons at upd_eq
      obtain ⟨maps, rfl, upd_eq⟩ := upd_eq
      dsimp at upd_eq
      split at upd_eq using heq | tup_not_in_dom
      · obtain ⟨v''', upd_eq, rfl⟩ := upd_eq
        specialize IH _ upd_eq
        simp_rw [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff, List.traverse_eq_some,
                 List.attach_cons, List.attach_nil, List.map_nil, List.forall₂_cons_left_iff, List.forall₂_nil_left_iff] at IH
        obtain ⟨_, ⟨x, _, eval_args', rfl, rfl⟩, upd_eq⟩ := IH
        simp_rw [Option.bind_eq_some_iff, List.map_eq_map, List.attach_map, List.traverse_map, Function.comp_def,
                 List.traverse_attach_eq_traverse'] at eval_args'
        obtain ⟨_, h₁, v', eval_e', _|_⟩ := eval_args'
        rw [List.traverse_attach_eq_traverse' (f := λ x ↦ Sum.inl <$> List.traverse (TypedSetTheory.eval (T ∪ M)) x),
            List.traverse_eq_some] at h₁
        simp_rw [List.foldlM_cons, List.foldlM_nil, bind_pure] at upd_eq

        simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff, List.attach_cons, List.attach_nil, List.map_nil,
                 List.traverse_singleton, Option.map_eq_map, Option.map_eq_some_iff, Option.bind_eq_some_iff]

        exists .fn maps, rfl, [(Sum.inl <$> (vs :: vss), v')], ⟨(_, v'), ⟨_, ?_, v', eval_e', rfl⟩, rfl⟩
        · simp_rw [List.traverse_eq_some, List.traverse_attach_eq_traverse', List.map_eq_map, List.attach_map,
                   List.attach_cons, List.forall₂_map_left_iff, List.forall₂_map_right_iff, Option.map_eq_some_iff,
                   List.traverse_eq_some]
          apply List.Forall₂.cons
          · exists vs
          · conv =>
              enter [1, a, c]
              conv => enter [1, d, 2]; rw [Sum.inl.injEq]
              rw [exists_eq_right]
            unfold List.attach
            simp_rw [List.forall₂_map_left_iff, List.forall₂_attachWith]
            assumption
        · simp_rw [List.foldlM_cons, List.foldlM_nil, bind_pure, List.map_eq_map, List.map_cons]
          unfold TypedSetTheory.eval.doUpdate
          dsimp
          conv => enter [1, 2]; apply heq
          dsimp
          simp_rw [Option.bind_eq_some_iff]
          exists v''', ?_ <;> try trivial
          convert upd_eq

          simp_rw [← List.traverse_eq_some, List.traverse_fmap] at eval_args h₁
          rw [eval_args, Option.map_eq_map, Option.map_some] at h₁
          cases h₁
          rfl
      · subst v'
        simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]
        exists .fn maps, ?_, [(Sum.inl <$> (vs :: vss), v)], ?_
        · simp_rw [List.traverse_eq_some, Option.bind_eq_some_iff, List.traverse_eq_some]

          rw [List.attach_cons, List.attach_nil, List.map_nil, List.forall₂_singleton]
          exists Sum.inl <$> (vs :: vss), ?_, v, ?_ <;> try trivial
          erw [List.map_eq_map, List.map_cons, List.map_eq_map, List.map_cons, List.attach_cons]
          apply List.Forall₂.cons
          · rw [← List.traverse_eq_some] at eval_arg
            dsimp
            erw [List.traverse_attach_eq_traverse', eval_arg]
            rfl
          · -- almost `eval_args`
            rw [List.attach_map, List.map_map, Function.comp_def, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
            dsimp
            simp_rw [List.traverse_attach_eq_traverse', Option.map_eq_some_iff, List.traverse_eq_some]
            conv =>
              enter [1, a, c]
              conv => enter [1, d, 2]; rw [Sum.inl.injEq]
              rw [exists_eq_right]
            erwa [List.forall₂_attachWith]
        · simp_rw [List.foldlM_cons, List.foldlM_nil, bind_pure, List.map_eq_map, List.map_cons]
          unfold TypedSetTheory.eval.doUpdate
          dsimp
          conv in List.find? _ _ => apply tup_not_in_dom

  theorem NetworkPlusCal.Statement.reorder_await'.{u}
    {r : GuardedPlusCal.Ref Typ (Expression Typ)}
    {e e' : Expression.{0} Typ}
    (h' : r.name ∉ TypedSetTheory.prims.{u}) :
      ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧⊥ ∪
        ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧* ∘ᵣ₁ ⟦NetworkPlusCal.Statement.await (Typ := Typ) e⟧⊥ ⊇
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) ((↿e.replace) <| r.substOf e')⟧⊥ ∪
        ⟦NetworkPlusCal.Statement.await (Typ := Typ) ((↿e.replace) <| r.substOf e')⟧* ∘ᵣ₁ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧⊥ := by
    have generic_reorder_await' {e'' : Expression.{0} Typ}
      (neval_imp_neval : ∀ M, M ⊢ e' ↯ → M ⊢ e'' ↯)
      (eval_imp_eval : ∀ M T {v v' vss}, List.traverse (List.traverse (TypedSetTheory.eval (T ∪ M))) r.args = some vss
          → (r_name_in_M : r.name ∈ M) → r.name ∉ T → T ∪ M ⊢ e' ⇒ v → GuardedPlusCal.Memory.updateRef.doUpdate v (AList.get M r.name r_name_in_M) vss = some v'
          → T ∪ M ⊢ e'' ⇒ v') :
        ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧⊥
        ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧*
          ∘ᵣ₁ ⟦NetworkPlusCal.Statement.await (Typ := Typ) e⟧⊥ ⊇
        ⟦NetworkPlusCal.Statement.await (Typ := Typ) (e.replace r.name e'')⟧⊥
        ∪ ⟦NetworkPlusCal.Statement.await (Typ := Typ) (e.replace r.name e'')⟧*
          ∘ᵣ₁ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧⊥ := by as_aux_lemma =>
      rintro ⟨⟨Ma, Ta, Fa, _⟩, _⟩ (⟨rfl, abort_await⟩|⟨⟨Mb, Tb, Fb, _⟩, ε₁, ε₂, red_await, abort_assign, rfl⟩)
      · obtain abort_await|abort_await := abort_await
        · obtain ⟨_, _, _, neval_e_subst, _|_, rfl⟩ := abort_await
          by_cases r_name_in_fv_e : r.name ∈ e.freeVars
          · by_cases eval_e' : ∃ v, Ta ∪ Ma ⊢ e' ⇒ v
            · obtain ⟨v, eval_e'⟩ := eval_e'
              by_cases r_name_in_mem : r.name ∈ Ma ∧ r.name ∉ Ta
              · obtain ⟨r_name_in_Ma, r_name_not_in_Ta⟩ := r_name_in_mem

                by_cases eval_args : ∃ vss, List.traverse (List.traverse (TypedSetTheory.eval (Ta ∪ Ma))) r.args = some vss
                · obtain ⟨vss, eval_args⟩ := eval_args
                  by_cases upd : ∃ v', GuardedPlusCal.Memory.updateRef.doUpdate v (AList.get Ma r.name r_name_in_Ma) vss = some v'
                  · obtain ⟨v', upd_eq⟩ := upd
                    let Mb := Ma.insert r.name v'
                    have upd_eq : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v = some Mb := by
                      unfold GuardedPlusCal.Memory.updateRef
                      simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]

                      exists Ma.get r.name r_name_in_Ma, ?_, v', ?_ <;> try rfl
                      · apply AList.lookup_eq_some_get_of_mem
                      · assumption

                    right
                    exists ⟨Mb, Ta, Fa, none⟩, [], [], ?_, ?_ <;> try trivial
                    · sem_redn Ma ⤳ Mb, Ta, Fa
                      · exact v
                      · exact vss
                      · assumption
                      · simp_rw [List.traverse_eq_some] at eval_args
                        assumption
                      · assumption
                      · assumption
                    · exists rfl
                      left
                      exists Mb, Ta, Fa, ?_, ?_ <;> try rfl
                      rw [← neval_e_subst, TypedSetTheory.eval_subst h']
                      · apply TypedSetTheory.eval_mem_ext
                        intro x
                        rw [AList.union_insert_ext_of_not_mem r_name_not_in_Ta]
                      · apply eval_imp_eval <;> assumption
                  · push_neg at upd
                    rw [← Option.eq_none_iff_forall_ne_some] at upd

                    replace upd : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v = none := by
                      unfold GuardedPlusCal.Memory.updateRef
                      simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff]

                      intros v₁ lookup_r_name_Ma v₂ upd'
                      rw [AList.lookup_eq_some_get_of_mem r_name_in_Ma] at lookup_r_name_Ma
                      cases lookup_r_name_Ma
                      rw [upd] at upd'
                      contradiction

                    left
                    exists rfl
                    right
                    exists Ma, Ta, Fa, v, vss, ?_, ?_, ?_ <;> try trivial
                    simp_rw [List.traverse_eq_some] at eval_args
                    assumption
                · push_neg at eval_args
                  rw [← Option.eq_none_iff_forall_ne_some] at eval_args
                  simp_rw [List.traverse_eq_none] at eval_args
                  left
                  exists rfl
                  left; right
                  obtain ⟨a, a_in, e, e_in, neval_e⟩ := eval_args
                  exists _, a_in, _, e_in, Ma, Ta, Fa
              · rw [not_and_or, not_not] at r_name_in_mem
                left
                exists rfl
                left; left; left
                exists Ma, Ta, Fa
            · push_neg at eval_e'

              replace eval_e' : Ta ∪ Ma ⊢ e' ↯ := by rwa [Option.eq_none_iff_forall_ne_some]

              left
              exists rfl
              left; left; right
              exists Ma, Ta, Fa
          · rw [TypedSetTheory.eval_subst_of_not_mem_fv h' r_name_in_fv_e] at neval_e_subst
            by_cases eval_e' : ∃ v, Ta ∪ Ma ⊢ e' ⇒ v
            · obtain ⟨v, eval_e'⟩ := eval_e'
              by_cases r_name_in_mem : r.name ∈ Ma ∧ r.name ∉ Ta
              · obtain ⟨r_name_in_Ma, r_name_not_in_Ta⟩ := r_name_in_mem
                by_cases eval_args : ∃ vss, List.traverse (List.traverse (TypedSetTheory.eval (Ta ∪ Ma))) r.args = some vss
                · obtain ⟨vss, eval_args⟩ := eval_args
                  by_cases upd : ∃ v', GuardedPlusCal.Memory.updateRef.doUpdate v (AList.get Ma r.name r_name_in_Ma) vss = some v'
                  · obtain ⟨v', upd_eq⟩ := upd

                    let Mb := Ma.insert r.name v'
                    have upd_eq : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v = some Mb := by
                      unfold GuardedPlusCal.Memory.updateRef
                      simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]

                      exists Ma.get r.name r_name_in_Ma, ?_, v', ?_ <;> try rfl
                      · apply AList.lookup_eq_some_get_of_mem
                      · assumption

                    right
                    exists ⟨Mb, Ta, Fa, none⟩, [], [], ?_, ?_ <;> try trivial
                    · sem_redn Ma ⤳ Mb, Ta, Fa
                      · exact v
                      · exact vss
                      · assumption
                      · simp_rw [List.traverse_eq_some] at eval_args
                        assumption
                      · assumption
                      · assumption
                    · exists rfl
                      left
                      exists Mb, Ta, Fa, ?_, ?_ <;> try rfl
                      rw [← neval_e_subst]
                      apply eval_ext [r.name]
                      · intros x x_neq
                        rw [List.not_mem_singleton] at x_neq
                        rw [AList.union_insert_ext_of_not_mem r_name_not_in_Ta x, AList.lookup_insert_ne x_neq]
                      · rwa [List.singleton_disjoint]
                  · push_neg at upd
                    rw [← Option.eq_none_iff_forall_ne_some] at upd

                    replace upd : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v = none := by
                      unfold GuardedPlusCal.Memory.updateRef
                      simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff]

                      intros v₁ lookup_r_name_Ma v₂ upd'
                      rw [AList.lookup_eq_some_get_of_mem r_name_in_Ma] at lookup_r_name_Ma
                      cases lookup_r_name_Ma
                      rw [upd] at upd'
                      contradiction

                    left
                    exists rfl
                    right
                    exists Ma, Ta, Fa, v, vss, ?_, ?_, ?_ <;> try trivial
                    simp_rw [List.traverse_eq_some] at eval_args
                    assumption
                · push_neg at eval_args
                  rw [← Option.eq_none_iff_forall_ne_some] at eval_args
                  simp_rw [List.traverse_eq_none] at eval_args
                  left
                  exists rfl
                  left; right
                  obtain ⟨a, a_in, e, e_in, neval_e⟩ := eval_args
                  exists _, a_in, _, e_in, Ma, Ta, Fa
              · rw [not_and_or, not_not] at r_name_in_mem
                left
                exists rfl
                left; left; left
                exists Ma, Ta, Fa
            · push_neg at eval_e'

              replace eval_e' : Ta ∪ Ma ⊢ e' ↯ := by rwa [Option.eq_none_iff_forall_ne_some]

              left
              exists rfl
              left; left; right
              exists Ma, Ta, Fa
        · obtain ⟨_, _, _, v, v_not_bool, eval_e_subst, _|_, rfl⟩ := abort_await
          by_cases eval_e' : ∃ v, Ta ∪ Ma ⊢ e' ⇒ v
          · obtain ⟨v', eval_e'⟩ := eval_e'
            by_cases r_name_in_mem : r.name ∈ Ma ∧ r.name ∉ Ta
            · obtain ⟨r_name_in_Ma, r_name_not_in_Ta⟩ := r_name_in_mem
              by_cases eval_args : ∃ vss, List.traverse (List.traverse (TypedSetTheory.eval (Ta ∪ Ma))) r.args = some vss
              · obtain ⟨vss, eval_args⟩ := eval_args
                by_cases upd : ∃ v'', GuardedPlusCal.Memory.updateRef.doUpdate v' (AList.get Ma r.name r_name_in_Ma) vss = some v''
                · obtain ⟨v'', upd_eq'⟩ := upd

                  let Mb := Ma.insert r.name v''
                  have upd_eq : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v' = some Mb := by
                    unfold GuardedPlusCal.Memory.updateRef
                    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]

                    exists Ma.get r.name r_name_in_Ma, ?_, v'', ?_ <;> try rfl
                    · apply AList.lookup_eq_some_get_of_mem
                    · assumption

                  right
                  exists ⟨Mb, Ta, Fa, none⟩, [], [], ?_, ?_ <;> try trivial
                  · sem_redn Ma ⤳ Mb, Ta, Fa
                    · exact v'
                    · exact vss
                    · assumption
                    · simp_rw [List.traverse_eq_some] at eval_args
                      assumption
                    · assumption
                    · assumption
                  · exists rfl
                    right
                    exists Mb, Ta, Fa, v, v_not_bool, ?_, ?_ <;> try trivial
                    rw [← eval_e_subst, TypedSetTheory.eval_subst h']
                    · apply TypedSetTheory.eval_mem_ext
                      intros x
                      rw [AList.union_insert_ext_of_not_mem r_name_not_in_Ta]
                    · apply eval_imp_eval Ma Ta <;> try assumption
                · push_neg at upd
                  rw [← Option.eq_none_iff_forall_ne_some] at upd

                  replace upd : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v' = none := by
                    unfold GuardedPlusCal.Memory.updateRef
                    simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff]

                    intros v₁ lookup_r_name_Ma v₂ upd'
                    rw [AList.lookup_eq_some_get_of_mem r_name_in_Ma] at lookup_r_name_Ma
                    cases lookup_r_name_Ma
                    rw [upd] at upd'
                    contradiction

                  left
                  exists rfl
                  right
                  exists Ma, Ta, Fa, v', vss, ?_, ?_, ?_ <;> try trivial
                  simp_rw [List.traverse_eq_some] at eval_args
                  assumption
              · push_neg at eval_args
                rw [← Option.eq_none_iff_forall_ne_some] at eval_args
                simp_rw [List.traverse_eq_none] at eval_args
                left
                exists rfl
                left; right
                obtain ⟨a, a_in, e, e_in, neval_e⟩ := eval_args
                exists _, a_in, _, e_in, Ma, Ta, Fa
            · rw [not_and_or, not_not] at r_name_in_mem
              left
              exists rfl
              left; left; left
              exists Ma, Ta, Fa
          · push_neg at eval_e'

            replace eval_e' : Ta ∪ Ma ⊢ e' ↯ := by rwa [Option.eq_none_iff_forall_ne_some]

            left
            exists rfl
            left; left; right
            exists Ma, Ta, Fa
      · obtain ⟨⟨_, _, _⟩, rfl, ⟨_, _, _, _|_, _|_, eval_e, rfl⟩, _|_, rfl⟩ := red_await
        obtain ⟨-, ((abort_assign|abort_assign)|abort_assign)|abort_assign⟩ := abort_assign
        · obtain ⟨_, _, _, r_unassignable, _|_, rfl⟩ := abort_assign
          left
          exists rfl
          left; left; left
          exists Ma, Ta, Fa
        · by_cases r_name_in_fv_e : r.name ∈ e.freeVars
          · obtain ⟨_, _, _, neval_e', _|_, rfl⟩ := abort_assign
            rw [TypedSetTheory.neval_subst_of_mem_fv_of_neval r_name_in_fv_e] at eval_e
            · contradiction
            · apply neval_imp_neval
              assumption
          · left
            exists rfl
            left; left; right
            exact abort_assign
        · left
          exists rfl
          left; right
          exact abort_assign
        · left
          exists rfl
          right
          exact abort_assign

    unfold GuardedPlusCal.Ref.substOf
    split_ifs with args_empty <;> apply generic_reorder_await'
    · exact λ _ ↦ id
    · intros M T v v' vss eval_args _ _ eval_e' upd_eq
      rw [List.nil_of_isEmpty args_empty, List.traverse_nil'] at eval_args
      cases eval_args
      rw [GuardedPlusCal.Memory.updateRef.doUpdate_empty_args] at upd_eq
      cases upd_eq
      assumption
    · exact NetworkPlusCal.Statement.reorder_await'.aux_neval_except
    · exact λ M T v v' vss ↦ NetworkPlusCal.Statement.reorder_await'.aux_eval_except h'

  theorem NetworkPlusCal.Statement.sem_await_congr.{u} {e₁ e₂ : Expression.{u} Typ} (h : ∀ M : TypedSetTheory.Memory.{u}, TypedSetTheory.eval M e₁ = TypedSetTheory.eval M e₂) :
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) e₁⟧* = ⟦NetworkPlusCal.Statement.await (Typ := Typ) e₂⟧* := by
    ext ⟨⟨Ma, Ta, Fa, _⟩, _, ⟨Mb, Tb, Fb, _⟩⟩
    constructor
    · rintro ⟨⟨⟩, rfl, ⟨_, _, _, _|_, _|_, eval_e₁, rfl⟩, _|_, rfl⟩
      rw [h (Ta ∪ Ma)] at eval_e₁
      sem_redn Ma, Ta, Fa
      assumption
    · rintro ⟨⟨⟩, rfl, ⟨_, _, _, _|_, _|_, eval_e₂, rfl⟩, _|_, rfl⟩
      rw [← h (Ta ∪ Ma)] at eval_e₂
      sem_redn Ma, Ta, Fa
      assumption

  /-- A slightly weaker version of `NetworkPlusCal.Statement.sem_await_congr`. -/
  theorem NetworkPlusCal.Statement.sem_await_congr'.{u} {e₁ e₂ : Expression.{u} Typ} (h : ∀ M : TypedSetTheory.Memory.{u}, M ⊢ e₁ ⇒ .bool true ↔ M ⊢ e₂ ⇒ .bool true) :
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) e₁⟧* = ⟦NetworkPlusCal.Statement.await (Typ := Typ) e₂⟧* := by
    ext ⟨⟨Ma, Ta, Fa, _⟩, _, ⟨Mb, Tb, Fb, _⟩⟩
    iff_rintro ⟨⟨⟩, rfl, ⟨_, _, _, _|_, _|_, eval_e₁, rfl⟩, _|_, rfl⟩ ⟨⟨⟩, rfl, ⟨_, _, _, _|_, _|_, eval_e₂, rfl⟩, _|_, rfl⟩
    · rw [h (Ta ∪ Ma)] at eval_e₁
      sem_redn Ma, Ta, Fa
      assumption
    · rw [← h (Ta ∪ Ma)] at eval_e₂
      sem_redn Ma, Ta, Fa
      assumption

  theorem NetworkPlusCal.Statement.sem_await_of_imp.{u} {e₁ e₂ : Expression.{u} Typ} (h : ∀ M : TypedSetTheory.Memory.{u}, M ⊢ e₁ ⇒ .bool true → M ⊢ e₂ ⇒ .bool true) :
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) e₁⟧* ⊆ ⟦NetworkPlusCal.Statement.await (Typ := Typ) e₂⟧* := by
    rintro ⟨⟨Ma, Ta, Fa, _⟩, _, ⟨Mb, Tb, Fb, _⟩⟩ ⟨⟨⟩, rfl, ⟨_, _, _, _|_, _|_, eval_e₁, rfl⟩, _|_, rfl⟩
    apply h (Ta ∪ Ma) at eval_e₁
    sem_redn Ma, Ta, Fa
    assumption

  theorem NetworkPlusCal.Statement.abort_await_congr.{u} {e₁ e₂ : Expression.{u} Typ}
    (h₂ : ∀ M : TypedSetTheory.Memory.{u}, TypedSetTheory.eval M e₁ = TypedSetTheory.eval M e₂) :
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) e₁⟧⊥ = ⟦NetworkPlusCal.Statement.await (Typ := Typ) e₂⟧⊥ := by
    ext ⟨⟨Ma, Ta, Fa, _⟩, _⟩
    constructor
    · rintro ⟨rfl, ⟨_, _, _, eval_e₁, _|_, rfl⟩|⟨_, _, _, v, v_not_bool, eval_e₁, _|_, rfl⟩⟩
      · rw [h₂] at eval_e₁
        exists rfl
        left
        exists Ma, Ta, Fa
      · rw [h₂] at eval_e₁
        exists rfl
        right
        exists Ma, Ta, Fa, v
    · rintro ⟨rfl, ⟨_, _, _, eval_e₂, _|_, rfl⟩|⟨_, _, _, v, v_not_bool, eval_e₂, _|_, rfl⟩⟩
      · rw [← h₂] at eval_e₂
        exists rfl
        left
        exists Ma, Ta, Fa
      · rw [← h₂] at eval_e₂
        exists rfl
        right
        exists Ma, Ta, Fa, v

  theorem NetworkPlusCal.Statement.abort_await_of_imp.{u} {e₁ e₂ : Expression.{u} Typ}
    (h₂ : ∀ (M : TypedSetTheory.Memory.{u}) v, (∀ b, v ≠ .some (.bool b)) → TypedSetTheory.eval M e₁ = v → TypedSetTheory.eval M e₂ = v) :
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) e₁⟧⊥ ⊆ ⟦NetworkPlusCal.Statement.await (Typ := Typ) e₂⟧⊥ := by
    rintro ⟨⟨Ma, Ta, Fa, _⟩, _⟩ ⟨rfl, ⟨_, _, _, eval_e₁, _|_, rfl⟩|⟨_, _, _, v, v_not_bool, eval_e₁, _|_, rfl⟩⟩
    · apply h₂ at eval_e₁
      · exists rfl
        left
        exists Ma, Ta, Fa
      · trivial
    · apply h₂ at eval_e₁
      · exists rfl
        right
        exists Ma, Ta, Fa, v
      · rintro b (_|_)
        exact v_not_bool _ rfl

  theorem NetworkPlusCal.Statement.reorder_let'.{u} {name «=|∈»} {τ : Typ} {r} {e e': Expression.{0} Typ}
    (h' : r.name ∉ TypedSetTheory.prims.{u}) (h'' : name ≠ r.name) (h''' : name ∉ e'.freeVars)
    (h''' : ∀ arg ∈ r.args, ∀ e ∈ arg, name ∉ e.freeVars) :
      ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧⊥ ∪
        ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧* ∘ᵣ₁ ⟦NetworkPlusCal.Statement.let name τ «=|∈» e⟧⊥ ⊇
      ⟦NetworkPlusCal.Statement.let name τ «=|∈» ((↿e.replace) <| r.substOf e')⟧⊥ ∪
        ⟦NetworkPlusCal.Statement.let name τ «=|∈» ((↿e.replace) <| r.substOf e')⟧* ∘ᵣ₁ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧⊥ := by
    have generic_reorder_await' {e'' : Expression.{0} Typ}
      (neval_imp_neval : ∀ M, M ⊢ e' ↯ → M ⊢ e'' ↯)
      (eval_imp_eval : ∀ M T {v v' vss}, List.traverse (List.traverse (TypedSetTheory.eval (T ∪ M))) r.args = some vss
          → (r_name_in_M : r.name ∈ M) → r.name ∉ T → T ∪ M ⊢ e' ⇒ v → GuardedPlusCal.Memory.updateRef.doUpdate v (AList.get M r.name r_name_in_M) vss = some v'
          → T ∪ M ⊢ e'' ⇒ v') :
        ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧⊥
        ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧*
          ∘ᵣ₁ ⟦NetworkPlusCal.Statement.let name τ «=|∈» e⟧⊥ ⊇
        ⟦NetworkPlusCal.Statement.let name τ «=|∈» (e.replace r.name e'')⟧⊥
        ∪ ⟦NetworkPlusCal.Statement.let name τ «=|∈» (e.replace r.name e'')⟧*
          ∘ᵣ₁ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e'⟧⊥ := by as_aux_lemma =>
      rintro ⟨⟨Ma, Ta, Fa, _⟩, _⟩ (⟨rfl, abort_let⟩|⟨⟨Mb, Tb, Fb, _⟩, ε₁, ε₂, red_let, abort_assign, rfl⟩)
      · obtain abort_let|abort_let := abort_let
        · obtain ⟨_, _, _, neval_e_subst, _|_, rfl⟩ := abort_let
          by_cases r_name_in_fv_e : r.name ∈ e.freeVars
          · by_cases eval_e' : ∃ v, Ta ∪ Ma ⊢ e' ⇒ v
            · obtain ⟨v, eval_e'⟩ := eval_e'
              by_cases r_name_in_mem : r.name ∈ Ma ∧ r.name ∉ Ta
              · obtain ⟨r_name_in_Ma, r_name_not_in_Ta⟩ := r_name_in_mem

                by_cases eval_args : ∃ vss, List.traverse (List.traverse (TypedSetTheory.eval (Ta ∪ Ma))) r.args = some vss
                · obtain ⟨vss, eval_args⟩ := eval_args
                  by_cases upd : ∃ v', GuardedPlusCal.Memory.updateRef.doUpdate v (AList.get Ma r.name r_name_in_Ma) vss = some v'
                  · obtain ⟨v', upd_eq⟩ := upd
                    let Mb := Ma.insert r.name v'
                    have upd_eq : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v = some Mb := by
                      unfold GuardedPlusCal.Memory.updateRef
                      simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]

                      exists Ma.get r.name r_name_in_Ma, ?_, v', ?_ <;> try rfl
                      · apply AList.lookup_eq_some_get_of_mem
                      · assumption

                    right
                    exists ⟨Mb, Ta, Fa, none⟩, [], [], ?_, ?_ <;> try trivial
                    · sem_redn Ma ⤳ Mb, Ta, Fa
                      · exact v
                      · exact vss
                      · assumption
                      · simp_rw [List.traverse_eq_some] at eval_args
                        assumption
                      · assumption
                      · assumption
                    · exists rfl
                      left
                      exists Mb, Ta, Fa, ?_, ?_ <;> try rfl
                      rw [← neval_e_subst, TypedSetTheory.eval_subst h']
                      · apply TypedSetTheory.eval_mem_ext
                        intro x
                        rw [AList.union_insert_ext_of_not_mem r_name_not_in_Ta]
                      · apply eval_imp_eval <;> assumption
                  · push_neg at upd
                    rw [← Option.eq_none_iff_forall_ne_some] at upd

                    replace upd : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v = none := by
                      unfold GuardedPlusCal.Memory.updateRef
                      simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff]

                      intros v₁ lookup_r_name_Ma v₂ upd'
                      rw [AList.lookup_eq_some_get_of_mem r_name_in_Ma] at lookup_r_name_Ma
                      cases lookup_r_name_Ma
                      rw [upd] at upd'
                      contradiction

                    left
                    exists rfl
                    right
                    exists Ma, Ta, Fa, v, vss, ?_, ?_, ?_ <;> try trivial
                    simp_rw [List.traverse_eq_some] at eval_args
                    assumption
                · push_neg at eval_args
                  rw [← Option.eq_none_iff_forall_ne_some] at eval_args
                  simp_rw [List.traverse_eq_none] at eval_args
                  left
                  exists rfl
                  left; right
                  obtain ⟨a, a_in, e, e_in, neval_e⟩ := eval_args
                  exists _, a_in, _, e_in, Ma, Ta, Fa
              · rw [not_and_or, not_not] at r_name_in_mem
                left
                exists rfl
                left; left; left
                exists Ma, Ta, Fa
            · push_neg at eval_e'

              replace eval_e' : Ta ∪ Ma ⊢ e' ↯ := by rwa [Option.eq_none_iff_forall_ne_some]

              left
              exists rfl
              left; left; right
              exists Ma, Ta, Fa
          · rw [TypedSetTheory.eval_subst_of_not_mem_fv h' r_name_in_fv_e] at neval_e_subst
            by_cases eval_e' : ∃ v, Ta ∪ Ma ⊢ e' ⇒ v
            · obtain ⟨v, eval_e'⟩ := eval_e'
              by_cases r_name_in_mem : r.name ∈ Ma ∧ r.name ∉ Ta
              · obtain ⟨r_name_in_Ma, r_name_not_in_Ta⟩ := r_name_in_mem
                by_cases eval_args : ∃ vss, List.traverse (List.traverse (TypedSetTheory.eval (Ta ∪ Ma))) r.args = some vss
                · obtain ⟨vss, eval_args⟩ := eval_args
                  by_cases upd : ∃ v', GuardedPlusCal.Memory.updateRef.doUpdate v (AList.get Ma r.name r_name_in_Ma) vss = some v'
                  · obtain ⟨v', upd_eq⟩ := upd

                    let Mb := Ma.insert r.name v'
                    have upd_eq : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v = some Mb := by
                      unfold GuardedPlusCal.Memory.updateRef
                      simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]

                      exists Ma.get r.name r_name_in_Ma, ?_, v', ?_ <;> try rfl
                      · apply AList.lookup_eq_some_get_of_mem
                      · assumption

                    right
                    exists ⟨Mb, Ta, Fa, none⟩, [], [], ?_, ?_ <;> try trivial
                    · sem_redn Ma ⤳ Mb, Ta, Fa
                      · exact v
                      · exact vss
                      · assumption
                      · simp_rw [List.traverse_eq_some] at eval_args
                        assumption
                      · assumption
                      · assumption
                    · exists rfl
                      left
                      exists Mb, Ta, Fa, ?_, ?_ <;> try rfl
                      rw [← neval_e_subst]
                      apply eval_ext [r.name]
                      · intros x x_neq
                        rw [List.not_mem_singleton] at x_neq
                        rw [AList.union_insert_ext_of_not_mem r_name_not_in_Ta x, AList.lookup_insert_ne x_neq]
                      · rwa [List.singleton_disjoint]
                  · push_neg at upd
                    rw [← Option.eq_none_iff_forall_ne_some] at upd

                    replace upd : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v = none := by
                      unfold GuardedPlusCal.Memory.updateRef
                      simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff]

                      intros v₁ lookup_r_name_Ma v₂ upd'
                      rw [AList.lookup_eq_some_get_of_mem r_name_in_Ma] at lookup_r_name_Ma
                      cases lookup_r_name_Ma
                      rw [upd] at upd'
                      contradiction

                    left
                    exists rfl
                    right
                    exists Ma, Ta, Fa, v, vss, ?_, ?_, ?_ <;> try trivial
                    simp_rw [List.traverse_eq_some] at eval_args
                    assumption
                · push_neg at eval_args
                  rw [← Option.eq_none_iff_forall_ne_some] at eval_args
                  simp_rw [List.traverse_eq_none] at eval_args
                  left
                  exists rfl
                  left; right
                  obtain ⟨a, a_in, e, e_in, neval_e⟩ := eval_args
                  exists _, a_in, _, e_in, Ma, Ta, Fa
              · rw [not_and_or, not_not] at r_name_in_mem
                left
                exists rfl
                left; left; left
                exists Ma, Ta, Fa
            · push_neg at eval_e'

              replace eval_e' : Ta ∪ Ma ⊢ e' ↯ := by rwa [Option.eq_none_iff_forall_ne_some]

              left
              exists rfl
              left; left; right
              exists Ma, Ta, Fa
        · obtain ⟨_, _, _, v, eval_e_subst, _|_, rfl, v_is_set?⟩ := abort_let
          by_cases eval_e' : ∃ v, Ta ∪ Ma ⊢ e' ⇒ v
          · obtain ⟨v', eval_e'⟩ := eval_e'
            by_cases r_name_in_mem : r.name ∈ Ma ∧ r.name ∉ Ta
            · obtain ⟨r_name_in_Ma, r_name_not_in_Ta⟩ := r_name_in_mem
              by_cases eval_args : ∃ vss, List.traverse (List.traverse (TypedSetTheory.eval (Ta ∪ Ma))) r.args = some vss
              · obtain ⟨vss, eval_args⟩ := eval_args
                by_cases upd : ∃ v'', GuardedPlusCal.Memory.updateRef.doUpdate v' (AList.get Ma r.name r_name_in_Ma) vss = some v''
                · obtain ⟨v'', upd_eq'⟩ := upd

                  let Mb := Ma.insert r.name v''
                  have upd_eq : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v' = some Mb := by
                    unfold GuardedPlusCal.Memory.updateRef
                    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]

                    exists Ma.get r.name r_name_in_Ma, ?_, v'', ?_ <;> try rfl
                    · apply AList.lookup_eq_some_get_of_mem
                    · assumption

                  right
                  exists ⟨Mb, Ta, Fa, none⟩, [], [], ?_, ?_ <;> try trivial
                  · sem_redn Ma ⤳ Mb, Ta, Fa
                    · exact v'
                    · exact vss
                    · assumption
                    · simp_rw [List.traverse_eq_some] at eval_args
                      assumption
                    · assumption
                    · assumption
                  · exists rfl
                    right
                    exists Mb, Ta, Fa, v, ?_, ?_ <;> try trivial
                    rw [← eval_e_subst, TypedSetTheory.eval_subst h']
                    · apply TypedSetTheory.eval_mem_ext
                      intros x
                      rw [AList.union_insert_ext_of_not_mem r_name_not_in_Ta]
                    · apply eval_imp_eval Ma Ta <;> try assumption
                · push_neg at upd
                  rw [← Option.eq_none_iff_forall_ne_some] at upd

                  replace upd : GuardedPlusCal.Memory.updateRef Ma {r with args := vss} v' = none := by
                    unfold GuardedPlusCal.Memory.updateRef
                    simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff]

                    intros v₁ lookup_r_name_Ma v₂ upd'
                    rw [AList.lookup_eq_some_get_of_mem r_name_in_Ma] at lookup_r_name_Ma
                    cases lookup_r_name_Ma
                    rw [upd] at upd'
                    contradiction

                  left
                  exists rfl
                  right
                  exists Ma, Ta, Fa, v', vss, ?_, ?_, ?_ <;> try trivial
                  simp_rw [List.traverse_eq_some] at eval_args
                  assumption
              · push_neg at eval_args
                rw [← Option.eq_none_iff_forall_ne_some] at eval_args
                simp_rw [List.traverse_eq_none] at eval_args
                left
                exists rfl
                left; right
                obtain ⟨a, a_in, e, e_in, neval_e⟩ := eval_args
                exists _, a_in, _, e_in, Ma, Ta, Fa
            · rw [not_and_or, not_not] at r_name_in_mem
              left
              exists rfl
              left; left; left
              exists Ma, Ta, Fa
          · push_neg at eval_e'

            replace eval_e' : Ta ∪ Ma ⊢ e' ↯ := by rwa [Option.eq_none_iff_forall_ne_some]

            left
            exists rfl
            left; left; right
            exists Ma, Ta, Fa
      · obtain ⟨⟨_, _, _⟩, rfl, ⟨_, _, _, _, eval_e, lookup_name, _|_, rfl, int_is_set?⟩, _|_, rfl⟩ := red_let
        split at int_is_set?
          <;> try trivial

        2: cases int_is_set?
        1: obtain ⟨_, _, _|_⟩ := int_is_set?

        all:
          obtain ⟨-, ((abort_assign|abort_assign)|abort_assign)|abort_assign⟩ := abort_assign
          · obtain ⟨_, _, _, r_unassignable, _|_, rfl⟩ := abort_assign
            left
            exists rfl
            left; left; left
            exists Ma, Ta, Fa, ?_, ?_ <;> try rfl
            apply r_unassignable.imp_right λ r_name_in ↦ ?_
            rwa [AList.mem_insert_of_ne (Ne.symm h'')] at r_name_in
          · by_cases r_name_in_fv_e : r.name ∈ e.freeVars
            · obtain ⟨_, _, _, neval_e', _|_, rfl⟩ := abort_assign
              rw [TypedSetTheory.neval_subst_of_mem_fv_of_neval r_name_in_fv_e] at eval_e
              · contradiction
              · apply neval_imp_neval
                rw [← neval_e']
                apply eval_ext [name]
                intros x x_neq
                rw [List.not_mem_singleton] at x_neq
                rw [AList.lookup_union, AList.lookup_union, AList.lookup_insert_ne x_neq]
                rwa [List.singleton_disjoint]
            · left
              exists rfl
              left; left; right
              obtain ⟨_, _, _, eval_e', _|_, rfl⟩ := abort_assign
              exists Ma, Ta, Fa, ?_, ?_ <;> try trivial
              rw [← eval_e']
              apply eval_ext [name]
              intros x x_neq
              rw [List.not_mem_singleton] at x_neq
              rw [AList.lookup_union, AList.lookup_union, AList.lookup_insert_ne x_neq]
              rwa [List.singleton_disjoint]
          · left
            exists rfl
            left; right
            obtain ⟨arg, arg_in, e'', e''_in, _, _, _, eval_e'', _|_, rfl⟩ := abort_assign
            exists arg, arg_in, e'', e''_in, Ma, Ta, Fa, ?_, ?_ <;> try rfl
            rw [← eval_e'']
            apply eval_ext [name]
            intros x x_neq
            rw [List.not_mem_singleton] at x_neq
            rw [AList.lookup_union, AList.lookup_union, AList.lookup_insert_ne x_neq]
            rw [List.singleton_disjoint]
            exact h''' _ arg_in _ e''_in
          · left
            exists rfl
            right
            obtain ⟨_, _, _, v, vss, eval_e', eval_args, upd, r_name_not_in, _|_, rfl⟩ := abort_assign
            exists Ma, Ta, Fa, v, vss, ?_, ?_, upd, ?_, ?_ <;> try rfl
            · rw [← eval_e']
              apply eval_ext [name]
              intros x x_neq
              rw [List.not_mem_singleton] at x_neq
              rw [AList.lookup_union, AList.lookup_union, AList.lookup_insert_ne x_neq]
              rwa [List.singleton_disjoint]
            · rw [← List.forall₂_iff_forall₂_attach] at eval_args ⊢
              refine List.Forall₂.imp ?_ eval_args
              intros es'' vs''
              rw (config := {occs := .pos [1]}) [← List.forall₂_iff_forall₂_attach]
              rw (config := {occs := .pos [2]}) [← List.forall₂_iff_forall₂_attach]
              apply List.Forall₂.imp
              intros e v eval_e
              rw [← eval_e]
              apply eval_ext [name]
              · intros x x_neq
                rw [List.not_mem_singleton] at x_neq
                rw [AList.lookup_union, AList.lookup_union, AList.lookup_insert_ne x_neq]
              · rw [List.singleton_disjoint]
                exact h''' _ es''.property _ e.property
            · rwa [AList.mem_insert_of_ne (Ne.symm h'')] at r_name_not_in

    unfold GuardedPlusCal.Ref.substOf
    split_ifs with args_empty <;> apply generic_reorder_await'
    · exact λ _ ↦ id
    · intros M T v v' vss eval_args _ _ eval_e' upd_eq
      rw [List.nil_of_isEmpty args_empty, List.traverse_nil'] at eval_args
      cases eval_args
      rw [GuardedPlusCal.Memory.updateRef.doUpdate_empty_args] at upd_eq
      cases upd_eq
      assumption
    · exact NetworkPlusCal.Statement.reorder_await'.aux_neval_except
    · exact λ M T v v' vss ↦ NetworkPlusCal.Statement.reorder_await'.aux_eval_except h'

  theorem AtomicBranch.correctness_precond_let.{u} {nameₛ} {mailboxₛ} {name} {τ : Typ.{u}} {«=|∈»} {e : Expression.{u} Typ}
    (wf : match mailboxₛ with | none => True | some _ => inbox ++ nameₛ ≠ name ∧ Expression.FreshIn e (inbox ++ nameₛ))
    --(wf : match mailboxₛ with | none => True | some _ => inbox ++ nameₛ ∉ (GuardedPlusCal.Statement.let pos name τ «=|∈» e).freeVars Expression.freeVars)
    (wf' : name ≠ "self") :
      StrongRefinement.Terminating (· ∼[Option.map (fun x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·)
        ⟦GuardedPlusCal.Statement.let name τ «=|∈» e⟧* ⟦GuardedPlusCal.Statement.let name τ «=|∈» e⟧⊥
        ⟦NetworkPlusCal.Statement.let name τ «=|∈» e⟧* := by
    rintro ⟨Mₜ, Tₜ, Fₜ, _⟩ ⟨Mₜ', Tₜ', Fₜ', _⟩ ε ⟨Mₛ, Tₛ, Fₛ, _⟩ sim_σₛ_σₜ ⟨_, rfl, ⟨_, _, _, v', eval_e, _, _|_, rfl, next⟩, rfl, rfl⟩
    split at next using vs <;> try contradiction
    1:  obtain ⟨v', v'_in, next⟩ := next
    all:
      obtain _|_ := next
      left
      sem_exists Mₛ, Tₛ ⤳ Tₛ.insert name v', Fₛ

    -- The matching relation holds between the new states
    1,7:
      cases mailboxₛ with
      | none => refine ⟨rfl, sim_σₛ_σₜ.right.left, sim_σₛ_σₜ.right.right.left ▸ rfl, sim_σₛ_σₜ.right.right.right⟩
      | some mailboxₛ =>
        have name_neq : name ≠ inbox ++ nameₛ := Ne.symm wf.left

        obtain ⟨rfl, sim_σₛ_σₜ⟩ := sim_σₛ_σₜ
        dsimp at sim_σₛ_σₜ
        split at sim_σₛ_σₜ using _ | h | h <;> solve
          | contradiction
          | cases h
            refine ⟨rfl, ?_, ?_, ?_⟩
            · intros v v_neq
              by_cases h : v = name
              · subst v
                rw [sim_σₛ_σₜ.left _ v_neq]
              · apply sim_σₛ_σₜ.left
                assumption
            · rw [sim_σₛ_σₜ.right.left]
            · solve
                | obtain ⟨vs, _, _, v, eval_self, _, _, _⟩ := sim_σₛ_σₜ.right.right
                  refine ⟨vs, ‹_›, ?_, v, ?_, ‹_›, ‹_›, ‹_›⟩
                  · rwa [AList.lookup_insert_ne (Ne.symm name_neq)]
                  · rw [← eval_self, TypedSetTheory.eval_var, TypedSetTheory.eval_var]
                    split_ifs <;> try trivial
                    simp_rw [AList.lookup_union, AList.lookup_insert_ne (Ne.symm wf')]
                | obtain ⟨vs, _, _, _, _, _⟩ := sim_σₛ_σₜ.right.right
                  refine ⟨vs, ‹_›, ?_, ‹_›, ‹_›, ‹_›⟩
                  rwa [AList.lookup_insert_ne (Ne.symm name_neq)]

    1,6: exact relatesTo_eq_label sim_σₛ_σₜ

    1: exact .set vs
    -- 4: exact v'

    -- Evaluations in Mₜ and Mₛ yield the same values
    1,4:
      cases mailboxₛ with
      | none =>
        rwa [sim_σₛ_σₜ.right.left, sim_σₛ_σₜ.right.right.left]
      | some mailboxₛ =>
        rw [← eval_e]
        obtain ⟨-, sim_σₛ_σₜ⟩ := sim_σₛ_σₜ
        dsimp at sim_σₛ_σₜ
        split at sim_σₛ_σₜ using _ | h | h <;> solve
          | contradiction
          | cases h
            apply eval_ext [inbox ++ nameₛ]
            · simp_rw [List.not_mem_singleton]
              intros x x_neq
              simp_rw [AList.lookup_union, sim_σₛ_σₜ.right.left, sim_σₛ_σₜ.left _ x_neq]
            · rw [List.singleton_disjoint]
              apply not_mem_of_fresh
              exact wf.right

    2,4:
      exists _, v'_in

    -- Memories do not contain the new binding
    1,2:
      cases mailboxₛ with
      | none =>
        rwa [sim_σₛ_σₜ.right.left, sim_σₛ_σₜ.right.right.left]
      | some _ =>
        have name_neq : name ≠ inbox ++ nameₛ := Ne.symm wf.left
          -- simp_rw [GuardedPlusCal.Statement.freeVars, List.not_mem_cons_iff] at wf
          -- exact Ne.symm wf.left

        obtain ⟨-, sim_σₛ_σₜ⟩ := sim_σₛ_σₜ
        dsimp at sim_σₛ_σₜ
        split at sim_σₛ_σₜ using _ | h | h <;> solve
          | contradiction
          | cases h
            rw [sim_σₛ_σₜ.right.left]
            simp_rw [AList.lookup_union, sim_σₛ_σₜ.left _ name_neq, ← AList.lookup_union]
            assumption

  theorem AtomicBranch.correctness_precond_await.{u} {nameₛ} {mailboxₛ} {e : Expression.{u} Typ}
    (wf : match mailboxₛ with | none => True | some _ => Expression.FreshIn e (inbox ++ nameₛ)) : -- (GuardedPlusCal.Statement.await (Typ := Typ) pos e).freeVars Expression.freeVars) :
      StrongRefinement.Terminating (· ∼[Option.map (λ x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·)
        ⟦GuardedPlusCal.Statement.await.{u} (Typ := Typ) e⟧* ⟦GuardedPlusCal.Statement.await.{u} (Typ := Typ) e⟧⊥
        ⟦NetworkPlusCal.Statement.await.{u} (Typ := Typ) e⟧* := by
    rintro ⟨Mₜ, Tₜ, Fₜ, _⟩ ⟨Mₜ', Tₜ', Fₜ', _⟩ ε ⟨Mₛ, Tₛ, Fₛ, _⟩ sim_σₛ_σₜ ⟨_, rfl, ⟨_, _, _, _|_, _|_, eval_e, rfl⟩, _|_, rfl⟩
    left
    sem_exists Mₛ, Tₛ, Fₛ
    · rwa [sim_σₛ_σₜ.left] at sim_σₛ_σₜ
    · exact relatesTo_eq_label sim_σₛ_σₜ
    · cases mailboxₛ with
      | none => rwa [sim_σₛ_σₜ.right.left, sim_σₛ_σₜ.right.right.left]
      | some mailboxₛ =>
        trans TypedSetTheory.eval (Tₜ ∪ Mₜ) e
        · apply eval_ext [inbox ++ nameₛ]
          · obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim_σₛ_σₜ <;> {
              simp_rw [List.not_mem_singleton]
              intros v v_not_in
              simp_rw [AList.lookup_union, sim_σₛ_σₜ.right.right.left, sim_σₛ_σₜ.right.left _ v_not_in]
            }
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            assumption
        · assumption

  set_option linter.unusedTactic false in
  theorem AtomicBranch.correctness_precond_receive {nameₛ : String} {mailboxₛ : Expression.{0} Typ}
    {chan : GuardedPlusCal.ChanRef.{0} Typ (Expression Typ)}
    {ref : GuardedPlusCal.Ref.{0} Typ (Expression Typ)} {τ}
    (wf : GuardedPlusCal.Statement.FreshIn.{0} Expression.FreshIn (GuardedPlusCal.Statement.receive (Typ := Typ) chan ref) (inbox ++ nameₛ))
    (wf₂ : ref.name ≠ "self")
    (wf' : match mailboxₛ with
      | .var x (.channel τ) => chan = {name := x, τ := .channel τ, args := [] : GuardedPlusCal.ChanRef Typ (Expression Typ)}
      | .funcall (.var x (.function .address (.channel τ))) [.var "self" .address] => chan = {name := x, τ := .function .address (.channel τ), args := [.var "self" .address] : GuardedPlusCal.ChanRef Typ (Expression Typ)}
      | _ => False) :
      StrongRefinement.Terminating (· ∼[.some (mailboxₛ, inbox ++ nameₛ)] ·)
        ⟦GuardedPlusCal.Statement.receive (Typ := Typ) chan ref⟧*
        ⟦GuardedPlusCal.Statement.receive (Typ := Typ) chan ref⟧⊥
        (⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ) (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«>» (.nat "0"))⟧* ∘ᵣ₂
         ⟦NetworkPlusCal.Statement.assign (Typ := Typ) ref (Expression.opcall (.var "Head" (.operator [.seq τ] τ)) [.var (inbox ++ nameₛ) (.seq τ)])⟧* ∘ᵣ₂
         ⟦NetworkPlusCal.Statement.assign (Typ := Typ) ⟨inbox ++ nameₛ, .seq τ, []⟩ (Expression.opcall (Typ := Typ) (.var "Tail" (.operator [.seq τ] (.seq τ))) [.var (inbox ++ nameₛ) (.seq τ)])⟧*) := by
    rintro ⟨Maₜ, Taₜ, Faₜ, _⟩ ⟨Mdₜ, Tdₜ, Fdₜ, _⟩ ε ⟨Maₛ, Tₛ, Fₛ, _⟩ sim_σₛ_σₜ ⟨⟨Mcₜ, Tcₜ, Fcₜ, _⟩, _, _, red_await, ⟨⟨Mbₜ, Tbₜ, Fbₜ, _⟩, ε₁, ε₂, red_assign_ref, red_assign_inbox, rfl⟩, rfl⟩
    obtain ⟨⟨⟩, rfl, ⟨_, _, _, _|_, _|_, eval_len_inbox, rfl⟩, _|_, rfl⟩ := red_await
    obtain ⟨⟨⟩, -, ⟨_, _, _, _, v, vss, eval_Head_inbox, eval_ref_args, upd_Maₜ_eq_Mcₜ, _, _|_, _|_, rfl⟩, _|_, rfl⟩ := red_assign_ref
    obtain ⟨⟨⟩, -, ⟨_, _, _, _, v', vss', eval_Tail_inbox, eval_ref_args', upd_Mcₜ_eq_Mdₜ, _, _|_, _|_, rfl⟩, _|_, rfl⟩ := red_assign_inbox

    obtain ⟨_, _, eval_inbox_eq, vs, rfl⟩ := TypedSetTheory.eval_Head_to_is_nonempty_seq TypedSetTheory.eval_Head eval_Head_inbox
    obtain ⟨_, v', vs', eval_inbox_eq', rfl⟩ := TypedSetTheory.eval_Tail_is_seq TypedSetTheory.eval_Tail eval_Tail_inbox
    clear eval_Head_inbox eval_Tail_inbox

    have ref_name_neq : ref.name ≠ inbox ++ nameₛ := by
      obtain ⟨_, _, _, _⟩ := wf
      assumption

    have : TypedSetTheory.eval (Taₜ ∪ Mbₜ) (.var (inbox ++ nameₛ) (.seq τ)) = TypedSetTheory.eval (Taₜ ∪ Maₜ) (.var (inbox ++ nameₛ) (.seq τ)) := by
      trans
      · apply TypedSetTheory.eval_not_fv_irrel (v := ref.name)
        unfold Expression.freeVars
        simp [ref_name_neq]
      · -- TODO: extract as lemma?
        unfold GuardedPlusCal.Memory.updateRef at upd_Maₜ_eq_Mcₜ
        simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Maₜ_eq_Mcₜ
        obtain ⟨v, _, v', _, _|_⟩ := upd_Maₜ_eq_Mcₜ
        simp_rw [AList.union_erase, AList.erase_insert, TypedSetTheory.eval_var]
        split_ifs <;> try trivial
        simp_rw [AList.lookup_union, AList.lookup_erase_ne (Ne.symm ref_name_neq)]
    erw [this] at eval_inbox_eq'
    obtain _|_ := TypedSetTheory.eval_det eval_inbox_eq eval_inbox_eq'
    clear this eval_inbox_eq'
    unfold TypedSetTheory.eval at eval_inbox_eq
    dsimp [TypedSetTheory.primFromName] at eval_inbox_eq
    split_ifs at eval_inbox_eq <;> first
      | split at eval_inbox_eq <;> injections
      | skip

    guard_goal_nums 1

    obtain ⟨rfl, sim_σₛ_σₜ⟩ := sim_σₛ_σₜ
    split at sim_σₛ_σₜ using _ | x τ₁ τ₂ _ h | x τ _ h <;> first
      | contradiction
      | cases h
    · obtain ⟨mem_ext, rfl, vs, lookup_inbox, inbox_not_in_Tₛ, v₀, eval_es_vs', fifos_ext₁, fifos_ext₂, lookup_mailbox⟩ := sim_σₛ_σₜ
      split at wf' using _ | _ _ h <;> try contradiction
      cases h
      obtain rfl := wf'

      cases lookup_mbox_Faₜ : AList.lookup (x, [v₀]) Faₜ with
      | none =>
        right
        exists [], List.prefix_refl _
        rw [lookup_mbox_Faₜ, Option.bind_eq_bind, Option.bind_none] at lookup_mailbox
        refine ⟨rfl, ?_⟩
        left
        right
        refine ⟨_, _, _, [v₀], rfl, rfl, ?_, ?_⟩
        · rwa [List.forall₂_singleton]
        · assumption
      | some vs' =>
        erw [lookup_mbox_Faₜ, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at lookup_mailbox

        rw [AList.lookup_union_eq_some] at eval_inbox_eq
        obtain inbox_in_Tₛ|⟨inbox_not_in_Tₛ, eval_inbox_eq⟩ := eval_inbox_eq
        · rw [inbox_not_in_Tₛ] at inbox_in_Tₛ
          contradiction
        · rw [lookup_inbox] at eval_inbox_eq
          cases eval_inbox_eq
          rw [List.cons_append] at lookup_mailbox
          left

          obtain ⟨Mbₛ, upd_Maₛ_eq_Mbₛ⟩ : ∃ Mbₛ, GuardedPlusCal.Memory.updateRef Maₛ { ref with args := vss } v = .some Mbₛ := by
            unfold GuardedPlusCal.Memory.updateRef at upd_Maₜ_eq_Mcₜ ⊢
            simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Maₜ_eq_Mcₜ ⊢
            obtain ⟨v', lookup_Maₜ, v'', update_v, _|_⟩ := upd_Maₜ_eq_Mcₜ
            refine ⟨AList.insert ref.name v'' Maₛ, v', ?_, v'', ?_, rfl⟩
            · rw [← lookup_Maₜ, mem_ext _ ref_name_neq]
            · assumption

          sem_exists Maₛ ⤳ Mbₛ, Tₛ, Fₛ ⤳ Fₛ.replace (x, [v₀]) (vs ++ vs')
          · refine ⟨rfl, ?_, rfl, vs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intros v' v'_neq

              have lookup_v' : AList.lookup v' Maₛ = AList.lookup v' Maₜ := mem_ext _ v'_neq
              have lookup_ref_name : AList.lookup ref.name Maₛ = AList.lookup ref.name Maₜ := mem_ext _ ref_name_neq

              unfold GuardedPlusCal.Memory.updateRef at upd_Maₛ_eq_Mbₛ upd_Maₜ_eq_Mcₜ upd_Mcₜ_eq_Mdₜ
              simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Maₛ_eq_Mbₛ upd_Maₜ_eq_Mcₜ upd_Mcₜ_eq_Mdₜ
              obtain ⟨v₁, h₁₁, _, h₁₂, _|_⟩ := upd_Maₛ_eq_Mbₛ
              obtain ⟨v₂, h₂₁, _, h₂₂, _|_⟩ := upd_Maₜ_eq_Mcₜ
              obtain ⟨v₃, h₃₁, _, h₃₂, _|_⟩ := upd_Mcₜ_eq_Mdₜ

              rw [AList.lookup_insert_ne v'_neq]
              by_cases h : v' = ref.name
              · subst v'
                have : v₁ = v₂ := by rw [← Option.some_inj, ← h₁₁, ← h₂₁, mem_ext _ ref_name_neq]
                rw [AList.lookup_insert, AList.lookup_insert, ← h₁₂, ← h₂₂, this]
              · rw [AList.lookup_insert_ne h, AList.lookup_insert_ne h, mem_ext _ v'_neq]
            · unfold GuardedPlusCal.Memory.updateRef at upd_Mcₜ_eq_Mdₜ
              simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Mcₜ_eq_Mdₜ
              obtain ⟨v, lookup_Mcₜ, v'', upd, _|_⟩ := upd_Mcₜ_eq_Mdₜ
              obtain rfl := List.forall₂_nil_left_iff.mp eval_ref_args'
              rw [AList.lookup_insert, ← upd]
              unfold GuardedPlusCal.Memory.updateRef.doUpdate
              trivial
            · assumption
            · exact v₀
            · rw [← eval_es_vs', eval_ext [ref.name]]
              · intros x x_neq
                rw [List.not_mem_singleton] at x_neq
                unfold GuardedPlusCal.Memory.updateRef at upd_Maₛ_eq_Mbₛ
                simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Maₛ_eq_Mbₛ
                obtain ⟨_, _, _, _, _|_⟩ := upd_Maₛ_eq_Mbₛ
                rw [AList.lookup_union, AList.lookup_union, AList.lookup_insert_ne x_neq]
              · rwa [List.singleton_disjoint, Expression.freeVars, List.not_mem_singleton]
            · intros c' c'_neq es'
              rw [AList.lookup_replace_ne]
              · apply fifos_ext₁
                assumption
              · simp [c'_neq]
            · intros es' es'_neq
              rw [AList.lookup_replace_ne]
              · apply fifos_ext₂
                assumption
              · simp [es'_neq]
            · rw [AList.lookup_replace, lookup_mailbox, lookup_mbox_Faₜ]
              rfl
          -- · exact [v₀]
          · exact vss
          · exact v
          -- · exact vs ++ vs'
          · rwa [List.forall₂_singleton]
          · rw [← List.forall₂_iff_forall₂_attach] at eval_ref_args ⊢
            refine List.Forall₂.imp ?_ eval_ref_args
            intros es'' vs''
            rw (config := {occs := .pos [1]}) [← List.forall₂_iff_forall₂_attach]
            rw (config := {occs := .pos [2]}) [← List.forall₂_iff_forall₂_attach]
            apply List.Forall₂.imp
            intros e v eval_e
            rw [← eval_e]
            apply eval_ext [inbox ++ nameₛ]
            · intros v v_not_in
              rw [List.not_mem_singleton] at v_not_in
              simp_rw [AList.lookup_union, mem_ext _ v_not_in]
            · rw [List.singleton_disjoint]
              obtain ⟨_, _, _, wf⟩ := wf
              apply not_mem_of_fresh
              exact wf _ es''.property _ e.property
          · assumption
          · assumption
          -- · rfl
    · obtain ⟨mem_ext, rfl, vs, lookup_inbox, inbox_not_in_Tₛ, fifos_ext₁, fifos_ext₂, lookup_mailbox⟩ := sim_σₛ_σₜ
      split at wf' using h' <;> try contradiction
      cases wf'
      cases h'
      cases lookup_mbox_Faₜ : AList.lookup (x, []) Faₜ with
      | none =>
        right
        exists [], List.prefix_refl _
        rw [lookup_mbox_Faₜ, Option.bind_eq_bind, Option.bind_none] at lookup_mailbox
        refine ⟨rfl, ?_⟩
        left
        right
        exists _, _, _, _, rfl, rfl, List.Forall₂.nil
      | some vs' =>
        erw [lookup_mbox_Faₜ, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at lookup_mailbox

        rw [AList.lookup_union_eq_some] at eval_inbox_eq
        obtain inbox_in_Tₛ|⟨inbox_not_in_Tₛ, eval_inbox_eq⟩ := eval_inbox_eq
        · rw [inbox_not_in_Tₛ] at inbox_in_Tₛ
          contradiction
        · rw [lookup_inbox] at eval_inbox_eq
          cases eval_inbox_eq
          rw [List.cons_append] at lookup_mailbox
          left

          obtain ⟨Mbₛ, upd_Maₛ_eq_Mbₛ⟩ : ∃ Mbₛ, GuardedPlusCal.Memory.updateRef Maₛ { ref with args := vss } v = .some Mbₛ := by
            unfold GuardedPlusCal.Memory.updateRef at upd_Maₜ_eq_Mcₜ ⊢
            simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Maₜ_eq_Mcₜ ⊢
            obtain ⟨v', lookup_Maₜ, v'', update_v, _|_⟩ := upd_Maₜ_eq_Mcₜ
            refine ⟨AList.insert ref.name v'' Maₛ, v', ?_, v'', ?_, rfl⟩
            · rw [← lookup_Maₜ, mem_ext _ ref_name_neq]
            · assumption

          sem_exists Maₛ ⤳ Mbₛ, Tₛ, Fₛ ⤳ Fₛ.replace (x, []) (vs ++ vs')
          · refine ⟨rfl, ?_, rfl, vs, ?_, ?_, ?_, ?_, ?_⟩
            · intros v' v'_neq

              have lookup_v' : AList.lookup v' Maₛ = AList.lookup v' Maₜ := mem_ext _ v'_neq
              have lookup_ref_name : AList.lookup ref.name Maₛ = AList.lookup ref.name Maₜ := mem_ext _ ref_name_neq

              unfold GuardedPlusCal.Memory.updateRef at upd_Maₛ_eq_Mbₛ upd_Maₜ_eq_Mcₜ upd_Mcₜ_eq_Mdₜ
              simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Maₛ_eq_Mbₛ upd_Maₜ_eq_Mcₜ upd_Mcₜ_eq_Mdₜ
              obtain ⟨v₁, h₁₁, _, h₁₂, _|_⟩ := upd_Maₛ_eq_Mbₛ
              obtain ⟨v₂, h₂₁, _, h₂₂, _|_⟩ := upd_Maₜ_eq_Mcₜ
              obtain ⟨v₃, h₃₁, _, h₃₂, _|_⟩ := upd_Mcₜ_eq_Mdₜ

              rw [AList.lookup_insert_ne v'_neq]
              by_cases h : v' = ref.name
              · subst v'
                have : v₁ = v₂ := by rw [← Option.some_inj, ← h₁₁, ← h₂₁, mem_ext _ ref_name_neq]
                rw [AList.lookup_insert, AList.lookup_insert, ← h₁₂, ← h₂₂, this]
              · rw [AList.lookup_insert_ne h, AList.lookup_insert_ne h, mem_ext _ v'_neq]
            · unfold GuardedPlusCal.Memory.updateRef at upd_Mcₜ_eq_Mdₜ
              simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Mcₜ_eq_Mdₜ
              obtain ⟨v, lookup_Mcₜ, v'', upd, _|_⟩ := upd_Mcₜ_eq_Mdₜ
              obtain rfl := List.forall₂_nil_left_iff.mp eval_ref_args'
              rw [AList.lookup_insert, ← upd]
              unfold GuardedPlusCal.Memory.updateRef.doUpdate
              trivial
            · assumption
            · intros c' c'_neq es'
              rw [AList.lookup_replace_ne]
              · apply fifos_ext₁
                assumption
              · simp [c'_neq]
            · intros es' es'_neq
              rw [AList.lookup_replace_ne]
              · apply fifos_ext₂
                assumption
              · simp [es'_neq]
            · rw [AList.lookup_replace, lookup_mailbox, lookup_mbox_Faₜ]
              rfl
          -- · exact []
          · exact vss
          · exact v
          -- · exact vs ++ vs'
          · apply List.Forall₂.nil
          · rw [← List.forall₂_iff_forall₂_attach] at eval_ref_args ⊢
            refine List.Forall₂.imp ?_ eval_ref_args
            intros es'' vs''
            rw (config := {occs := .pos [1]}) [← List.forall₂_iff_forall₂_attach]
            rw (config := {occs := .pos [2]}) [← List.forall₂_iff_forall₂_attach]
            apply List.Forall₂.imp
            intros e v eval_e
            rw [← eval_e]
            apply eval_ext [inbox ++ nameₛ]
            · intros v v_not_in
              rw [List.not_mem_singleton] at v_not_in
              simp_rw [AList.lookup_union, mem_ext _ v_not_in]
            · rw [List.singleton_disjoint]
              obtain ⟨_, _, _, wf⟩ := wf
              apply not_mem_of_fresh
              exact wf _ es''.property _ e.property
          · assumption
          · assumption
          -- · rfl

  theorem sem_assoc {α β ε} [Trace ε] [Reduce α (Set (β × ε × β))] {S : α} {Ss : List α} :
      List.foldr (⟦·⟧* ∘ᵣ₂ ·) {(x, e, y) | x = y ∧ e = Trace.τ} (Ss ++ [S]) =
        List.foldr (⟦·⟧* ∘ᵣ₂ ·) {(x, e, y) | x = y ∧ e = Trace.τ} Ss ∘ᵣ₂ ⟦S⟧* := by
    rw [← List.foldr_map, List.map_append, List.map_singleton, List.foldr_concat]
    conv_lhs => enter [2]; apply Relation.lcomp₂.right_id_eq
    conv_lhs => enter [2]; apply Relation.lcomp₂.left_id_eq.symm
    rw [List.foldr_assoc (ha := ⟨λ _ _ _ ↦ Relation.lcomp₂.assoc.symm⟩), List.foldr_map]
    rfl

  theorem sem_assoc' {α β ε} [Trace ε] [Reduce α (Set (β × ε × β))] {S : α} {Ss : List (Set (β × ε × β))} :
      List.foldl Relation.lcomp₂ ({(x, e, y) | x = y ∧ e = Trace.τ} ∘ᵣ₂ ⟦S⟧*) Ss = ⟦S⟧* ∘ᵣ₂ List.foldl Relation.lcomp₂ {(x, e, y) | x = y ∧ e = Trace.τ} Ss := by
    conv_lhs => enter [2]; apply Relation.lcomp₂.left_id_eq
    conv_lhs => enter [2]; apply Relation.lcomp₂.right_id_eq.symm
    rw [← List.foldl_map, List.foldl_assoc (ha := ⟨λ _ _ _ ↦ Relation.lcomp₂.assoc.symm⟩), List.foldl_map]
    rfl

  theorem sem_assoc'' {α β ε} [Trace ε] [Reduce α (Set (β × ε × β))] {S : α} {Ss : List α} :
      List.foldr (⟦·⟧* ∘ᵣ₂ ·) ⟦S⟧* Ss =
        List.foldr (⟦·⟧* ∘ᵣ₂ ·) {(x, e, y) | x = y ∧ e = Trace.τ} Ss ∘ᵣ₂ ⟦S⟧* := by
    rw [← List.foldr_map]
    conv_lhs => enter [2]; apply Relation.lcomp₂.left_id_eq.symm
    rw [List.foldr_assoc (ha := ⟨λ _ _ _ ↦ Relation.lcomp₂.assoc.symm⟩), List.foldr_map]
    rfl

  theorem abort_assoc {α β ε} [Trace ε] [Reduce α (Set (β × ε × β))] [Abort α (Set (β × ε))] {S : α} {Ss : List α} :
      List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ (Ss ++ [S]) =
        List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ss ∪
          List.foldr (⟦·⟧* ∘ᵣ₂ ·) {(x, e, y) | x = y ∧ e = Trace.τ} Ss ∘ᵣ₁ ⟦S⟧⊥ := by
    induction Ss with
    | nil =>
      simp_rw [List.nil_append, List.foldr_cons, List.foldr_nil]
      conv_lhs => rw [Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]
      conv_rhs => rw [Set.empty_union]; apply Relation.lcomp₁.left_id_eq
    | cons S Ss IH =>
      simp_rw [List.cons_append, List.foldr_cons, IH, Relation.lcomp₁.right_union_eq_union, Relation.lcomp₁.left_lcomp₂_eq, Set.union_assoc]

  theorem abort_assoc' {α γ β ε} [Trace ε] [Reduce α (Set (β × ε × β))] [Reduce γ (Set (β × ε × β))]
    [Abort α (Set (β × ε))] [Abort γ (Set (β × ε))] {S : γ} {Ss : List α} :
      List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ⟦S⟧⊥ Ss =
        List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ss ∪
          List.foldr (⟦·⟧* ∘ᵣ₂ ·) {(x, e, y) | x = y ∧ e = Trace.τ} Ss ∘ᵣ₁ ⟦S⟧⊥ := by
    conv_lhs => enter [2]; rw [← Set.union_empty (a := ⟦S⟧⊥), ← Relation.lcomp₁.right_empty_eq_empty (R := ⟦S⟧*)]
    induction Ss with
    | nil =>
      repeat rw [List.foldr_nil]
      erw [Relation.lcomp₁.right_empty_eq_empty, Set.union_empty, Set.empty_union, Relation.lcomp₁.left_id_eq]
    | cons S' Ss IH =>
      repeat rw [List.foldr_cons]
      rw [IH, Relation.lcomp₁.right_union_eq_union, Set.union_assoc, Relation.lcomp₁.left_lcomp₂_eq]

  theorem div_assoc' {α γ β ε} [Trace ε] [Reduce α (Set (β × ε × β))] [Reduce γ (Set (β × ε × β))]
    [Diverge α (Set (β × ε))] [Diverge γ (Set (β × ε))] {S : γ} {Ss : List α} :
      List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ⟦S⟧∞ Ss =
        List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ss ∪
          List.foldr (⟦·⟧* ∘ᵣ₂ ·) {(x, e, y) | x = y ∧ e = Trace.τ} Ss ∘ᵣ₁ ⟦S⟧∞ := by
    conv_lhs => enter [2]; rw [← Set.union_empty (a := ⟦S⟧∞), ← Relation.lcomp₁.right_empty_eq_empty (R := ⟦S⟧*)]
    induction Ss with
    | nil =>
      repeat rw [List.foldr_nil]
      erw [Relation.lcomp₁.right_empty_eq_empty, Set.union_empty, Set.empty_union, Relation.lcomp₁.left_id_eq]
    | cons S' Ss IH =>
      repeat rw [List.foldr_cons]
      rw [IH, Relation.lcomp₁.right_union_eq_union, Set.union_assoc, Relation.lcomp₁.left_lcomp₂_eq]

  theorem Nat.even_div_two {n : Nat} (h : Even n) : n / 2 = (n + 1) / 2 := by
    rw [Nat.div_eq_iff]
    · rw [Nat.even_iff] at h
      omega
    · exact Nat.zero_lt_two

  theorem Nat.odd_div_two {n : Nat} (h : Odd n) : n / 2 + 1 = (n + 1) / 2 := by
    rw [← Nat.add_div_right n Nat.zero_lt_two]
    replace h : Even (n + 1) := by grind only [= Nat.odd_iff, = Nat.even_iff]
    rw [Nat.even_div_two h]

  lemma foldl_red_eq_foldr_red {α β ε} [Trace ε] (xs : List β) [Reduce β (Set (α × ε × α))] :
      xs.foldl (· ∘ᵣ₂ ⟦·⟧*) {⟨x, e, y⟩ : α × ε × α | x = y ∧ e = Trace.τ} = xs.foldr (⟦·⟧* ∘ᵣ₂ ·) {⟨x, e, y⟩ | x = y ∧ e = Trace.τ} := by
    induction xs with
    | nil =>
      rfl
    | cons x xs IH =>
      erw [List.foldl_cons, ← List.foldl_map, sem_assoc', List.foldr_cons, List.foldl_map, IH]

  lemma GuardedPlusCal.Statement.strong_refinement.await.{u} {mailbox} {e : Expression.{u} Typ}
    (wf : match mailbox with | .none => True | .some ⟨_, inbox⟩ => e.FreshIn inbox) :
      StrongRefinement.Aborting (· ∼[mailbox] ·)
        ⟦GuardedPlusCal.Statement.await.{u} (Typ := Typ) e⟧⊥
        ⟦NetworkPlusCal.Statement.await.{u} (Typ := Typ) e⟧⊥ := by
    rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim ⟨rfl, ⟨_, _, _, eval_e_eq_v, _|_, rfl⟩|⟨_, _, _, v, v_not_bool, eval_e_eq_v, _|_, rfl⟩⟩
      <;> exists [], le_rfl, relatesTo_eq_label sim
      <;> [ (left; use Mₛ, Tₛ, Fₛ, ?_, rfl)
          | (right; use Mₛ, Tₛ, Fₛ, v, v_not_bool, ?_, rfl) ]
      <;> {
        match mailbox with
        | .none => rwa [sim.right.left, sim.right.right.left]
        | .some (_, inbox) =>
          rw [← eval_e_eq_v]
          apply eval_ext [inbox]
          · intros v v_not_in
            rw [List.not_mem_singleton] at v_not_in
            obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
              obtain ⟨_, mem_ext, rfl, _⟩ := sim
              simp_rw [AList.lookup_union, mem_ext _ v_not_in]
            }
          · rw [List.singleton_disjoint]
            apply not_mem_of_fresh
            exact wf
    }

  theorem AtomicBranch.correctness_precond_await'
    {nameₛ : String} {mailboxₛ : Option (Expression.{0} Typ)}
    (B : Option (GuardedPlusCal.Block.{0} (NetworkPlusCal.Statement Typ (Expression Typ) true) false)) {i : Nat}
    {newInstrs : List (GuardedPlusCal.Ref.{0} Typ (Expression Typ) × Expression.{0} Typ)}
    {precondₛ : GuardedPlusCal.Block.{0} (GuardedPlusCal.Statement Typ (Expression Typ) true) false}
    {Ss Ss' : List (GuardedPlusCal.Statement.{0} Typ (Expression Typ) true false)}
    {e : Expression.{0} Typ}
    {«Σ» Γ Δ Ξ : Scope}
    {«Σ_disj_Δ» : Disjoint («Σ» \ {"self"}) (Δ \ {"self"})} {«Σ_disj_Γ» : Disjoint («Σ» \ {"self"}) (Γ \ {"self"})} {Δ_disj_Γ : Disjoint (Δ \ {"self"}) (Γ \ {"self"})}
    («prims_in_Σ» : TypedSetTheory.prims.keys.toFinset ⊆ «Σ» \ {"self"})
    (e_wellscoped : Expression.WellScoped e («Σ» \ {"self"} ∪ Γ \ {"self"} ∪ Ξ))
    (h : precondₛ.begin.concat precondₛ.last = Ss ++ GuardedPlusCal.Statement.await e :: Ss')
    (wf : match mailboxₛ with
      | none => True
      | some _ => ∀ S ∈ precondₛ.toList, GuardedPlusCal.Statement.FreshIn Expression.FreshIn S (inbox ++ nameₛ))
    (i_eq : i = newInstrs.length / 2)
    (newInstrs_len_even : Even newInstrs.length)
    (wellscoped : if h'' : !Ss.isEmpty then
      ∃ (_ : Disjoint («Σ» \ {"self"}) Ξ) (_ : Disjoint (Δ \ {"self"}) Ξ) (_ : Disjoint (Γ \ {"self"}) Ξ),
        GuardedPlusCal.AtomicBranch.WellScopedPrecond (flip Expression.WellScoped) («Σ» \ {"self"}) (Δ \ {"self"}) (Γ \ {"self"}) ‹_› ‹_› ‹_›
          (.some (GuardedPlusCal.Block.ofList Ss (propext List.isEmpty_eq_false_iff ▸ Bool.not_eq_true' _ ▸ List.isEmpty_reverse ▸ h''))) {"self"} Ξ
    else Ξ = {"self"})
    (newInstrs_shape : ∀ (k : Nat) (_ : k < newInstrs.length),
      (∀ arg ∈ newInstrs[k].1.args, ∀ idx ∈ arg, Expression.WellScoped idx ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ)) ∧
      Expression.WellScoped newInstrs[k].2 ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ) ∧
      (Even k → ∃ r τ, r.name ≠ inbox ++ nameₛ ∧ r.name ∈ Γ \ {"self"} ∧  newInstrs[k] = ⟨r ,.opcall (.var "Head" (.operator [.seq τ] τ)) [.var (inbox ++ nameₛ) (.seq τ)]⟩) ∧
      (Odd k → ∃ τ, inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ newInstrs[k] = ⟨⟨inbox ++ nameₛ, .seq τ, []⟩, .opcall (.var "Tail" (.operator [.seq τ] (.seq τ))) [.var (inbox ++ nameₛ) (.seq τ)]⟩))
    (mailbox_some : newInstrs ≠ [] → mailboxₛ.isSome)
    (inv : match (motive := _ → Prop) B with
      | .none => Ss = [] ∧ i = 0 ∧ newInstrs = []
      | .some B => StrongRefinement (· ∼[Option.map (fun x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·)
        (List.foldr (⟦·⟧* ∘ᵣ₂ ·) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} Ss)
        (List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ss)
        (List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ss)
        (⟦B⟧* ∘ᵣ₂ List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} newInstrs)
        (⟦B⟧⊥ ∪ ⟦B⟧* ∘ᵣ₁ newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) ∅)
        (⟦B⟧∞ ∪ ⟦B⟧* ∘ᵣ₁ newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧∞ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) ∅)) :
    ----
      i = newInstrs.length / 2 ∧
      Even newInstrs.length ∧
      (if h'' : !(Ss ++ [GuardedPlusCal.Statement.await e]).isEmpty then
        ∃ (_ : Disjoint («Σ» \ {"self"}) Ξ) (_ : Disjoint (Δ \ {"self"}) Ξ) (_ : Disjoint (Γ \ {"self"}) Ξ),
          GuardedPlusCal.AtomicBranch.WellScopedPrecond (flip Expression.WellScoped) («Σ» \ {"self"}) (Δ \ {"self"}) (Γ \ {"self"}) ‹_› ‹_› ‹_›
            (.some (GuardedPlusCal.Block.ofList (Ss ++ [GuardedPlusCal.Statement.await e]) (propext List.isEmpty_eq_false_iff ▸ Bool.not_eq_true' _ ▸ h''))) {"self"} Ξ
      else Ξ = {"self"}) ∧
      (∀ (k : Nat) (_ : k < newInstrs.length),
        (∀ arg ∈ newInstrs[k].1.args, ∀ idx ∈ arg, Expression.WellScoped idx ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ)) ∧
        Expression.WellScoped newInstrs[k].2 ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ) ∧
        (Even k → ∃ r τ, r.name ≠ inbox ++ nameₛ ∧ r.name ∈ Γ \ {"self"} ∧ newInstrs[k] = ⟨r ,.opcall (.var "Head" (.operator [.seq τ] τ)) [.var (inbox ++ nameₛ) (.seq τ)]⟩) ∧
        (Odd k → ∃ τ, inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ newInstrs[k] = ⟨⟨inbox ++ nameₛ, .seq τ, []⟩, .opcall (.var "Tail" (.operator [.seq τ] (.seq τ))) [.var (inbox ++ nameₛ) (.seq τ)]⟩)) ∧
      (newInstrs ≠ [] → mailboxₛ.isSome) ∧
      StrongRefinement (· ∼[Option.map (λ x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·)
        (List.foldr (⟦·⟧* ∘ᵣ₂ ·) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (Ss ++ [GuardedPlusCal.Statement.await e]))
        (List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ (Ss ++ [GuardedPlusCal.Statement.await e]))
        (List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ (Ss ++ [GuardedPlusCal.Statement.await e]))
        (B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₂
          ⟦NetworkPlusCal.Statement.await (Typ := Typ) (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧* ∘ᵣ₂
          List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} newInstrs)
        (B.elim ∅ (⟦·⟧⊥) ∪
          B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₁
            ⟦NetworkPlusCal.Statement.await (Typ := Typ) (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧⊥ ∪
          (B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₂
            ⟦NetworkPlusCal.Statement.await (Typ := Typ) (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧*) ∘ᵣ₁
            newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) ∅)
        (B.elim ∅ (⟦·⟧∞) ∪
          B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₁
            ⟦NetworkPlusCal.Statement.await (Typ := Typ) (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧∞ ∪
          (B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₂
            ⟦NetworkPlusCal.Statement.await (Typ := Typ) (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧*) ∘ᵣ₁
            newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧∞ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) ∅) := by {
    have newInstrs_shape' : ∀ r ∈ newInstrs, r.1.name ∉ TypedSetTheory.prims.{0} := by
      rw [List.forall_mem_iff_getElem]
      intros i i_le
      specialize newInstrs_shape i i_le
      obtain ⟨-, -, h₁, h₂⟩ := newInstrs_shape
      obtain h|h := Nat.even_or_odd i
      · obtain ⟨r, _, _, _, newInstrs_i_eq⟩ := h₁ h
        apply Finset.not_mem_subset «prims_in_Σ»
        apply Disjoint.notMem_of_mem_right_finset «Σ_disj_Γ»
        rwa [newInstrs_i_eq]
      · obtain ⟨_, _, newInstrs_i_eq⟩ := h₂ h
        apply Finset.not_mem_subset «prims_in_Σ»
        rwa [newInstrs_i_eq]

    have reorder_await_newInstrs :
        ⟦NetworkPlusCal.Statement.await (Typ := Typ) (List.foldr (λ x e ↦ e.replace (GuardedPlusCal.Ref.substOf x.1 x.2).1 (GuardedPlusCal.Ref.substOf x.1 x.2).2) e newInstrs)⟧* ∘ᵣ₂
          List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) {⟨x, e, y⟩ | x = y ∧ e = Trace.τ} newInstrs =
        List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) {⟨x, e, y⟩ | x = y ∧ e = Trace.τ} newInstrs ∘ᵣ₂
          ⟦NetworkPlusCal.Statement.await (Typ := Typ) e⟧* := by
      clear inv i_eq newInstrs_len_even newInstrs_shape mailbox_some
      induction newInstrs with
      | nil =>
        simp_rw [List.foldl_nil, List.foldr_nil]
        conv_rhs => apply Relation.lcomp₂.left_id_eq
        conv_lhs => apply Relation.lcomp₂.right_id_eq
      | cons newInstr newInstrs IH =>
        simp_rw [List.foldr_cons, List.foldl_cons]
        have r_name_not_in : newInstr.1.name ∉ TypedSetTheory.prims.{0} := newInstrs_shape' newInstr List.mem_cons_self

        have : List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) ({x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) newInstr.1 newInstr.2⟧*) newInstrs =
            ⟦NetworkPlusCal.Statement.assign (Typ := Typ) newInstr.1 newInstr.2⟧* ∘ᵣ₂ List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} newInstrs := by
          rw [← List.foldl_map]
          nth_rw 2 [← List.foldl_map]
          apply sem_assoc'
        erw [this, Relation.lcomp₂.assoc, ← NetworkPlusCal.Statement.reorder_await r_name_not_in, ← Relation.lcomp₂.assoc, IH, Relation.lcomp₂.assoc]

        intros r r_in
        exact newInstrs_shape' r (List.mem_cons_of_mem _ r_in)

    and_intros
    · assumption
    · assumption
    · have : (!(Ss ++ [GuardedPlusCal.Statement.await e]).isEmpty) = true := by simp
      rw [dite_cond_eq_true (eq_true this)]

      split_ifs at wellscoped with h
      · obtain ⟨_, _, _, wellscoped⟩ := wellscoped
        exists ‹_›, ‹_›, ‹_›
        --apply GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_await_cons <;> assumption
        apply GuardedPlusCal.AtomicBranch.WellScopedPrecond.append _ _ ?_ wellscoped
        · rw [GuardedPlusCal.Block.ofList_singleton]
          apply GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_await_end
          assumption
        · apply List.cons_ne_nil
      · cases wellscoped
        exists Finset.sdiff_disjoint, Finset.sdiff_disjoint, Finset.sdiff_disjoint
        rw [Bool.not_eq_true, Bool.not_eq_false', List.isEmpty_iff] at h
        subst Ss
        simp [List.nil_append, GuardedPlusCal.Block.ofList_singleton]
        apply GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_await_end
        assumption
    · assumption
    · assumption
    · have B_div_empty : B.elim (∅ : Set (_ × _)) (⟦·⟧∞) = ∅ := by
        cases B
          <;> [ rfl
              | (dsimp; erw [NetworkPlusCal.Block.div_empty]) ]

      have newInstrs_div_empty : newInstrs.foldr (init := ∅)
          (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧∞ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) = ∅ := by
        clear * -
        induction newInstrs with
        | nil =>
          rfl
        | cons S newInstrs IH =>
          rw [List.foldr_cons, IH, Relation.lcomp₁.right_empty_eq_empty, NetworkPlusCal.Statement.div_empty, Set.empty_union]

      rw [B_div_empty, Set.empty_union, newInstrs_div_empty, Relation.lcomp₁.right_empty_eq_empty, NetworkPlusCal.Statement.div_empty,
          Relation.lcomp₁.right_empty_eq_empty, Set.empty_union]
      apply StrongRefinement.ofNonDiverging
      · rw [List.foldr_map, sem_assoc, abort_assoc, reorder_await_newInstrs, Relation.lcomp₂.assoc]
        apply StrongRefinement.Terminating.Comp
        · cases B with
          | none =>
            obtain ⟨rfl, i_eq, rfl⟩ := inv
            rintro ⟨Maₜ, Faₜ, _⟩ ⟨Mbₜ, Fbₜ, _⟩ ε ⟨Maₛ, Faₛ, lₛ⟩ _ ⟨_, ε₁, ε₂, ⟨_|_, rfl⟩, _|_, rfl⟩
            left
            exists ⟨Maₛ, Faₛ, lₛ⟩
          | some B =>
            exact inv.1
        · apply AtomicBranch.correctness_precond_await
          cases mailboxₛ with
          | none => apply True.intro
          | some mailboxₛ =>
            dsimp at wf ⊢
            specialize wf (.await e) _
            · simp_all
            · assumption
      · rw [List.foldr_concat, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty, abort_assoc']

        -- reorder await
        have reorder_await_newInstrs' :
            ⟦NetworkPlusCal.Statement.await (Typ := Typ) (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧⊥ ∪
              ⟦NetworkPlusCal.Statement.await (Typ := Typ) (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧* ∘ᵣ₁
                newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) ∅ ⊆
            newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem)
              ⟦NetworkPlusCal.Statement.await (Typ := Typ) e⟧⊥ := by
          clear * - newInstrs_shape'
          induction newInstrs with
          | nil =>
            rw [List.map_nil, List.foldr_nil, List.foldr_nil, List.foldr_nil, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]
          | cons S newInstrs IH =>
            rw [List.map_cons, List.foldr_cons, List.foldr_cons, List.foldr_cons]

            trans'
            · apply Set.union_subset_union_right
              apply Relation.lcomp₁.subset_of_subset_right
              apply IH
              intros r r_in
              exact newInstrs_shape' _ (List.mem_cons_of_mem _ r_in)
            · rw [Relation.lcomp₁.right_union_eq_union, ← Relation.lcomp₁.left_lcomp₂_eq]
              conv =>
                enter [1, 2, 2, 1]
                apply NetworkPlusCal.Statement.reorder_await (newInstrs_shape' _ List.mem_cons_self) |>.symm

              rw [Relation.lcomp₁.right_union_eq_union, ← Set.union_assoc, ← Set.union_assoc, ← Relation.lcomp₁.left_lcomp₂_eq]
              apply Set.union_subset_union_left
              apply NetworkPlusCal.Statement.reorder_await'
              exact newInstrs_shape' _ List.mem_cons_self

        rw [Set.union_assoc, Relation.lcomp₁.left_lcomp₂_eq, ← Relation.lcomp₁.right_union_eq_union]

        apply StrongRefinement.Aborting.Mono le_rfl
        · apply Set.union_subset_union_right
          apply Relation.lcomp₁.subset_of_subset_right
          apply reorder_await_newInstrs'
        · conv =>
            enter [3, 2, 2]
            apply List.foldr_map (f := λ (x : _ × _) ↦ NetworkPlusCal.Statement.assign x.1 x.2)
                                (g := λ x y ↦ ⟦x⟧⊥ ∪ ⟦x⟧* ∘ᵣ₁ y)
                    |>.symm
          rw [abort_assoc', List.foldr_map, List.foldr_map, Relation.lcomp₁.right_union_eq_union, ← Set.union_assoc, ← Relation.lcomp₁.left_lcomp₂_eq]

          apply StrongRefinement.Aborting.Comp
          · cases B with
            | none =>
              obtain ⟨rfl, _, rfl⟩ := inv
              erw [List.foldr_nil, Set.empty_union, Relation.lcomp₁.right_empty_eq_empty]
              apply StrongRefinement.Aborting.Empty
            | some B =>
              exact inv.2
          · apply GuardedPlusCal.Statement.strong_refinement.await

            have wf' : match (motive := _ → Prop) mailboxₛ with
                | none => True
                | some _ => GuardedPlusCal.Statement.FreshIn Expression.FreshIn (GuardedPlusCal.Statement.await (Typ := Typ) e) (inbox ++ nameₛ) := by
              cases mailboxₛ with
              | none => apply True.intro
              | some val =>
                apply wf
                erw [GuardedPlusCal.Block.toList, h]
                exact List.mem_append_cons_self

            cases mailboxₛ with
            | none => trivial
            | some _ => exact wf'
          · cases B with
            | none =>
              obtain ⟨rfl, _, rfl⟩ := inv
              erw [List.foldr_nil, List.foldr_nil, Relation.lcomp₂.right_id_eq]
              apply StrongRefinement.Terminating.Id
            | some B =>
              convert inv.1 using 2
              rw [← List.foldr_map (f := λ x : _ × _ ↦ NetworkPlusCal.Statement.assign x.1 x.2) (g := λ x y ↦ ⟦x⟧* ∘ᵣ₂ y),
                  ← List.foldl_map (f := λ x : _ × _ ↦ NetworkPlusCal.Statement.assign x.1 x.2) (g := λ x y ↦ x ∘ᵣ₂ ⟦y⟧*),
                  foldl_red_eq_foldr_red]
  }

  lemma GuardedPlusCal.Statement.strong_refinement.let.{u} {mailbox} {name «=|∈»} {τ : Typ} {e : Expression.{u} Typ}
    (wf : match mailbox with | .none => True | .some ⟨_, inbox⟩ => inbox ≠ name ∧ e.FreshIn inbox) :
      StrongRefinement.Aborting (· ∼[mailbox] ·)
        ⟦GuardedPlusCal.Statement.let name τ «=|∈» e⟧⊥
        ⟦NetworkPlusCal.Statement.let name τ «=|∈» e⟧⊥ := by
    rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim ⟨rfl, ⟨_, _, _, eval_e, _|_, rfl⟩|⟨_, _, _, v, eval_e, _|_, rfl, h⟩⟩
    · exists [], le_rfl
      constructor
      · exact relatesTo_eq_label sim
      · left
        exists Mₛ, Tₛ, Fₛ, ?_, ?_ <;> try rfl
        match mailbox with
        | none =>
          obtain ⟨rfl, rfl, rfl, rfl⟩ := sim
          assumption
        | some (v, inbox) =>
          obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
            rw [← eval_e]
            obtain ⟨_, mem_ext, rfl, _⟩ := sim
            apply eval_ext [inbox]
            · simp_rw [List.mem_singleton]
              intros x x_neq
              simp_rw [AList.lookup_union, mem_ext _ x_neq]
            · rw [List.singleton_disjoint]
              obtain ⟨_, _⟩ := wf
              apply not_mem_of_fresh
              assumption
          }
    · exists [], le_rfl
      constructor
      · exact relatesTo_eq_label sim
      · right
        exists Mₛ, Tₛ, Fₛ, v, ?_, ?_, ?_ <;> try trivial
        match mailbox with
        | none =>
          obtain ⟨rfl, rfl, rfl, rfl⟩ := sim
          assumption
        | some (v, inbox) =>
          obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
            rw [← eval_e]
            obtain ⟨_, mem_ext, rfl, _⟩ := sim
            apply eval_ext [inbox]
            · simp_rw [List.mem_singleton]
              intros x x_neq
              simp_rw [AList.lookup_union, mem_ext _ x_neq]
            · rw [List.singleton_disjoint]
              obtain ⟨_, _⟩ := wf
              apply not_mem_of_fresh
              assumption
          }

  theorem AtomicBranch.correctness_precond_let'
    {nameₛ : String} {mailboxₛ : Option (Expression Typ)}
    (B : Option (GuardedPlusCal.Block.{0} (NetworkPlusCal.Statement Typ (Expression Typ) true) false)) {i : Nat}
    {newInstrs : List (GuardedPlusCal.Ref.{0} Typ (Expression Typ) × Expression.{0} Typ)}
    {precondₛ : GuardedPlusCal.Block.{0} (GuardedPlusCal.Statement Typ (Expression Typ) true) false}
    {Ss Ss' : List (GuardedPlusCal.Statement.{0} Typ (Expression Typ) true false)}
    {name : String} {τ : Typ} {«=|∈» : Bool} {e : Expression.{0} Typ}
    {«Σ» Γ Δ Ξ : Scope}
    {«Σ_disj_Δ» : Disjoint («Σ» \ {"self"}) (Δ \ {"self"})} {«Σ_disj_Γ» : Disjoint («Σ» \ {"self"}) (Γ \ {"self"})} {Δ_disj_Γ : Disjoint (Δ \ {"self"}) (Γ \ {"self"})}
    («prims_in_Σ» : TypedSetTheory.prims.keys.toFinset ⊆ «Σ» \ {"self"})
    (e_wellscoped : Expression.WellScoped e («Σ» \ {"self"} ∪ Γ \ {"self"} ∪ Ξ))
    (name_wellscoped : name ∉ «Σ» \ {"self"} ∪ Δ \ {"self"} ∪ Γ \ {"self"} ∪ Ξ)
    (h : precondₛ.begin.concat precondₛ.last = Ss ++ GuardedPlusCal.Statement.let name τ «=|∈» e :: Ss')
    (wf : match mailboxₛ with
      | none => True
      | some _ => ∀ S ∈ precondₛ.toList, GuardedPlusCal.Statement.FreshIn Expression.FreshIn S (inbox ++ nameₛ))
    (i_eq : i = newInstrs.length / 2)
    (newInstrs_len_even : Even newInstrs.length)
    (wellscoped : if h'' : !Ss.isEmpty then
      ∃ (_ : Disjoint («Σ» \ {"self"}) Ξ) (_ : Disjoint (Δ \ {"self"}) Ξ) (_ : Disjoint (Γ \ {"self"}) Ξ),
        GuardedPlusCal.AtomicBranch.WellScopedPrecond (flip Expression.WellScoped) («Σ» \ {"self"}) (Δ \ {"self"}) (Γ \ {"self"}) ‹_› ‹_› ‹_›
          (.some (GuardedPlusCal.Block.ofList Ss (propext List.isEmpty_eq_false_iff ▸ Bool.not_eq_true' _ ▸ List.isEmpty_reverse ▸ h''))) {"self"} Ξ
    else Ξ = {"self"})
    (newInstrs_shape : ∀ (k : Nat) (_ : k < newInstrs.length),
      (∀ arg ∈ newInstrs[k].1.args, ∀ idx ∈ arg, Expression.WellScoped idx ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ)) ∧
      Expression.WellScoped newInstrs[k].2 ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ) ∧
      (Even k → ∃ r τ, r.name ≠ inbox ++ nameₛ ∧ r.name ∈ Γ \ {"self"} ∧  newInstrs[k] = ⟨r ,.opcall (.var "Head" (.operator [.seq τ] τ)) [.var (inbox ++ nameₛ) (.seq τ)]⟩) ∧
      (Odd k → ∃ τ, inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ newInstrs[k] = ⟨⟨inbox ++ nameₛ, .seq τ, []⟩, .opcall (.var "Tail" (.operator [.seq τ] (.seq τ))) [.var (inbox ++ nameₛ) (.seq τ)]⟩))
    (mailbox_some : newInstrs ≠ [] → mailboxₛ.isSome)
    (inv : match (motive := _ → Prop) B with
      | .none => Ss = [] ∧ i = 0 ∧ newInstrs = []
      | .some B => StrongRefinement (· ∼[Option.map (fun x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·)
        (List.foldr (⟦·⟧* ∘ᵣ₂ ·) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} Ss)
        (List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ss)
        (List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ss)
        (⟦B⟧* ∘ᵣ₂ List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} newInstrs)
        (⟦B⟧⊥ ∪ ⟦B⟧* ∘ᵣ₁ newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) ∅)
        (⟦B⟧∞ ∪ ⟦B⟧* ∘ᵣ₁ newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧∞ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) ∅)) :
    ----
      i = newInstrs.length / 2 ∧
      Even newInstrs.length ∧
      (if h'' : !(Ss ++ [GuardedPlusCal.Statement.let name τ «=|∈» e]).isEmpty then
        ∃ (_ : Disjoint («Σ» \ {"self"}) (insert name Ξ)) (_ : Disjoint (Δ \ {"self"}) (insert name Ξ)) (_ : Disjoint (Γ \ {"self"}) (insert name Ξ)),
          GuardedPlusCal.AtomicBranch.WellScopedPrecond (flip Expression.WellScoped) («Σ» \ {"self"}) (Δ \ {"self"}) (Γ \ {"self"}) ‹_› ‹_› ‹_›
            (.some (GuardedPlusCal.Block.ofList (Ss ++ [GuardedPlusCal.Statement.let name τ «=|∈» e]) (propext List.isEmpty_eq_false_iff ▸ Bool.not_eq_true' _ ▸ h''))) {"self"} (insert name Ξ)
      else (insert name Ξ) = {"self"}) ∧
      (∀ (k : Nat) (_ : k < newInstrs.length),
        (∀ arg ∈ newInstrs[k].1.args, ∀ idx ∈ arg, Expression.WellScoped idx ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ insert name Ξ)) ∧
        Expression.WellScoped newInstrs[k].2 ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ insert name Ξ) ∧
        (Even k → ∃ r τ, r.name ≠ inbox ++ nameₛ ∧ r.name ∈ Γ \ {"self"} ∧ newInstrs[k] = ⟨r ,.opcall (.var "Head" (.operator [.seq τ] τ)) [.var (inbox ++ nameₛ) (.seq τ)]⟩) ∧
        (Odd k → ∃ τ, inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ newInstrs[k] = ⟨⟨inbox ++ nameₛ, .seq τ, []⟩, .opcall (.var "Tail" (.operator [.seq τ] (.seq τ))) [.var (inbox ++ nameₛ) (.seq τ)]⟩)) ∧
      (newInstrs ≠ [] → mailboxₛ.isSome) ∧
      StrongRefinement (· ∼[Option.map (λ x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·)
        (List.foldr (⟦·⟧* ∘ᵣ₂ ·) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (Ss ++ [GuardedPlusCal.Statement.let name τ «=|∈» e]))
        (List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ (Ss ++ [GuardedPlusCal.Statement.let name τ «=|∈» e]))
        (List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ (Ss ++ [GuardedPlusCal.Statement.let name τ «=|∈» e]))
        (B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₂
          ⟦NetworkPlusCal.Statement.let name τ «=|∈» (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧* ∘ᵣ₂
          List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} newInstrs)
        (B.elim ∅ (⟦·⟧⊥) ∪
          B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₁
            ⟦NetworkPlusCal.Statement.let name τ «=|∈» (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧⊥ ∪
          (B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₂
            ⟦NetworkPlusCal.Statement.let name τ «=|∈» (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧*) ∘ᵣ₁
            newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) ∅)
        (B.elim ∅ (⟦·⟧∞) ∪
          B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₁
            ⟦NetworkPlusCal.Statement.let name τ «=|∈» (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧∞ ∪
          (B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₂
            ⟦NetworkPlusCal.Statement.let name τ «=|∈» (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧*) ∘ᵣ₁
            newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧∞ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) ∅) := by {
    repeat rw [Finset.notMem_union] at name_wellscoped
    obtain ⟨⟨⟨_, _⟩, name_not_in_Γ⟩, name_not_in⟩ := name_wellscoped

    -- By wellscoped-ness, `name` may not appear in the new instructions
    have newInstrs_shape' : ∀ r ∈ newInstrs, r.1.name ∉ TypedSetTheory.prims.{0} ∧ (∀ arg ∈ r.1.args, ∀ idx ∈ arg, idx.FreshIn name) ∧ r.2.FreshIn name ∧ r.1.name ≠ name := by
      rw [List.forall_mem_iff_getElem]
      intros i i_le

      by_cases h : newInstrs = []
      · subst newInstrs
        cases i_le
      · specialize mailbox_some h
        rw [Option.isSome_iff_exists] at mailbox_some
        obtain ⟨_, rfl⟩ := mailbox_some

        have name_neq : name ≠ inbox ++ nameₛ := by
          specialize wf (.let name τ «=|∈» e) (by simp_all)
          unfold GuardedPlusCal.Statement.FreshIn at wf
          obtain ⟨_, _⟩ := wf
          symm
          assumption

        specialize newInstrs_shape i i_le
        obtain ⟨h₁, h₂, h₃, h₄⟩ := newInstrs_shape
        and_intros
        · apply Finset.not_mem_subset «prims_in_Σ»
          obtain h|h := Nat.even_or_odd i
          · apply Disjoint.notMem_of_mem_right_finset «Σ_disj_Γ»
            obtain ⟨_, _, _, name_in_Γ, newInstrs_i_eq⟩ := h₃ h
            rwa [newInstrs_i_eq]
          · obtain ⟨_, «inbox_not_in_Σ», newInstrs_i_eq⟩ := h₄ h
            rwa [newInstrs_i_eq]
        · intros arg arg_in idx idx_in
          apply fresh_of_wellscoped_of_not_mem
          · apply h₁ <;> assumption
          · repeat rw [Finset.notMem_union]
            and_intros
            · assumption
            · assumption
            · rwa [Finset.notMem_singleton]
            · assumption
        · apply fresh_of_wellscoped_of_not_mem
          · apply h₂
          · repeat rw [Finset.notMem_union]
            and_intros
            · assumption
            · assumption
            · rwa [Finset.notMem_singleton]
            · assumption
        · obtain h|h := Nat.even_or_odd i
          · obtain ⟨_, _, _, name_in_Γ, newInstrs_i_eq⟩ := h₃ h
            rw [newInstrs_i_eq]
            rw [← Finset.forall_mem_not_eq'] at name_not_in_Γ
            exact name_not_in_Γ _ name_in_Γ
          · obtain ⟨_, _, newInstrs_i_eq⟩ := h₄ h
            symm
            rwa [newInstrs_i_eq]

    have reorder_let :
        ⟦NetworkPlusCal.Statement.let name τ «=|∈» (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧* ∘ᵣ₂
          List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} newInstrs =
        List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} newInstrs ∘ᵣ₂
          ⟦NetworkPlusCal.Statement.let name τ «=|∈» e⟧* := by
      rw [List.foldr_map]

      clear inv i_eq newInstrs_len_even newInstrs_shape mailbox_some
      induction newInstrs with
      | nil =>
        simp_rw [List.foldl_nil, List.foldr_nil]
        conv_rhs => apply Relation.lcomp₂.left_id_eq
        conv_lhs => apply Relation.lcomp₂.right_id_eq
      | cons newInstr newInstrs IH =>
        simp_rw [List.foldr_cons, List.foldl_cons]

        obtain ⟨r_name_not_in, name_fresh_in_r_args, name_fresh, r_name_neq⟩ := newInstrs_shape' newInstr List.mem_cons_self

        have : List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) ({x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) newInstr.1 newInstr.2⟧*) newInstrs =
            ⟦NetworkPlusCal.Statement.assign (Typ := Typ) newInstr.1 newInstr.2⟧* ∘ᵣ₂ List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} newInstrs := by
          rw [← List.foldl_map]
          nth_rw 2 [← List.foldl_map]
          apply sem_assoc'

        erw [this, Relation.lcomp₂.assoc, ← NetworkPlusCal.Statement.reorder_let _ r_name_not_in _ _, ← Relation.lcomp₂.assoc, IH, Relation.lcomp₂.assoc]
        · intros r r_in
          exact newInstrs_shape' r (List.mem_cons_of_mem _ r_in)
        · assumption
        · assumption
        · assumption

    and_intros
    · assumption
    · assumption
    · have : (!(Ss ++ [GuardedPlusCal.Statement.let name τ «=|∈» e]).isEmpty) = true := by simp

      rw [dite_cond_eq_true (eq_true this)]
      simp only [Finset.disjoint_insert_right]
      split_ifs at wellscoped with h
      · obtain ⟨_, _, _, wellscoped⟩ := wellscoped
        exists ⟨‹_›, ‹_›⟩, ⟨‹_›, ‹_›⟩, ⟨‹_›, ‹_›⟩
        rw [Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
        apply GuardedPlusCal.AtomicBranch.WellScopedPrecond.append (Ξ' := Ξ) _ h (List.cons_ne_nil _ _) wellscoped
        · rw [GuardedPlusCal.Block.ofList_singleton]
          apply GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_let_end <;> assumption
      · rw [Bool.not_eq_true, Bool.not_eq_false', List.isEmpty_iff] at h
        subst Ss Ξ
        exists ⟨‹_›, Finset.sdiff_disjoint⟩, ⟨‹_›, Finset.sdiff_disjoint⟩, ⟨‹_›, Finset.sdiff_disjoint⟩
        simp only [List.nil_append, GuardedPlusCal.Block.ofList_singleton]
        apply GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_let_end <;> assumption
    · intros k k_lt
      obtain ⟨args_wellscoped, e_wellscoped, _, _⟩ := newInstrs_shape k k_lt

      and_intros
      · intros arg arg_in idx idx_in
        apply wellscoped_mono_of_subset (args_wellscoped _ arg_in _ idx_in)
        apply Finset.union_subset_union_right
        exact Finset.subset_insert _ _
      · apply wellscoped_mono_of_subset e_wellscoped
        apply Finset.union_subset_union_right
        exact Finset.subset_insert _ _
      · assumption
      · assumption
    · assumption
    · have B_div_empty : B.elim (∅ : Set (_ × _)) (⟦·⟧∞) = ∅ := by
        cases B
          <;> [ rfl
              | (dsimp; erw [NetworkPlusCal.Block.div_empty]) ]

      have newInstrs_div_empty : newInstrs.foldr (init := ∅)
          (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧∞ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) = ∅ := by
        clear * -
        induction newInstrs with
        | nil =>
          rfl
        | cons S newInstrs IH =>
          rw [List.foldr_cons, IH, Relation.lcomp₁.right_empty_eq_empty, NetworkPlusCal.Statement.div_empty, Set.empty_union]

      rw [B_div_empty, Set.empty_union, newInstrs_div_empty, Relation.lcomp₁.right_empty_eq_empty, NetworkPlusCal.Statement.div_empty,
          Relation.lcomp₁.right_empty_eq_empty, Set.empty_union]
      apply StrongRefinement.ofNonDiverging

      · -- reorder, then compose, then by IH and AtomicBranch.correctness_precond_let obtain correctness
        simp_rw [reorder_let, Relation.lcomp₂.assoc, sem_assoc, abort_assoc]
        apply StrongRefinement.Terminating.Comp
        · cases B with
          | none =>
            obtain ⟨rfl, _, rfl⟩ := inv
            erw [Relation.lcomp₂.left_id_eq, List.foldr_nil, List.foldr_nil, List.foldl_nil]
            apply StrongRefinement.Terminating.Id
          | some B =>
            exact inv.1
        · apply AtomicBranch.correctness_precond_let
          · cases mailboxₛ with
            | none => apply True.intro
            | some _ =>
              obtain ⟨_, _⟩ := wf (.let name τ «=|∈» e) (by simp_all)
              trivial
          · split_ifs at wellscoped
            · obtain ⟨_, _, _, wellscoped⟩ := wellscoped
              have : {"self"} ⊆ _ := GuardedPlusCal.AtomicBranch.scope_supset_of_wellscoped_precond _ wellscoped
              have := Finset.not_mem_subset this name_not_in
              rwa [Finset.notMem_singleton] at this
            · cases wellscoped
              rwa [Finset.notMem_singleton] at name_not_in
      · rw [List.foldr_concat, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty, abort_assoc']

        -- reorder let
        have reorder_let_newInstrs' :
            ⟦NetworkPlusCal.Statement.let name τ «=|∈» (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧⊥ ∪
              ⟦NetworkPlusCal.Statement.let name τ «=|∈» (List.foldr (λ x e ↦ e.replace x.1 x.2) e (List.map (λ x ↦ GuardedPlusCal.Ref.substOf x.1 x.2) newInstrs))⟧* ∘ᵣ₁
                newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) ∅ ⊆
            newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem)
              ⟦NetworkPlusCal.Statement.let name τ «=|∈» e⟧⊥ := by
          clear * - newInstrs_shape'
          induction newInstrs with
          | nil =>
            rw [List.map_nil, List.foldr_nil, List.foldr_nil, List.foldr_nil, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]
          | cons S newInstrs IH =>
            rw [List.map_cons, List.foldr_cons, List.foldr_cons, List.foldr_cons]

            trans'
            · apply Set.union_subset_union_right
              apply Relation.lcomp₁.subset_of_subset_right
              apply IH
              intros r r_in
              exact newInstrs_shape' _ (List.mem_cons_of_mem _ r_in)
            · rw [Relation.lcomp₁.right_union_eq_union, ← Relation.lcomp₁.left_lcomp₂_eq]
              obtain ⟨_, name_fresh, _, _⟩ := newInstrs_shape' _ List.mem_cons_self
              conv =>
                enter [1, 2, 2, 1]
                apply NetworkPlusCal.Statement.reorder_let ‹_› ‹_› ‹_› ‹_› |>.symm

              rw [Relation.lcomp₁.right_union_eq_union, ← Set.union_assoc, ← Set.union_assoc, ← Relation.lcomp₁.left_lcomp₂_eq]

              apply Set.union_subset_union_left
              apply NetworkPlusCal.Statement.reorder_let'
              · assumption
              · symm
                assumption
              · apply not_mem_of_fresh
                assumption
              · intros arg arg_in e e_in
                apply not_mem_of_fresh
                exact name_fresh _ arg_in _ e_in

        rw [Set.union_assoc, Relation.lcomp₁.left_lcomp₂_eq, ← Relation.lcomp₁.right_union_eq_union]

        apply StrongRefinement.Aborting.Mono le_rfl
        · apply Set.union_subset_union_right
          apply Relation.lcomp₁.subset_of_subset_right
          apply reorder_let_newInstrs'
        · conv =>
            enter [3, 2, 2]
            apply List.foldr_map (f := λ (x : _ × _) ↦ NetworkPlusCal.Statement.assign x.1 x.2)
                                (g := λ x y ↦ ⟦x⟧⊥ ∪ ⟦x⟧* ∘ᵣ₁ y)
                    |>.symm
          rw [abort_assoc', List.foldr_map, List.foldr_map, Relation.lcomp₁.right_union_eq_union, ← Set.union_assoc, ← Relation.lcomp₁.left_lcomp₂_eq]

          apply StrongRefinement.Aborting.Comp
          · cases B with
            | none =>
              obtain ⟨rfl, _, rfl⟩ := inv
              erw [List.foldr_nil, Set.empty_union, Relation.lcomp₁.right_empty_eq_empty]
              apply StrongRefinement.Aborting.Empty
            | some B =>
              exact inv.2
          · apply GuardedPlusCal.Statement.strong_refinement.let

            have wf' : match (motive := _ → Prop) mailboxₛ with
                | none => True
                | some _ => GuardedPlusCal.Statement.FreshIn Expression.FreshIn (GuardedPlusCal.Statement.let name τ «=|∈» e) (inbox ++ nameₛ) := by
              cases mailboxₛ with
              | none => apply True.intro
              | some val =>
                apply wf
                erw [GuardedPlusCal.Block.toList, h]
                exact List.mem_append_cons_self

            cases mailboxₛ with
            | none => trivial
            | some _ => exact wf'
          · cases B with
            | none =>
              obtain ⟨rfl, _, rfl⟩ := inv
              erw [List.foldr_nil, List.foldr_nil, Relation.lcomp₂.right_id_eq]
              apply StrongRefinement.Terminating.Id
            | some B =>
              convert inv.1 using 2
              rw [← List.foldr_map (f := λ x : _ × _ ↦ NetworkPlusCal.Statement.assign x.1 x.2) (g := λ x y ↦ ⟦x⟧* ∘ᵣ₂ y),
                  ← List.foldl_map (f := λ x : _ × _ ↦ NetworkPlusCal.Statement.assign x.1 x.2) (g := λ x y ↦ x ∘ᵣ₂ ⟦y⟧*),
                  foldl_red_eq_foldr_red]
  }

  theorem GuardedPlusCal.Statement.strong_refinement.receive.{u} {mailbox}
    {chan : GuardedPlusCal.ChanRef.{0} Typ (Expression Typ)}
    {ref : GuardedPlusCal.Ref.{0} Typ (Expression Typ)} {τ}
    (inbox_not_prim : inbox ∉ TypedSetTheory.prims.{u})
    (ref_name_neq : ref.name ≠ inbox)
    (inbox_fresh_in_ref_args : ∀ arg ∈ ref.args, ∀ e ∈ arg, e.FreshIn inbox)
    (wf : match mailbox with
    | Expression.var x (.channel τ) => chan = { name := x, τ := .channel τ, args := [] }
    | Expression.funcall (Expression.var x (.function .address (.channel τ))) [Expression.var "self" .address] =>
      chan = { name := x, τ := .function .address (.channel τ), args := [Expression.var "self" .address] }
    | _ => False) :
      StrongRefinement.Aborting (· ∼[some (mailbox, inbox)] ·)
        ⟦GuardedPlusCal.Statement.receive (Typ := Typ) chan ref⟧⊥
        (⟦NetworkPlusCal.Statement.await (Typ := Typ)
          (Expression.infix (Typ := Typ)
            (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int)) [Expression.var inbox (.seq τ)])
            .«>» (Expression.nat (toString 0)))⟧⊥ ∪
          ⟦NetworkPlusCal.Statement.await (Typ := Typ)
            (Expression.infix (Typ := Typ)
              (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int)) [Expression.var inbox (.seq τ)])
              .«>» (Expression.nat (toString 0)))⟧* ∘ᵣ₁
            (⟦NetworkPlusCal.Statement.assign (Typ := Typ) ref
              (Expression.opcall (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var inbox (.seq τ)])⟧⊥ ∪
              ⟦NetworkPlusCal.Statement.assign (Typ := Typ) ref
                (Expression.opcall (Typ := Typ) (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var inbox (.seq τ)])⟧* ∘ᵣ₁
                ⟦NetworkPlusCal.Statement.assign (Typ := Typ) { name := inbox, τ := .seq τ, args := [] }
                  (Expression.opcall (Typ := Typ) (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var inbox (.seq τ)])⟧⊥)) := by
    rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim
           (abort_await|⟨⟨Mᵤ, Tᵤ, Fᵤ, lᵤ⟩, ε₁, ε₂, red_await, abort_head|⟨⟨Mᵥ, Tᵥ, Fᵥ, lᵥ⟩, ε₂, ε₃, red_head, abort_tail, rfl⟩, rfl⟩)
    · -- `await Len(inbox) > 0` cannot abort
      obtain ⟨rfl, ⟨_, _, _, eval_len, _|_, rfl⟩|⟨_, _, _, v, v_not_bool, eval_len, _|_, rfl⟩⟩ := abort_await
        <;> (obtain ⟨_, _, rfl⟩|⟨_, _, _, rfl⟩ := relatesTo_mailbox_shape sim
          <;> [ obtain ⟨rfl, _, rfl, vs, lookup_inbox_Mₜ, lookup_inbox_Tₛ, _, _, _⟩ := sim
              | obtain ⟨rfl, _, rfl, vs, lookup_inbox_Mₜ, lookup_inbox_Tₛ, _, _, _, _⟩ := sim ])
      1,2:
        apply TypedSetTheory.neval_gt_spec at eval_len
        obtain eval_len|eval_0 := eval_len
        · specialize eval_len (.int vs.length) _ vs.length rfl
          · apply TypedSetTheory.eval_Len_intro (vs := vs)
            · exact TypedSetTheory.eval_Len
            · erw [TypedSetTheory.eval_var, dif_neg inbox_not_prim, AList.lookup_union_eq_some]
              refine Or.inr ⟨?_, ?_⟩
              · rwa [← AList.lookup_eq_none]
              · assumption
            · rfl
            · rfl
          · contradiction
        · specialize eval_0 (.int 0) _ 0 rfl
          · apply TypedSetTheory.eval_nat_intro
            erw [Nat.repr_toInt!]
            rfl
          · contradiction
      1,2:
        apply TypedSetTheory.eval_gt_spec at eval_len
        obtain ⟨n₁, n₂, _, _, rfl⟩ := eval_len
        specialize v_not_bool (decide (n₁ > n₂)) rfl
        contradiction
    · -- `ref := Head(inbox)` may abort
      obtain ⟨⟨_, _, _⟩, rfl, ⟨_, _, _, _|_, _|_, eval_len, rfl⟩, _|_, -⟩ := red_await
      obtain ⟨-, ((abort_head|abort_head)|abort_head)|abort_head⟩ := abort_head
      · obtain ⟨_, _, _, h, _|_, rfl⟩ := abort_head
        exists [], le_rfl, relatesTo_eq_label sim
        left; left; left; left
        use Mₛ, Tₛ, Fₛ, ?_, rfl
        obtain ref_name_not_in_Mₜ|ref_name_in_Tₜ := h
        · left
          obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
            obtain ⟨rfl, mem_ext, rfl, _⟩ := sim
            rw [AList.notMem_iff] at ref_name_not_in_Mₜ ⊢
            rw [← ref_name_not_in_Mₜ]
            apply mem_ext
            assumption
          }
        · obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
            obtain ⟨rfl, _, rfl, _⟩ := sim
            right
            assumption
          }
      · -- inbox is in Mₜ (by eval_len) ↯
        obtain ⟨_, _, _, eval_inbox, _|_, rfl⟩ := abort_head
        apply TypedSetTheory.neval_Head TypedSetTheory.eval_Head at eval_inbox
        apply (Or.resolve_left · (not_not_intro (by rfl))) at eval_inbox
        obtain ⟨e, e_eq, eval_inbox⟩ := eval_inbox
        obtain rfl := List.eq_of_mem_singleton e_eq

        apply TypedSetTheory.eval_gt_spec at eval_len
        obtain ⟨_, n, eval_len, eval_0, vs_non_empty⟩ := eval_len
        erw [TypedSetTheory.eval_nat_iff, Nat.repr_toInt!] at eval_0
        cases eval_0
        apply TypedSetTheory.eval_Len_is_int TypedSetTheory.eval_Len at eval_len
        obtain ⟨_, vs, eval_inbox', _|_⟩ := eval_len
        injection vs_non_empty with vs_non_empty
        erw [true_eq_decide_iff, gt_iff_lt, Int.ofNat_lt] at vs_non_empty
        obtain ⟨_, _, rfl⟩ := List.exists_cons_of_length_pos vs_non_empty
        -- List.exists_cons_of_length_pos

        specialize eval_inbox _ eval_inbox' _ _ rfl
        contradiction
      · obtain ⟨arg, arg_in, e, e_in, _, _, _, eval_e, _|_, rfl⟩ := abort_head
        exists [], le_rfl, relatesTo_eq_label sim
        left; left; right
        exists Mₛ, Tₛ, Fₛ, rfl, rfl, e, ?_
        · exact List.mem_flatten_of_mem arg_in e_in
        · rw [← eval_e]
          apply eval_ext [inbox]
          · intros x x_not_in
            rw [List.not_mem_singleton] at x_not_in

            obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim <;> {
              obtain ⟨rfl, mem_ext, rfl, _⟩ := sim
              rw [AList.lookup_union, AList.lookup_union, mem_ext x x_not_in]
            }
          · specialize inbox_fresh_in_ref_args _ arg_in _ e_in
            rw [List.singleton_disjoint]
            exact not_mem_of_fresh inbox_fresh_in_ref_args
      · obtain ⟨_, _, _, v, vss, eval_head, eval_args, upd, ref_name_not_in_Tₛ, _|_, rfl⟩ := abort_head

        apply TypedSetTheory.eval_Head_to_is_nonempty_seq TypedSetTheory.eval_Head at eval_head
        obtain ⟨_, _, eval_inbox, vs, rfl⟩ := eval_head

        exists [], le_rfl, relatesTo_eq_label sim

        obtain ⟨mailbox, _, rfl⟩|⟨mailbox, _, _, rfl⟩ := relatesTo_mailbox_shape sim
          <;> [ (obtain ⟨rfl, mem_ext, rfl, vs', lookup_inbox_Mₜ, lookup_inbox_Tₛ, fifos_ext, fifos_ext', lookup_mailbox⟩ := sim;
                 split at wf using h' <;> first | contradiction | (cases wf; cases h')
                 let args : List Value := [])
              | (obtain ⟨rfl, mem_ext, rfl, vs', lookup_inbox_Mₜ, lookup_inbox_Tₛ, v', _, fifos_ext, fifos_ext', lookup_mailbox⟩ := sim;
                 split at wf using _ | h' <;> first | contradiction | (cases wf; cases h')
                 let args := [v']) ]
          <;> {
            have vs'_eq : vs' = v :: vs := by
              apply TypedSetTheory.eval_gt_spec at eval_len
              obtain ⟨_, _, eval_len, _, _⟩ := eval_len
              apply TypedSetTheory.eval_Len_is_int TypedSetTheory.eval_Len at eval_len
              obtain ⟨_, vs''', eval_inbox', _⟩ := eval_len
              erw [TypedSetTheory.eval_var, dif_neg inbox_not_prim] at eval_inbox eval_inbox'
              rw [AList.lookup_union_eq_some] at eval_inbox'

              have : AList.lookup inbox Tₛ ≠ some (Value.seq vs''') := by
                simp [lookup_inbox_Tₛ]
              apply (Or.resolve_left · this) at eval_inbox'
              clear this

              obtain ⟨inbox_not_in_Tₛ, _|_⟩ := lookup_inbox_Mₜ ▸ eval_inbox'

              have : AList.lookup inbox (Tₛ ∪ Mₜ) = some (Value.seq vs') := by
                rw [← lookup_inbox_Mₜ, AList.lookup_union_right inbox_not_in_Tₛ]
              obtain _|_ := eval_inbox ▸ this
              rfl

            cases lookup_mailbox_Fₜ : AList.lookup (mailbox, args) Fₜ with
            | none =>
              left; right
              exists Mₛ, Tₛ, Fₛ, args, rfl, rfl, ?_
              · unfold args
                simp only [List.forall₂_cons, List.forall₂_nil_right_iff, and_true]
                try assumption
              · rw [lookup_mailbox, lookup_mailbox_Fₜ]
                rfl
            | some vs'' =>
              right
              exists Mₛ, Tₛ, Fₛ, vss, v, vs ++ vs'', args, rfl, rfl, ?_, ?_, ?_
              · unfold args
                simp only [List.forall₂_cons, List.forall₂_nil_right_iff, and_true]
                try assumption
              · rw [← List.forall₂_iff_forall₂_attach] at eval_args ⊢
                refine List.Forall₂.imp ?_ eval_args
                rintro ⟨arg, arg_in⟩ ⟨vs, vs_in⟩ h
                rw [← List.forall₂_iff_forall₂_attach] at h ⊢
                refine List.Forall₂.imp ?_ h
                rintro ⟨e, e_in⟩ ⟨v, v_in⟩ eval_e_eq_v
                rw [← eval_e_eq_v]
                apply eval_ext [inbox]
                · simp_rw [List.mem_singleton]
                  intros x x_neq
                  simp_rw [AList.lookup_union, mem_ext _ x_neq]
                · rw [List.singleton_disjoint]
                  specialize inbox_fresh_in_ref_args _ arg_in _ e_in
                  apply not_mem_of_fresh inbox_fresh_in_ref_args
              · unfold args
                simp_rw [lookup_mailbox, Option.bind_eq_bind, Option.bind_eq_some_iff]
                exists vs'', lookup_mailbox_Fₜ
                rw [vs'_eq, List.cons_append]
                rfl
              · unfold GuardedPlusCal.Memory.updateRef at upd ⊢
                simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff] at upd ⊢
                rw [mem_ext _ ref_name_neq]
                intros v₁ lookup_ref_name_Mₜ v₂ upd'
                specialize upd _ lookup_ref_name_Mₜ _ upd'
                contradiction
        }
    · -- `inbox := Tail(inbox)` cannot abort
      obtain ⟨⟨_, _, _⟩, rfl, ⟨_, _, _, _|_, _|_, eval_len, rfl⟩, _|_, -⟩ := red_await
      obtain ⟨⟨Mᵥ, Tᵥ, Fᵥ⟩, rfl, ⟨Mᵥ, _, _, _, v, vss, eval_head, eval_args, upd_Mₜ_ref_name, ref_name_not_in_Tₜ, _|_, _|_, rfl⟩, _|_, rfl⟩ := red_head
      apply TypedSetTheory.eval_Head_to_is_nonempty_seq TypedSetTheory.eval_Head at eval_head
      obtain ⟨_, _, eval_inbox, vs, rfl⟩ := eval_head

      have inbox_not_in_Tₜ : inbox ∉ Tₜ := by
        obtain ⟨_, _, rfl⟩|⟨_, _, _, _, rfl⟩ := relatesTo_mailbox_shape sim
          <;> [ obtain ⟨rfl, _, rfl, _, _, lookup_inbox_Tₛ, -⟩ := sim
              | obtain ⟨rfl, _, rfl, _, _, lookup_inbox_Tₛ, -⟩ := sim  ]
        all:
          rwa [AList.lookup_eq_none] at lookup_inbox_Tₛ

      have inbox_in_Mₜ : inbox ∈ Mₜ := by
        erw [TypedSetTheory.eval_var, dif_neg inbox_not_prim, AList.lookup_union_eq_some] at eval_inbox
        obtain lookup_inbox|⟨_, lookup_inbox⟩ := eval_inbox
        · replace lookup_inbox : ∃ x, AList.lookup inbox Tₜ = some x := Exists.intro _ lookup_inbox
          rw [← Option.isSome_iff_exists, AList.lookup_isSome] at lookup_inbox
          contradiction
        · rw [← AList.lookup_isSome]
          exact Option.isSome_of_mem lookup_inbox

      obtain ⟨-, ((abort_tail|abort_tail)|abort_tail)|abort_tail⟩ := abort_tail
      · obtain ⟨_, _, _, inbox_not_in_Mᵥ|_, _|_, rfl⟩ := abort_tail
        · -- inbox is in Mₜ (by eval_inbox), hence in Mᵥ ↯
          unfold GuardedPlusCal.Memory.updateRef at upd_Mₜ_ref_name
          simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Mₜ_ref_name
          obtain ⟨_, _, _, upd, _|_⟩ := upd_Mₜ_ref_name
          rw [AList.mem_insert, not_or] at inbox_not_in_Mᵥ
          obtain ⟨_, _⟩ := inbox_not_in_Mᵥ
          contradiction
        · contradiction
      · obtain ⟨_, _, _, neval_inbox, _|_, rfl⟩ := abort_tail
        -- inbox is both in Mₜ and Mᵥ, and since inbox evaluates in Tₜ ∪ Mₜ, it should in Tₜ ∪ Mᵥ ↯
        unfold GuardedPlusCal.Memory.updateRef at upd_Mₜ_ref_name
        simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at upd_Mₜ_ref_name
        obtain ⟨_, lookup_ref_Mₜ, _, upd, _|_⟩ := upd_Mₜ_ref_name
        apply TypedSetTheory.neval_Tail TypedSetTheory.eval_Tail at neval_inbox
        apply (Or.resolve_left · (not_not_intro (by rfl))) at neval_inbox
        obtain ⟨e', e'_in, neval_inbox⟩ := neval_inbox
        specialize neval_inbox (.seq (v :: vs)) _ v vs rfl
        · obtain rfl := List.eq_of_mem_singleton e'_in
          rw [← eval_inbox]
          apply eval_ext [ref.name]
          · intros x x_nin

            have : x ≠ ref.name := by rwa [@List.not_mem_singleton] at x_nin

            rw [AList.union_insert_ext_of_not_mem ref_name_not_in_Tₜ _, AList.lookup_insert_ne this]
          · rwa [List.singleton_disjoint, Expression.freeVars, List.mem_singleton]
        · nomatch neval_inbox
      · nomatch abort_tail
      · obtain ⟨_, _, _, v', vss, eval_tail, eval_args, nupd, lookup_inbox_Tₜ, _|_, rfl⟩ := abort_tail
        obtain rfl : vss = [] := by rwa [List.forall₂_nil_left_iff] at eval_args
        clear eval_args
        unfold GuardedPlusCal.Memory.updateRef at nupd
        simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff] at nupd
        apply TypedSetTheory.eval_Tail_is_seq TypedSetTheory.eval_Tail at eval_tail
        obtain ⟨_, v', vs', eval_inbox, rfl⟩ := eval_tail
        specialize nupd (.seq (v' :: vs')) _ (.seq vs') _
        · dsimp at *
          erw [TypedSetTheory.eval_var, dif_neg inbox_not_prim, AList.lookup_union_eq_some] at eval_inbox
          obtain lookup_inbox_Tₜ'|⟨_, lookup_inbox_Mᵥ⟩ := eval_inbox
          · replace lookup_inbox_Tₜ' : ∃ x, AList.lookup inbox Tₜ = some x := Exists.intro _ lookup_inbox_Tₜ'
            rw [← Option.isSome_iff_exists, AList.lookup_isSome] at lookup_inbox_Tₜ'
            contradiction
          · assumption
        · rfl
        · contradiction

  lemma append_to_concat_concat {α} {xs : List α} {x y : α} : xs ++ [x, y] = xs ++ [x] ++ [y] := by
    simp

  private theorem AtomicBranch.correctness_precond_receive'.reorder_await.{u}
    {newInstrs : List (GuardedPlusCal.Ref.{0} Typ (Expression Typ) × Expression.{0} Typ)}
    {nameₛ : String} {i : Nat} {τ}
    {«Σ» Γ Ξ : Scope}
    («Σ_disj_Γ» : Disjoint («Σ» \ {"self"}) (Γ \ {"self"}))
    («prims_in_Σ» : TypedSetTheory.prims.{u}.keys.toFinset ⊆ «Σ» \ {"self"})
    (i_eq : i = newInstrs.length / 2)
    (newInstrs_len_even : Even newInstrs.length)
    (newInstrs_shape : ∀ (k : Nat) (_ : k < newInstrs.length),
        (∀ arg ∈ newInstrs[k].1.args, ∀ idx ∈ arg, Expression.WellScoped idx ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ)) ∧
        Expression.WellScoped newInstrs[k].2 ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ) ∧
        (Even k → ∃ r τ, r.name ≠ inbox ++ nameₛ ∧ r.name ∈ Γ \ {"self"} ∧ newInstrs[k] = ⟨r ,.opcall (.var "Head" (.operator [.seq τ] τ)) [.var (inbox ++ nameₛ) (.seq τ)]⟩) ∧
        (Odd k → ∃ τ, inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ newInstrs[k] = ⟨⟨inbox ++ nameₛ, .seq τ, []⟩, .opcall (.var "Tail" (.operator [.seq τ] (.seq τ))) [.var (inbox ++ nameₛ) (.seq τ)]⟩)) :
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ) (.infix (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«+» (.nat (0 : Nat).repr)) .«>» (.nat s!"{i}"))⟧* ∘ᵣ₂
        List.foldl (λ x (r, e) ↦ x ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧*) {⟨x, e, y⟩ | x = y ∧ e = Trace.τ} newInstrs =
      List.foldl (λ x (r, e) ↦ x ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧*) {⟨x, e, y⟩ | x = y ∧ e = Trace.τ} newInstrs ∘ᵣ₂
        ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ) (.infix (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«+» (.nat (newInstrs.length / 2).repr)) .«>» (.nat s!"{i}"))⟧* := by
    conv_lhs =>
      enter [1, 1, 1, 1, 3, 1, 1]
      rw [← Nat.zero_div 2, ← List.length_nil (α := GuardedPlusCal.Ref.{0} Typ (Expression Typ) × Expression.{0} Typ)]

    generalize ys_eq : ([] : List (GuardedPlusCal.Ref.{0} Typ (Expression Typ) × Expression.{0} Typ)) = ys
    generalize xs_eq : newInstrs = xs
    have newInstrs_eq : ys ++ xs = newInstrs := by rw [← ys_eq, ← xs_eq, List.nil_append]
    have ys_len_le : ys.length / 2 ≤ i := by
      erw [i_eq, ← ys_eq, Nat.zero_div]
      apply Nat.zero_le
    have ys_len_even : Even ys.length := by rw [← ys_eq]; apply Even.zero

    conv_rhs =>
      enter [2, 1, 1, 1, 3, 1, 1]
      rw [← Nat.add_zero (xs.length / 2), ← Nat.zero_div 2, ← List.length_nil, ys_eq, ← Nat.add_zero (xs.length / 2 + ys.length / 2), ← ite_cond_eq_true 0 1 (eq_true (ys_eq ▸ Even.zero : Even ys.length))]

    repeat rw [i_eq]
    rw [i_eq] at ys_len_le
    rw [xs_eq] at newInstrs_len_even

    clear xs_eq ys_eq

    induction ys, xs, ys_len_even, newInstrs_len_even using List.zipperEvenInduction generalizing i with
    | nil ys ys_len_even =>
      erw [if_pos ys_len_even, Nat.add_zero, Nat.zero_add]
      repeat rw [List.foldl_nil]
      conv_lhs => apply Relation.lcomp₂.right_id_eq
      conv_rhs => apply Relation.lcomp₂.left_id_eq
    | cons_cons xs x y ys xs_len_even ys_len_even IH =>
      -- repeat rw [jsp₂]

      have h₁ : (xs.length + 1) / 2 = xs.length / 2 := by rw [← Nat.even_div_two xs_len_even]
      have h₂ : Even (xs ++ [x, y]).length := List.length_append ▸ Even.add xs_len_even even_two
      have h₃ {α} {zs : List α} : (zs.length + 2) / 2 = zs.length / 2 + 1 := by
        omega

      rw [if_pos h₂, Nat.add_zero, List.length_append, List.length_cons, List.length_singleton, h₃, ← Nat.add_assoc
         ] at IH

      rw [← List.foldl_map (f := λ x : _ × _ ↦ NetworkPlusCal.Statement.assign x.1 x.2) (g := λ x y ↦ x ∘ᵣ₂ ⟦y⟧*),
          List.map_cons, List.map_cons, foldl_red_eq_foldr_red,
          List.foldr_cons, List.foldr_cons,
          Relation.lcomp₂.assoc, Relation.lcomp₂.assoc, ← foldl_red_eq_foldr_red,
          List.foldl_map,
          ← Relation.lcomp₂.assoc, ← Relation.lcomp₂.assoc, ← Relation.lcomp₂.assoc, ← Relation.lcomp₂.assoc,
          if_pos xs_len_even, List.length_cons, List.length_cons, Nat.even_div_two xs_len_even, h₁, Nat.add_zero, h₃,
          Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc,
          ← IH,
          -- NetworkPlusCal.Statement.reorder_await
         ]

      · conv_rhs =>
          pattern _ ∘ᵣ₂ _ ∘ᵣ₂ _ ∘ᵣ₂ _
          rw [Relation.lcomp₂.assoc, Relation.lcomp₂.assoc]
          pattern (⟦_⟧* ∘ᵣ₂ _) ∘ᵣ₂ _
          rw [← Relation.lcomp₂.assoc]
        rw [NetworkPlusCal.Statement.reorder_await,
            Relation.lcomp₂.assoc (R₁ := ⟦_⟧*) (R₂ := ⟦_⟧*) (R₃ := ⟦_⟧*),
            NetworkPlusCal.Statement.reorder_await,
            ← Relation.lcomp₂.assoc, ← Relation.lcomp₂.assoc,
           ]
        · congr 1

          subst newInstrs
          have newInstrs_shape₁ := newInstrs_shape xs.length (by simp +arith)
          have newInstrs_shape₂ := newInstrs_shape (xs.length + 1) (by simp +arith)
          simp_rw [List.getElem_append_right Nat.le.refl, Nat.sub_self xs.length, List.getElem_cons_zero] at newInstrs_shape₁
          simp_rw [List.getElem_append_right (Nat.le.step Nat.le.refl), (by omega : xs.length.succ - xs.length = 1)] at newInstrs_shape₂

          obtain ⟨-, -, even_shape, -⟩ := newInstrs_shape₁
          obtain ⟨ref, _, _, _, name_in, rfl⟩ := even_shape xs_len_even
          obtain ⟨-, -, -, odd_shape⟩ := newInstrs_shape₂
          obtain ⟨_, _, inbox_not_in, rfl⟩ := odd_shape (Even.add_one xs_len_even)

          apply NetworkPlusCal.Statement.sem_await_congr'
          intros M

          have inbox_neq_Len : inbox ++ nameₛ ≠ "Len" := by
            rw [← Finset.notMem_singleton]
            apply Finset.not_mem_subset (t := TypedSetTheory.prims.{u}.toFinmap.keys)
            · rw [TypedSetTheory.prims_toFinmap_keys_eq, ← Finset.inter_eq_right]
              rfl
            · apply Finset.not_mem_subset «prims_in_Σ»
              assumption

          have ref_name_neq_Len : ref.name ≠ "Len" := by
            rw [← Finset.notMem_singleton]
            apply Finset.not_mem_subset (t := TypedSetTheory.prims.{u}.toFinmap.keys)
            · rw [TypedSetTheory.prims_toFinmap_keys_eq.{u}, ← Finset.inter_eq_right]
              rfl
            · apply Finset.not_mem_subset «prims_in_Σ»
              apply Disjoint.notMem_of_mem_right_finset «Σ_disj_Γ»
              assumption

          have ref_name_neq_Tail : ref.name ≠ "Tail" := by
            rw [← Finset.notMem_singleton]
            apply Finset.not_mem_subset (t := TypedSetTheory.prims.{u}.toFinmap.keys)
            · rw [TypedSetTheory.prims_toFinmap_keys_eq.{u}, ← Finset.inter_eq_right]
              rfl
            · apply Finset.not_mem_subset «prims_in_Σ»
              apply Disjoint.notMem_of_mem_right_finset «Σ_disj_Γ»
              assumption

          have ref_name_neq_inbox : ref.name ≠ inbox ++ nameₛ := ‹_›

          clear * - inbox_neq_Len ref_name_neq_Len ref_name_neq_Tail ref_name_neq_inbox

          simp_rw [TypedSetTheory.eval_gt_iff, TypedSetTheory.eval_plus_iff, TypedSetTheory.eval_nat_iff]
          iff_rintro ⟨_, n₃, ⟨n₁, n₂, len_inbox_eq, _|_, _|_⟩, _|_, h⟩ eval
          · injection h with decide_eq
            symm at decide_eq
            erw [decide_eq_true_iff, Nat.repr_toInt!, Nat.repr_toInt!,
                 List.length_append, List.length_cons, List.length_cons
                ] at decide_eq

            have n₁_pos : n₁ > 0 := by grind only
            change 0 < n₁ at n₁_pos

            apply TypedSetTheory.eval_Len_is_int TypedSetTheory.eval_Len at len_inbox_eq
            obtain ⟨_, vs, eval_inbox_eq, _|_⟩ := len_inbox_eq

            dsimp [GuardedPlusCal.Ref.substOf]
            change TypedSetTheory.eval M (Expression.replace (Expression.replace _ _ _) _ _) = _
            conv_lhs =>
              enter [2, 1]
              dsimp
              unfold Expression.replace
              unfold Expression.replace
              unfold Expression.replace
              dsimp
              erw [List.map_singleton]
              unfold Expression.replace
              dsimp
              erw [if_pos rfl, if_neg inbox_neq_Len]
            repeat unfold registerSource
            split_ifs with args_empty
              <;> dsimp
              <;> (
                conv_lhs =>
                  enter [2]
                  unfold Expression.replace
                  dsimp
                  unfold Expression.replace
                  dsimp
                  unfold Expression.replace
                  dsimp
                  repeat erw [List.map_singleton]
                  unfold Expression.replace
                  dsimp
                  unfold registerSource
                  rw [if_neg ref_name_neq_Len]
                  repeat erw [List.map_singleton]
                  unfold Expression.replace
                  dsimp
                  unfold Expression.replace
                  dsimp
                  repeat erw [List.map_singleton]
                  dsimp
                  rw [if_neg ref_name_neq_Tail, if_neg ref_name_neq_inbox]
              )
              <;> {
                simp_rw [TypedSetTheory.eval_gt_iff, TypedSetTheory.eval_nat_iff]
                exists (vs.length - 1) + (xs.length / 2 + 1), _, ?_, rfl
                · apply TypedSetTheory.eval_plus_intro
                  · erw [Int.ofNat_lt, List.length_pos_iff_exists_cons] at n₁_pos
                    obtain ⟨v', vs', rfl⟩ := n₁_pos
                    rw [List.length_cons, Int.natCast_add, Int.natCast_one, Int.add_sub_cancel]
                    apply TypedSetTheory.eval_Len_intro rfl TypedSetTheory.eval_Len
                    · apply TypedSetTheory.eval_Tail_intro v' rfl TypedSetTheory.eval_Tail
                      erwa [TypedSetTheory.eval_var_irrel_type]
                    · rfl
                  · apply TypedSetTheory.eval_nat_intro
                    erw [Nat.repr_toInt!]
                    rfl
                · congr
                  erw [true_eq_decide_iff, Nat.repr_toInt!, List.length_append, List.length_cons, List.length_cons]
                  omega
            }
          · dsimp [GuardedPlusCal.Ref.substOf] at eval
            change TypedSetTheory.eval M (Expression.replace (Expression.replace _ _ _) _ _) = _ at eval
            conv_lhs at eval =>
              enter [2, 1]
              dsimp
              unfold Expression.replace
              unfold Expression.replace
              unfold Expression.replace
              dsimp
              erw [List.map_singleton]
              unfold Expression.replace
              dsimp
              erw [if_pos rfl, if_neg inbox_neq_Len]
            repeat unfold registerSource at eval
            split_ifs at eval with args_empty
              <;> dsimp
              <;> (
                conv_lhs at eval =>
                  enter [2]
                  unfold Expression.replace
                  dsimp
                  unfold Expression.replace
                  dsimp
                  unfold Expression.replace
                  dsimp
                  repeat erw [List.map_singleton]
                  unfold Expression.replace
                  dsimp
                  unfold registerSource
                  rw [if_neg ref_name_neq_Len]
                  repeat erw [List.map_singleton]
                  unfold Expression.replace
                  dsimp
                  unfold Expression.replace
                  dsimp
                  repeat erw [List.map_singleton]
                  dsimp
                  rw [if_neg ref_name_neq_Tail, if_neg ref_name_neq_inbox]
              )
              <;> {
                simp_rw [TypedSetTheory.eval_gt_iff, TypedSetTheory.eval_plus_iff, TypedSetTheory.eval_nat_iff] at eval
                obtain ⟨_, n₃, ⟨n₁, n₂, len_tail_inbox_eq, _|_, _|_⟩, _|_, h⟩ := eval
                injection h with decide_eq
                erw [true_eq_decide_iff, Nat.repr_toInt!, Nat.repr_toInt!] at decide_eq

                apply TypedSetTheory.eval_Len_is_int TypedSetTheory.eval_Len at len_tail_inbox_eq
                obtain ⟨_, vs, eval_tail_inbox_eq, _|_⟩ := len_tail_inbox_eq
                apply TypedSetTheory.eval_Tail_is_seq TypedSetTheory.eval_Tail at eval_tail_inbox_eq
                obtain ⟨_, v', _, eval_inbox_eq, _|_⟩ := eval_tail_inbox_eq

                refine ⟨_, _, ⟨vs.length + 1, xs.length / 2, ?_, ?_, rfl⟩, rfl, ?_⟩
                · apply TypedSetTheory.eval_Len_intro
                  · apply TypedSetTheory.eval_Len
                  · erwa [TypedSetTheory.eval_var_irrel_type] at eval_inbox_eq
                  · rfl
                  · rfl
                · rw [Nat.repr_toInt!]; rfl
                · congr 1
                  symm
                  erwa [decide_eq_true_iff, Nat.repr_toInt!, Int.add_assoc, Int.add_comm 1]
            }
        · subst newInstrs
          specialize newInstrs_shape xs.length _
          · simp +arith
          · simp_rw [List.getElem_append_right Nat.le.refl, Nat.sub_self xs.length, List.getElem_cons_zero] at newInstrs_shape
            obtain ⟨_, _, even_shape, _⟩ := newInstrs_shape
            obtain ⟨_, _, _, name_in, rfl⟩ := even_shape xs_len_even

            apply Finset.not_mem_subset «prims_in_Σ»
            apply Disjoint.notMem_of_mem_right_finset «Σ_disj_Γ»
            assumption
        · subst newInstrs
          specialize newInstrs_shape (xs.length + 1) _
          · simp +arith
          · have : xs.length.succ - xs.length = 1 := by omega
            apply Even.add_one at xs_len_even

            simp_rw [List.getElem_append_right (Nat.le.step Nat.le.refl), this] at newInstrs_shape
            obtain ⟨_, _, _, odd_shape⟩ := newInstrs_shape
            obtain ⟨_, inbox_not_in, rfl⟩ := odd_shape xs_len_even

            apply Finset.not_mem_subset «prims_in_Σ»
            assumption
      · exact i_eq
      · rwa [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
      · rw [← newInstrs_eq] at ys_len_le ⊢
        rw [List.length_append, List.length_cons, List.length_cons]
        omega

  private theorem AtomicBranch.correctness_precond_receive'.reorder_await'.{u}
    {newInstrs : List (GuardedPlusCal.Ref.{0} Typ (Expression Typ) × Expression.{0} Typ)}
    {nameₛ : String} {i : Nat} {τ}
    {«Σ» Γ Ξ : Scope}
    («Σ_disj_Γ» : Disjoint («Σ» \ {"self"}) (Γ \ {"self"}))
    («prims_in_Σ» : TypedSetTheory.prims.{u}.keys.toFinset ⊆ «Σ» \ {"self"})
    (i_eq : i = newInstrs.length / 2)
    (newInstrs_len_even : Even newInstrs.length)
    (newInstrs_shape : ∀ (k : Nat) (_ : k < newInstrs.length),
        (∀ arg ∈ newInstrs[k].1.args, ∀ idx ∈ arg, Expression.WellScoped idx ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ)) ∧
        Expression.WellScoped newInstrs[k].2 ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ) ∧
        (Even k → ∃ r τ, r.name ≠ inbox ++ nameₛ ∧ r.name ∈ Γ \ {"self"} ∧ newInstrs[k] = ⟨r, .opcall (.var "Head" (.operator [.seq τ] τ)) [.var (inbox ++ nameₛ) (.seq τ)]⟩) ∧
        (Odd k → ∃ τ, inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ newInstrs[k] = ⟨⟨inbox ++ nameₛ, .seq τ, []⟩, .opcall (.var "Tail" (.operator [.seq τ] (.seq τ))) [.var (inbox ++ nameₛ) (.seq τ)]⟩)) :
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ) (.infix (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«+» (.nat (toString (0 : Nat)))) .«>» (.nat s!"{i}"))⟧⊥
        ∪ ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ) (.infix (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«+» (.nat (toString (0 : Nat)))) .«>» (.nat s!"{i}"))⟧*
        ∘ᵣ₁ List.foldr (λ x y ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ y) ∅ newInstrs ⊆
      newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem)
        ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ) (.infix (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«+» (.nat (toString (newInstrs.length / 2)))) .«>» (.nat s!"{i}"))⟧⊥ := by
    conv in (occs := *) toString 0 =>
      all: rw [← Nat.zero_div 2, ← List.length_nil (α := GuardedPlusCal.Ref.{0} Typ (Expression Typ) × Expression.{0} Typ)]

    generalize ys_eq : ([] : List (GuardedPlusCal.Ref.{0} Typ (Expression Typ) × Expression.{0} Typ)) = ys
    generalize xs_eq : newInstrs = xs
    have newInstrs_eq : ys ++ xs = newInstrs := by rw [← ys_eq, ← xs_eq, List.nil_append]
    have ys_len_le : ys.length / 2 ≤ i := by
      erw [i_eq, ← ys_eq, Nat.zero_div]
      apply Nat.zero_le
    have ys_len_even : Even ys.length := by rw [← ys_eq]; apply Even.zero

    conv in (occs := *) xs.length / 2 =>
      all: rw [← Nat.add_zero (xs.length / 2), ← Nat.zero_div 2, ← List.length_nil, ys_eq, ← Nat.add_zero (xs.length / 2 + ys.length / 2), ← ite_cond_eq_true 0 1 (eq_true (ys_eq ▸ Even.zero : Even ys.length))]

    repeat rw [i_eq]
    rw [i_eq] at ys_len_le
    rw [xs_eq] at newInstrs_len_even

    clear xs_eq ys_eq i_eq i

    induction ys, xs, ys_len_even, newInstrs_len_even using List.zipperEvenInduction with
    | nil xs even_xs_len =>
      simp_rw [List.foldr_nil, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty, if_pos even_xs_len,
               List.length_nil, Nat.zero_div, Nat.add_zero, Nat.zero_add]
      exact subset_rfl
    | cons_cons xs y₁ y₂ ys even_xs_len even_ys_len IH =>
      have ys_len_div_two_eq : (ys.length + 2) / 2 = ys.length / 2 + 1 := by
        simp +arith
      have xs_len_div_two_eq : (xs.length + 2) / 2 = xs.length / 2 + 1 := by
        simp +arith

      have even_xs_len' : Even (xs.length + 2) := Even.add even_xs_len even_two

      simp_rw [List.length_append, List.length_cons, List.length_nil, if_pos even_xs_len',
               xs_len_div_two_eq, Nat.add_zero, Nat.add_comm (xs.length / 2) 1, ← Nat.add_assoc]
        at IH

      simp_rw [List.foldr_cons, Relation.lcomp₁.right_union_eq_union, ← Set.union_assoc,
               if_pos even_xs_len, List.length_cons, ys_len_div_two_eq, Nat.add_zero]


      have y₁_eq : (xs ++ y₁ :: y₂ :: ys)[xs.length] = y₁ := by simp [List.getElem_append_right]
      have y₂_eq : (xs ++ y₁ :: y₂ :: ys)[xs.length + 1] = y₂ := by simp [List.getElem_append_right]

      simp_rw [← newInstrs_eq, List.length_append, List.length_cons] at newInstrs_shape
      have y₁_name_not_prim : y₁.1.name ∉ TypedSetTheory.prims.{u} := by
        specialize newInstrs_shape xs.length _
        · omega
        · simp_rw [y₁_eq] at newInstrs_shape
          obtain ⟨_, _, even_shape, _⟩ := newInstrs_shape
          obtain ⟨_, _, _, «name_in_Γ», rfl⟩ := even_shape even_xs_len
          apply Finset.not_mem_subset «prims_in_Σ»
          apply Disjoint.notMem_of_mem_right_finset «Σ_disj_Γ»
          assumption
      have y₂_name_not_prim : y₂.1.name ∉ TypedSetTheory.prims.{u} := by
        specialize newInstrs_shape (xs.length + 1) _
        · omega
        · simp_rw [y₂_eq] at newInstrs_shape
          obtain ⟨_, _, _, odd_shape⟩ := newInstrs_shape
          obtain ⟨_, «inbox_not_in_Σ», _, rfl⟩ := odd_shape (Even.add_one even_xs_len)
          apply Finset.not_mem_subset «prims_in_Σ»
          assumption

      conv at IH =>
        enter [2, 2]
        change ?await ⊆ List.foldr
          (λ x y ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ y)
          ⟦NetworkPlusCal.Statement.await (Typ := Typ)
              (Expression.infix (Typ := Typ)
                (.infix (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)])
                            .«+» (.nat (toString (ys.length / 2 + 1 + xs.length / 2))))
                .«>» (.nat (toString (newInstrs.length / 2))))⟧⊥
          ys

      trans'
      · apply Set.union_subset_union_right
        apply Relation.lcomp₁.subset_of_subset_right
        apply Relation.lcomp₁.subset_of_subset_right
        apply IH
        · simp only [List.append_assoc, List.cons_append, List.nil_append, newInstrs_eq]
        · rw [← newInstrs_eq, List.length_append, List.length_cons, List.length_cons]
          grind
      · simp_rw [Relation.lcomp₁.right_union_eq_union, Set.union_assoc]
        conv_rhs => repeat rw [← Relation.lcomp₁.right_union_eq_union]
        conv_rhs =>
          pattern ⟦NetworkPlusCal.Statement.assign y₂.1 y₂.2⟧⊥ ∪ _
          rw [Relation.lcomp₁.right_union_eq_union, ← Set.union_assoc]
        conv_rhs =>
          pattern ⟦NetworkPlusCal.Statement.assign y₂.1 y₂.2⟧* ∘ᵣ₁ _ ∘ᵣ₁ _
          rw [← Relation.lcomp₁.left_lcomp₂_eq]

        trans'
        · apply Set.union_subset_union_right
          apply Relation.lcomp₁.subset_of_subset_right
          apply Set.union_subset_union_left
          apply NetworkPlusCal.Statement.reorder_await' y₂_name_not_prim
        · rw [NetworkPlusCal.Statement.reorder_await y₂_name_not_prim,
              Relation.lcomp₁.left_lcomp₂_eq]
          conv_rhs =>
            pattern ⟦_⟧⊥ ∪ ⟦_⟧* ∘ᵣ₁ ⟦_⟧⊥ ∪ _
            rw [Set.union_assoc, ← Relation.lcomp₁.right_union_eq_union]
          conv_rhs =>
            rw [Relation.lcomp₁.right_union_eq_union, ← Set.union_assoc]
          conv_rhs =>
            pattern ⟦NetworkPlusCal.Statement.assign y₁.1 y₁.2⟧* ∘ᵣ₁ _ ∘ᵣ₁ _
            rw [← Relation.lcomp₁.left_lcomp₂_eq]

          trans'
          · apply Set.union_subset_union_left
            apply NetworkPlusCal.Statement.reorder_await' y₁_name_not_prim
          · rw [NetworkPlusCal.Statement.reorder_await y₁_name_not_prim,
                Relation.lcomp₁.left_lcomp₂_eq]
            simp_rw [Set.union_assoc, ← Relation.lcomp₁.right_union_eq_union]

            apply Set.union_subset_union
            · apply NetworkPlusCal.Statement.abort_await_of_imp
              intro M v v_neq_bool eval

              obtain ⟨_, _, even_shape, _⟩ := newInstrs_shape xs.length (by omega)
              obtain ⟨_, _, _, odd_shape⟩ := newInstrs_shape (xs.length + 1) (by omega)
              simp_rw [y₁_eq, y₂_eq] at even_shape odd_shape
              obtain ⟨r, _, _, _, rfl⟩ := even_shape even_xs_len
              obtain ⟨_, _, _, rfl⟩ := odd_shape (Even.add_one even_xs_len)

              dsimp [GuardedPlusCal.Ref.substOf]
              change TypedSetTheory.eval M (Expression.replace (Expression.replace _ _ _) _ _) = v

              have xs_len_le_newInstrs_len : xs.length < newInstrs.length := by grind

              have inbox_neq_Len : inbox ++ nameₛ ≠ "Len" := by
                rw [← Finset.notMem_singleton]
                apply Finset.not_mem_subset (t := TypedSetTheory.prims.{u}.toFinmap.keys)
                · rw [TypedSetTheory.prims_toFinmap_keys_eq, ← Finset.inter_eq_right]
                  rfl
                · apply Finset.not_mem_subset «prims_in_Σ»
                  assumption

              have r_name_neq_Len : r.name ≠ "Len" := by
                rw [← Finset.notMem_singleton]
                apply Finset.not_mem_subset (t := TypedSetTheory.prims.{u}.toFinmap.keys)
                · rw [TypedSetTheory.prims_toFinmap_keys_eq.{u}, ← Finset.inter_eq_right]
                  rfl
                · apply Finset.not_mem_subset «prims_in_Σ»
                  apply Disjoint.notMem_of_mem_right_finset «Σ_disj_Γ»
                  assumption

              have r_name_neq_Tail : r.name ≠ "Tail" := by
                rw [← Finset.notMem_singleton]
                apply Finset.not_mem_subset (t := TypedSetTheory.prims.{u}.toFinmap.keys)
                · rw [TypedSetTheory.prims_toFinmap_keys_eq.{u}, ← Finset.inter_eq_right]
                  rfl
                · apply Finset.not_mem_subset «prims_in_Σ»
                  apply Disjoint.notMem_of_mem_right_finset «Σ_disj_Γ»
                  assumption

              have r_name_neq_inbox : r.name ≠ inbox ++ nameₛ := ‹_›

              dsimp
              conv_lhs =>
                enter [2, 1]
                dsimp
                unfold Expression.replace
                unfold Expression.replace
                unfold Expression.replace
                dsimp
                erw [List.map_singleton]
                unfold Expression.replace
                dsimp
                erw [if_pos rfl, if_neg inbox_neq_Len]
              repeat unfold registerSource
              split_ifs with args_empty
                <;> dsimp
                <;> (
                  conv_lhs =>
                    enter [2]
                    unfold Expression.replace
                    dsimp
                    unfold Expression.replace
                    dsimp
                    unfold Expression.replace
                    dsimp
                    repeat erw [List.map_singleton]
                    unfold Expression.replace
                    dsimp
                    unfold registerSource
                    rw [if_neg r_name_neq_Len]
                    repeat erw [List.map_singleton]
                    unfold Expression.replace
                    dsimp
                    unfold Expression.replace
                    dsimp
                    repeat erw [List.map_singleton]
                    dsimp
                    rw [if_neg r_name_neq_Tail, if_neg r_name_neq_inbox]
                ) <;> {
                  obtain ⟨⟩|v := v
                  · apply TypedSetTheory.neval_gt_spec at eval
                    obtain eval|eval := eval
                    · by_cases eval_inbox : ∃ vs, M ⊢ Expression.var (inbox ++ nameₛ) (.seq τ) ⇒ .seq vs
                      · obtain ⟨vs, eval_inbox⟩ := eval_inbox
                        specialize eval (.int (vs.length + xs.length / 2)) _ _ rfl
                        · apply TypedSetTheory.eval_plus_intro
                          · apply TypedSetTheory.eval_Len_intro rfl TypedSetTheory.eval_Len
                            · exact eval_inbox
                            · rfl
                          · apply TypedSetTheory.eval_nat_intro
                            erw [Nat.repr_toInt!]
                            rfl
                        · contradiction
                      · push_neg at eval_inbox
                        apply TypedSetTheory.neval_gt_intro
                        intros v₁ v₂ eval_plus eval_nat
                        apply TypedSetTheory.eval_plus_spec at eval_plus
                        obtain ⟨n₁, n₂, eval_Len, nat, rfl⟩ := eval_plus
                        apply TypedSetTheory.eval_Len_is_int TypedSetTheory.eval_Len at eval_Len
                        obtain ⟨_, vs, eval_Tail_inbox, _|_⟩ := eval_Len
                        apply TypedSetTheory.eval_Tail_is_seq TypedSetTheory.eval_Tail at eval_Tail_inbox
                        obtain ⟨_, v', vs', eval_inbox', _|_⟩ := eval_Tail_inbox
                        nomatch eval_inbox _ (TypedSetTheory.eval_var_irrel_type ▸ eval_inbox')
                    · specialize eval (.int (newInstrs.length / 2)) _ (newInstrs.length / 2)
                      · erw [TypedSetTheory.eval_nat_iff, Nat.repr_toInt!]
                        rfl
                      · contradiction
                  · apply TypedSetTheory.eval_gt_spec at eval
                    obtain ⟨n₁, n₂, eval_Len, eval_nat, rfl⟩ := eval

                    by_cases h : n₁ > n₂
                    · specialize v_neq_bool true _
                      · congr
                        rwa [decide_eq_true_iff]
                      · contradiction
                    · specialize v_neq_bool false _
                      · congr
                        rwa [decide_eq_false_iff_not]
                      · contradiction
                }
            · apply Relation.lcomp₁.subset_of_subset_left

              have newInstrs_shape₁ := newInstrs_shape xs.length (by simp +arith)
              have newInstrs_shape₂ := newInstrs_shape (xs.length + 1) (by simp +arith)
              simp_rw [List.getElem_append_right Nat.le.refl, Nat.sub_self xs.length, List.getElem_cons_zero] at newInstrs_shape₁
              simp_rw [List.getElem_append_right (Nat.le.step Nat.le.refl), (by omega : xs.length.succ - xs.length = 1)] at newInstrs_shape₂

              obtain ⟨-, -, even_shape, -⟩ := newInstrs_shape₁
              obtain ⟨ref, _, _, name_in, rfl⟩ := even_shape even_xs_len
              obtain ⟨-, -, -, odd_shape⟩ := newInstrs_shape₂
              obtain ⟨_, inbox_not_in, rfl⟩ := odd_shape (Even.add_one even_xs_len)

              apply NetworkPlusCal.Statement.sem_await_of_imp
              intros M eval_Len_gt

              have inbox_neq_Len : inbox ++ nameₛ ≠ "Len" := by
                rw [← Finset.notMem_singleton]
                apply Finset.not_mem_subset (t := TypedSetTheory.prims.{u}.toFinmap.keys)
                · rw [TypedSetTheory.prims_toFinmap_keys_eq, ← Finset.inter_eq_right]
                  rfl
                · apply Finset.not_mem_subset «prims_in_Σ»
                  assumption

              have ref_name_neq_Len : ref.name ≠ "Len" := by
                rw [← Finset.notMem_singleton]
                apply Finset.not_mem_subset (t := TypedSetTheory.prims.{u}.toFinmap.keys)
                · rw [TypedSetTheory.prims_toFinmap_keys_eq.{u}, ← Finset.inter_eq_right]
                  rfl
                · apply Finset.not_mem_subset «prims_in_Σ»
                  apply Disjoint.notMem_of_mem_right_finset «Σ_disj_Γ»
                  assumption

              have ref_name_neq_Tail : ref.name ≠ "Tail" := by
                rw [← Finset.notMem_singleton]
                apply Finset.not_mem_subset (t := TypedSetTheory.prims.{u}.toFinmap.keys)
                · rw [TypedSetTheory.prims_toFinmap_keys_eq.{u}, ← Finset.inter_eq_right]
                  rfl
                · apply Finset.not_mem_subset «prims_in_Σ»
                  apply Disjoint.notMem_of_mem_right_finset «Σ_disj_Γ»
                  assumption

              have ref_name_neq_inbox : ref.name ≠ inbox ++ nameₛ := ‹_›

              clear * - eval_Len_gt ys_len_le inbox_neq_Len ref_name_neq_Len ref_name_neq_Tail ref_name_neq_inbox

              simp_rw [TypedSetTheory.eval_gt_iff, TypedSetTheory.eval_plus_iff, TypedSetTheory.eval_nat_iff] at eval_Len_gt
              obtain ⟨_, n₃, ⟨n₁, n₂, len_inbox_eq, _|_, _|_⟩, _|_, h⟩ := eval_Len_gt
              · injection h with decide_eq
                symm at decide_eq
                erw [decide_eq_true_iff, Nat.repr_toInt!, Nat.repr_toInt!] at decide_eq

                have n₁_pos : n₁ > 0 := by grind only
                change 0 < n₁ at n₁_pos

                apply TypedSetTheory.eval_Len_is_int TypedSetTheory.eval_Len at len_inbox_eq
                obtain ⟨_, vs, eval_inbox_eq, _|_⟩ := len_inbox_eq

                dsimp [GuardedPlusCal.Ref.substOf]
                change TypedSetTheory.eval M (Expression.replace (Expression.replace _ _ _) _ _) = _
                conv_lhs =>
                  enter [2, 1]
                  dsimp
                  unfold Expression.replace
                  unfold Expression.replace
                  unfold Expression.replace
                  dsimp
                  erw [List.map_singleton]
                  unfold Expression.replace
                  dsimp
                  erw [if_pos rfl, if_neg inbox_neq_Len]
                repeat unfold registerSource
                split_ifs with args_empty
                  <;> dsimp
                  <;> (
                    conv_lhs =>
                      enter [2]
                      unfold Expression.replace
                      dsimp
                      unfold Expression.replace
                      dsimp
                      unfold Expression.replace
                      dsimp
                      repeat erw [List.map_singleton]
                      unfold Expression.replace
                      dsimp
                      unfold registerSource
                      rw [if_neg ref_name_neq_Len]
                      repeat erw [List.map_singleton]
                      unfold Expression.replace
                      dsimp
                      unfold Expression.replace
                      dsimp
                      repeat erw [List.map_singleton]
                      dsimp
                      rw [if_neg ref_name_neq_Tail, if_neg ref_name_neq_inbox]
                  )
                  <;> {
                    simp_rw [TypedSetTheory.eval_gt_iff, TypedSetTheory.eval_nat_iff]
                    exists (vs.length - 1) + (xs.length / 2 + 1), _, ?_, rfl
                    · apply TypedSetTheory.eval_plus_intro
                      · erw [Int.ofNat_lt, List.length_pos_iff_exists_cons] at n₁_pos
                        obtain ⟨v', vs', rfl⟩ := n₁_pos
                        rw [List.length_cons, Int.natCast_add, Int.natCast_one, Int.add_sub_cancel]
                        apply TypedSetTheory.eval_Len_intro rfl TypedSetTheory.eval_Len
                        · apply TypedSetTheory.eval_Tail_intro v' rfl TypedSetTheory.eval_Tail
                          erwa [TypedSetTheory.eval_var_irrel_type]
                        · rfl
                      · apply TypedSetTheory.eval_nat_intro
                        erw [Nat.repr_toInt!, Int.natCast_add, Int.add_comm]
                        rfl
                    · congr
                      erw [true_eq_decide_iff, Nat.repr_toInt!]
                      omega
                }

  -- set_option maxHeartbeats 500000 in
  theorem AtomicBranch.correctness_precond_receive'
    {nameₛ : String} {mailboxₛ : Expression.{0} Typ}
    {precondₛ : GuardedPlusCal.Block.{0} (GuardedPlusCal.Statement Typ (Expression Typ) true) false}
    (B : Option (GuardedPlusCal.Block.{0} (NetworkPlusCal.Statement Typ (Expression Typ) true) false))
    {i : Nat} {τ}
    {newInstrs : List (GuardedPlusCal.Ref.{0} Typ (Expression Typ) × Expression.{0} Typ)}
    {Ss Ss' : List (GuardedPlusCal.Statement.{0} Typ (Expression Typ) true false)}
    {chan : GuardedPlusCal.ChanRef.{0} Typ (Expression Typ)}
    {ref : GuardedPlusCal.Ref.{0} Typ (Expression Typ)}
    {«Σ» Γ Δ Ξ : Scope}
    {«Σ_disj_Δ» : Disjoint («Σ» \ {"self"}) (Δ \ {"self"})} {«Σ_disj_Γ» : Disjoint («Σ» \ {"self"}) (Γ \ {"self"})} {Δ_disj_Γ : Disjoint (Δ \ {"self"}) (Γ \ {"self"})}
    («prims_in_Σ» : TypedSetTheory.prims.{0}.keys.toFinset ⊆ «Σ» \ {"self"})
    (h₁ : ref.name ∈ Γ \ {"self"}) (h₂ : chan.name ∈ Δ \ {"self"})
    (h₃ : ∀ idx ∈ chan.args, flip Expression.WellScoped («Σ» \ {"self"} ∪ Γ \ {"self"} ∪ Ξ) idx)
    (h₄ : ∀ arg ∈ ref.args, ∀ idx ∈ arg, flip Expression.WellScoped («Σ» \ {"self"} ∪ Γ \ {"self"} ∪ Ξ) idx)
    (h₅ : ref.name ≠ inbox ++ nameₛ)
    (h' : precondₛ.begin.concat precondₛ.last = Ss ++ GuardedPlusCal.Statement.receive chan ref :: Ss')
    (h'' : inbox ++ nameₛ ∉ «Σ» \ {"self"})
    (wf : ∀ S ∈ precondₛ.toList, GuardedPlusCal.Statement.FreshIn Expression.FreshIn S (inbox ++ nameₛ))
    (wf'' : match (motive := _ → Prop) mailboxₛ with
      | Expression.var x (.channel τ) => chan = { name := x, τ := .channel τ, args := [] }
      | Expression.funcall (Expression.var x (.function .address (.channel τ))) [Expression.var "self" .address] => chan = { name := x, τ := .function .address (.channel τ), args := [Expression.var "self" .address] }
      | _ => False)
    (newInstrs_len_even : Even newInstrs.length)
    (wellscoped : if h'' : !Ss.isEmpty then
      ∃ (_ : Disjoint («Σ» \ {"self"}) Ξ) (_ : Disjoint (Δ \ {"self"}) Ξ) (_ : Disjoint (Γ \ {"self"}) Ξ),
        GuardedPlusCal.AtomicBranch.WellScopedPrecond (flip Expression.WellScoped) («Σ» \ {"self"}) (Δ \ {"self"}) (Γ \ {"self"}) ‹_› ‹_› ‹_›
          (.some (GuardedPlusCal.Block.ofList Ss (propext List.isEmpty_eq_false_iff ▸ Bool.not_eq_true' _ ▸ h''))) {"self"} Ξ
    else Ξ = {"self"})
    (newInstrs_shape : ∀ (k : Nat) (_ : k < newInstrs.length),
      (∀ arg ∈ newInstrs[k].1.args, ∀ idx ∈ arg, Expression.WellScoped idx ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ)) ∧
      Expression.WellScoped newInstrs[k].2 ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ) ∧
      (Even k → ∃ r τ, r.name ≠ inbox ++ nameₛ ∧ r.name ∈ Γ \ {"self"} ∧ newInstrs[k] = ⟨r ,.opcall (.var "Head" (.operator [.seq τ] τ)) [.var (inbox ++ nameₛ) (.seq τ)]⟩) ∧
      (Odd k → ∃ τ, inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ newInstrs[k] = ⟨⟨inbox ++ nameₛ, .seq τ, []⟩, .opcall (.var "Tail" (.operator [.seq τ] (.seq τ))) [.var (inbox ++ nameₛ) (.seq τ)]⟩))
    (i_eq : i = newInstrs.length / 2)
    (inv : match (motive := _ → Prop) B with
      | .none => Ss = [] ∧ i = 0 ∧ newInstrs = []
      | .some B =>
        StrongRefinement
          (· ∼[.some (mailboxₛ, inbox ++ nameₛ)] ·)
          (List.foldr (⟦·⟧* ∘ᵣ₂ ·) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} Ss)
          (List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ss)
          (List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ss)
          (⟦B⟧* ∘ᵣ₂ List.foldl (λ sem (x : _ × _) ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} newInstrs)
          (⟦B⟧⊥ ∪ ⟦B⟧* ∘ᵣ₁ newInstrs.foldr (λ ⟨r, e⟩ sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧* ∘ᵣ₁ sem) ∅)
          (⟦B⟧∞ ∪ ⟦B⟧* ∘ᵣ₁ newInstrs.foldr (λ ⟨r, e⟩ sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧∞ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧* ∘ᵣ₁ sem) ∅)) :
    ----
      i + 1 = (newInstrs ++
        [(ref, Expression.opcall (Typ := Typ) (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
         ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])]).length / 2 ∧
      Even (newInstrs ++
        [(ref, Expression.opcall (Typ := Typ) (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
         ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])]).length ∧
      (if h'' : !(Ss ++ [GuardedPlusCal.Statement.receive chan ref]).isEmpty then
        ∃ (_ : Disjoint («Σ» \ {"self"}) Ξ) (_ : Disjoint (Δ \ {"self"}) Ξ) (_ : Disjoint (Γ \ {"self"}) Ξ),
          GuardedPlusCal.AtomicBranch.WellScopedPrecond (flip Expression.WellScoped) («Σ» \ {"self"}) (Δ \ {"self"}) (Γ \ {"self"}) ‹_› ‹_› ‹_›
            (.some (GuardedPlusCal.Block.ofList (Ss ++ [GuardedPlusCal.Statement.receive chan ref]) (propext List.isEmpty_eq_false_iff ▸ Bool.not_eq_true' _ ▸ h''))) {"self"} Ξ
      else Ξ = {"self"}) ∧
      (∀ (k : Nat) (_ : k < (newInstrs ++
          [(ref, Expression.opcall (Typ := Typ) (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
            ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])]).length),
        (∀ arg ∈ (newInstrs ++
          [(ref, Expression.opcall (Typ := Typ) (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
            ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])])[k].1.args, ∀ idx ∈ arg, Expression.WellScoped idx ((«Σ» \ {"self"}) ∪ (Γ \ {"self"}  ∪ {inbox ++ nameₛ}) ∪ Ξ)) ∧
        Expression.WellScoped (newInstrs ++
          [(ref, Expression.opcall (Typ := Typ) (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
            ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])])[k].2 ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ) ∧
        (Even k → ∃ r τ', r.name ≠ inbox ++ nameₛ ∧ r.name ∈ Γ \ {"self"} ∧ (newInstrs ++
          [(ref, Expression.opcall (Typ := Typ) (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
            ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])])[k] = ⟨r , .opcall (.var "Head" (.operator [.seq τ'] τ')) [.var (inbox ++ nameₛ) (.seq τ')]⟩) ∧
        (Odd k → ∃ τ', inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ (newInstrs ++
          [(ref, Expression.opcall (Typ := Typ) (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
            ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])])[k] = ⟨⟨inbox ++ nameₛ, .seq τ', []⟩, .opcall (.var "Tail" (.operator [.seq τ'] (.seq τ'))) [.var (inbox ++ nameₛ) (.seq τ')]⟩)) ∧
      ((newInstrs ++
        [(ref, Expression.opcall (Typ := Typ) (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
          ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])]) ≠ [] → (Option.some mailboxₛ).isSome) ∧
      StrongRefinement
        (· ∼[.some (mailboxₛ, inbox ++ nameₛ)] ·)
        (List.foldr (⟦·⟧* ∘ᵣ₂ ·) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (Ss ++ [GuardedPlusCal.Statement.receive chan ref]))
        (List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ (Ss ++ [GuardedPlusCal.Statement.receive chan ref]))
        (List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ (Ss ++ [GuardedPlusCal.Statement.receive chan ref]))
        (B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₂
          ⟦NetworkPlusCal.Statement.await (Typ := Typ)
            (Expression.infix (Typ := Typ)
              (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int)) [Expression.var (inbox ++ nameₛ) (.seq τ)])
              .«>»
              (Expression.nat (toString i)))⟧* ∘ᵣ₂
          List.foldl (λ sem x ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧*)
            {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ}
            (newInstrs ++
              [(ref, Expression.opcall (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
               ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])]))
        (B.elim ∅ (⟦·⟧⊥) ∪
          B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₁
            ⟦NetworkPlusCal.Statement.await (Typ := Typ)
              (Expression.infix (Typ := Typ)
                (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int)) [Expression.var (inbox ++ nameₛ) (.seq τ)])
                .«>»
                (Expression.nat (toString i)))⟧⊥ ∪
          (B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₂
            ⟦NetworkPlusCal.Statement.await (Typ := Typ)
              (Expression.infix (Typ := Typ)
                (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int)) [Expression.var (inbox ++ nameₛ) (.seq τ)])
                .«>»
                (Expression.nat (toString i)))⟧*) ∘ᵣ₁
            List.foldr (λ ⟨r, e⟩ sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧* ∘ᵣ₁ sem) ∅
              (newInstrs ++
                [(ref, Expression.opcall (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
                 ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])]))
        (B.elim ∅ (⟦·⟧∞) ∪
          B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₁
            ⟦NetworkPlusCal.Statement.await (Typ := Typ)
              (Expression.infix (Typ := Typ)
                (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int)) [Expression.var (inbox ++ nameₛ) (.seq τ)])
                .«>»
                (Expression.nat (toString i)))⟧∞ ∪
          (B.elim {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} (⟦·⟧*) ∘ᵣ₂
            ⟦NetworkPlusCal.Statement.await (Typ := Typ)
              (Expression.infix (Typ := Typ)
                (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int)) [Expression.var (inbox ++ nameₛ) (.seq τ)])
                .«>»
                (Expression.nat (toString i)))⟧*) ∘ᵣ₁
            List.foldr (λ ⟨r, e⟩ sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧∞ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧* ∘ᵣ₁ sem) ∅
              (newInstrs ++
                [(ref, Expression.opcall (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
                 ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])])) := by {
  have reorder_await' :
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ) (.infix (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«+» (.nat (0 : Nat).repr)) .«>» (.nat s!"{i}"))⟧* ∘ᵣ₂
        List.foldl (λ x (r, e) ↦ x ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧*) {⟨x, e, y⟩ | x = y ∧ e = Trace.τ} newInstrs =
      List.foldl (λ x (r, e) ↦ x ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧*) {⟨x, e, y⟩ | x = y ∧ e = Trace.τ} newInstrs ∘ᵣ₂
        ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ) (.infix (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«+» (.nat (newInstrs.length / 2).repr)) .«>» (.nat s!"{i}"))⟧* :=
    AtomicBranch.correctness_precond_receive'.reorder_await.{0} «Σ_disj_Γ» «prims_in_Σ» i_eq newInstrs_len_even newInstrs_shape

  have await_eq {i : Nat} :
      ⟦NetworkPlusCal.Statement.await.{0} (Typ := Typ) (Expression.infix (Typ := Typ) (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«>» (.nat s!"{i}"))⟧* =
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ) (.infix (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«+» (.nat (0 : Nat).repr)) .«>» (.nat s!"{i}"))⟧* := by
    apply NetworkPlusCal.Statement.sem_await_congr'
    intro M
    simp_rw [TypedSetTheory.eval_gt_iff, TypedSetTheory.eval_plus_iff, TypedSetTheory.eval_nat_iff]
    iff_rintro ⟨n₁, n₂, eval_len_inbox_eq, _|_, h⟩ ⟨_, n₃, ⟨n₁, n₂, eval_len_inbox_eq, _|_, _|_⟩, _|_, h⟩
    · refine ⟨n₁, i, ⟨n₁, 0, ?_, ?_, ?_⟩, ?_, ?_⟩
      · assumption
      · rw [Nat.repr_toInt!]; rfl
      · rw [Int.add_zero]
      · erw [Nat.repr_toInt!]
      · erwa [Nat.repr_toInt!] at h
    · refine ⟨n₁, i, ?_, ?_, ?_⟩
      · assumption
      · erw [Nat.repr_toInt!]
      · erwa [Nat.repr_toInt!, Nat.repr_toInt!, Int.add_zero] at h

  have await_eq' {i : Nat} :
      ⟦NetworkPlusCal.Statement.await.{0} (Typ := Typ) (Expression.infix (Typ := Typ) (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«>» (.nat s!"{i}"))⟧⊥ =
      ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ) (.infix (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«+» (.nat (0 : Nat).repr)) .«>» (.nat s!"{i}"))⟧⊥ := by
    apply NetworkPlusCal.Statement.abort_await_congr
    intros M
    · ext v
      simp_rw [TypedSetTheory.eval_gt_iff, TypedSetTheory.eval_plus_iff, TypedSetTheory.eval_nat_iff]
      iff_rintro ⟨n₁, n₂, eval_len_inbox_eq, _|_, h⟩ ⟨_, n₃, ⟨n₁, n₂, eval_len_inbox_eq, _|_, _|_⟩, _|_, h⟩
      · refine ⟨n₁, i, ⟨n₁, 0, ?_, ?_, ?_⟩, ?_, ?_⟩
        · assumption
        · rw [Nat.repr_toInt!]; rfl
        · rw [Int.add_zero]
        · erw [Nat.repr_toInt!]
        · erwa [Nat.repr_toInt!] at h
      · refine ⟨n₁, i, ?_, ?_, ?_⟩
        · assumption
        · erw [Nat.repr_toInt!]
        · erwa [Nat.repr_toInt!, Nat.repr_toInt!, Int.add_zero] at h

  and_intros
  · rw [i_eq, List.length_append, List.length_cons, List.length_cons, List.length_nil, Nat.add_div_right]
    apply Nat.zero_lt_succ
  · rw [List.length_append]
    apply Even.add
    · assumption
    · simp
  · have : (!(Ss ++ [GuardedPlusCal.Statement.receive chan ref]).isEmpty) = true := by simp

    rw [dite_cond_eq_true (eq_true this)]
    split_ifs at wellscoped with h''
    · obtain ⟨_, _, _, wellscoped⟩ := wellscoped
      rw [Bool.not_eq_true', List.isEmpty_eq_false_iff] at h''
      exists ‹_›, ‹_›, ‹_›
      apply GuardedPlusCal.AtomicBranch.WellScopedPrecond.append (Ξ' := Ξ) _ (propext List.reverse_ne_nil_iff.symm ▸ h'') (List.cons_ne_nil _ _) wellscoped
      rw [GuardedPlusCal.Block.ofList_singleton]
      apply GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_receive_end <;> assumption
    · cases wellscoped
      exists Finset.sdiff_disjoint, Finset.sdiff_disjoint, Finset.sdiff_disjoint
      rw [Bool.not_eq_true, Bool.not_eq_false', List.isEmpty_iff] at h''
      subst Ss
      erw [GuardedPlusCal.Block.ofList_singleton]
      apply GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_receive_end <;> assumption
  · intros k k_le

    replace k_le : k < newInstrs.length ∨ k = newInstrs.length ∨ k = newInstrs.length + 1 := by
      rw [List.length_append] at k_le
      change k < newInstrs.length + 2 at k_le
      omega

    and_intros <;> obtain k_le|rfl|rfl := k_le
    1,4,7,10,13:
      simp_rw [List.getElem_append_left k_le]
      obtain ⟨_, _, _, _⟩ := newInstrs_shape k k_le
      assumption
    1,3,5,7: simp_rw [List.getElem_append_right (Nat.le_refl _), Nat.sub_self _]
    1-4: simp_rw [List.getElem_append_right (Nat.le_add_right _ 1), Nat.add_sub_cancel_left _ _]
    · intro h
      rw [← Nat.not_even_iff_odd] at h
      contradiction
    · intro _
      exists ref, τ
    · dsimp
      unfold Expression.WellScoped
      simp_rw [List.mem_singleton, forall_eq]
      unfold Expression.WellScoped
      constructor
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply «prims_in_Σ»
        simp [TypedSetTheory.prims_keys_eq]
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_singleton_self
    · intros arg arg_in idx idx_in
      apply wellscoped_mono_of_subset (h₄ _ arg_in _ idx_in)
      apply Finset.union_subset_union_left
      apply Finset.union_subset_union_right
      apply Finset.subset_union_left
    · intro _
      exists τ
    · intro h
      rw [Nat.even_add_one] at h
      contradiction
    · dsimp
      unfold Expression.WellScoped
      simp_rw [List.mem_singleton, forall_eq]
      unfold Expression.WellScoped
      constructor
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply «prims_in_Σ»
        simp [TypedSetTheory.prims_keys_eq]
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_singleton_self
    · rintro _ (_|_)
  · intro _
    rfl
  · have B_div_empty : B.elim (∅ : Set (_ × _)) (⟦·⟧∞) = ∅ := by
      cases B
        <;> [ rfl
            | (dsimp; erw [NetworkPlusCal.Block.div_empty]) ]

    have newInstrs_div_empty : (newInstrs ++
                [(ref, Expression.opcall (Typ := Typ) (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
                 ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])]).foldr (init := ∅)
        (λ (x : _ × _) sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧∞ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem) = ∅ := by
      clear * -
      generalize (newInstrs ++
                [(ref, Expression.opcall (Typ := Typ) (Expression.var "Head" (.operator [.seq τ] τ)) [Expression.var (inbox ++ nameₛ) (.seq τ)]),
                 ({ name := inbox ++ nameₛ, τ := .seq τ, args := [] }, Expression.opcall (Expression.var "Tail" (.operator [.seq τ] (.seq τ))) [Expression.var (inbox ++ nameₛ) (.seq τ)])]) = newInstrs
      induction newInstrs with
      | nil =>
        rfl
      | cons S newInstrs IH =>
        rw [List.foldr_cons, IH, Relation.lcomp₁.right_empty_eq_empty, NetworkPlusCal.Statement.div_empty, Set.empty_union]

    rw [B_div_empty, Set.empty_union, newInstrs_div_empty, Relation.lcomp₁.right_empty_eq_empty, NetworkPlusCal.Statement.div_empty,
        Relation.lcomp₁.right_empty_eq_empty, Set.empty_union]
    apply StrongRefinement.ofNonDiverging

    · simp_rw [sem_assoc, abort_assoc]
      rw [← List.foldl_map, List.map_append, List.foldl_append, List.foldl_map, List.foldl_map, List.foldl_cons, List.foldl_cons, List.foldl_nil]
      conv =>
        enter [4, 2]
        (repeat rw [Relation.lcomp₂.assoc])
        -- conv => enter [1, 1, 1, 1, 2, 4, 2]; erw [String.append_empty, String.empty_append]
        rw [await_eq, reorder_await', i_eq]
      conv => enter [4]; (repeat rw [← Relation.lcomp₂.assoc]); rw [Relation.lcomp₂.assoc]
      apply StrongRefinement.Terminating.Comp
      · cases B with
        | none =>
          obtain ⟨rfl, i_eq, rfl⟩ := inv
          simp_rw [List.foldr_nil, List.foldl_nil]
          rintro ⟨Maₜ, Faₜ, _⟩ ⟨Mbₜ, Fbₜ, _⟩ ε ⟨Maₛ, Faₛ, lₛ⟩ _ ⟨_, ε₁, ε₂, ⟨_|_, rfl⟩, _|_, rfl⟩
          left
          exists ⟨Maₛ, Faₛ, lₛ⟩
        | some B => exact inv.1
      · -- reduce `await Len(inbox) + n > n` to `await Len(inbox) > 0`
        conv => enter [4, 1]; change ?await

        have : -- TODO: extract as lemma?
            ?await = ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ)
              (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ nameₛ) (.seq τ)]) .«>» (.nat "0"))⟧* := by
          ext ⟨⟨Ma, Fa, _⟩, _, ⟨Mb, Fb, _⟩⟩
          apply exists_congr
          rintro ⟨Mb, Fb⟩
          apply and_congr_right'
          apply and_congr_left'
          apply exists₃_congr
          intros M T F
          apply and_congr_right'
          apply and_congr_right'
          apply and_congr_left'
          rw [TypedSetTheory.eval_plus_gt_eq_gt_minus, TypedSetTheory.eval_infix_congr]
          · rfl
          · unfold TypedSetTheory.eval
            erw [Option.pure_def, Option.bind_eq_some_iff]
            exists .int (newInstrs.length / 2)
            and_intros
            · unfold TypedSetTheory.eval
              rw [Option.pure_def]
              congr
              -- change ("" ++ _ ++ "").toInt! = _
              erw [Nat.repr_toInt!]
              rfl
            · erw [Option.bind_eq_some_iff]
              exists .int (newInstrs.length / 2)
              and_intros
              · unfold TypedSetTheory.eval
                rw [Option.pure_def]
                congr
                erw [Nat.repr_toInt!]
                rfl
              · dsimp
                congr
                have : "0".toInt! = 0 := by
                  change (String.singleton '0').toInt! = 0
                  grind only [String.singleton_toInt!]
                simp [this]

        -- then prove that `await Len(inbox) > 0; ref := Head(inbox); inbox := Tail(inbox)` refines `receive(mailbox, ref)`
        rw [this]; clear this
        apply AtomicBranch.correctness_precond_receive
        · specialize wf (.receive chan ref) (by simp_all)
          assumption
        · rw [Finset.mem_sdiff, Finset.notMem_singleton] at h₁
          exact h₁.right
        · exact wf''
    · conv =>
        enter [3, 2, 2]
        conv => enter [1]; change λ x sem ↦ ⟦NetworkPlusCal.Statement.assign x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign x.1 x.2⟧* ∘ᵣ₁ sem
        rw [← List.foldr_map (f := λ x : _ × _ ↦ NetworkPlusCal.Statement.assign x.1 x.2) (g := λ x y ↦ ⟦x⟧⊥ ∪ ⟦x⟧* ∘ᵣ₁ y)]
        rw [List.map_append, List.map_cons, List.map_cons, List.map_nil, append_to_concat_concat]
        dsimp

      repeat rw [List.foldr_concat, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty, abort_assoc']
      rw [sem_assoc]
      repeat rw [List.foldr_map]
      rw [Relation.lcomp₁.left_lcomp₂_eq, Set.union_assoc, ← Relation.lcomp₁.right_union_eq_union]
      conv =>
        enter [3, 2, 2]
        repeat rw [Relation.lcomp₁.right_union_eq_union]
        rw [Relation.lcomp₁.left_lcomp₂_eq]
        repeat rw [Relation.lcomp₁.right_union_eq_union]
        repeat rw [Set.union_assoc]

      conv in ⟦_⟧* ∘ᵣ₁ _ ∘ᵣ₁ _ =>
        rw [await_eq, ← Relation.lcomp₁.left_lcomp₂_eq,
            ← List.foldr_map (f := λ x : _ × _ ↦ NetworkPlusCal.Statement.assign x.1 x.2) (g := λ x y ↦ ⟦x⟧* ∘ᵣ₂ y),
            ← foldl_red_eq_foldr_red, List.foldl_map, reorder_await', Relation.lcomp₁.left_lcomp₂_eq]
      conv in ⟦_⟧* ∘ᵣ₁ _ ∘ᵣ₁ _ ∘ᵣ₁ _ =>
        rw [await_eq, ← Relation.lcomp₁.left_lcomp₂_eq,
            ← List.foldr_map (f := λ x : _ × _ ↦ NetworkPlusCal.Statement.assign x.1 x.2) (g := λ x y ↦ ⟦x⟧* ∘ᵣ₂ y),
            ← foldl_red_eq_foldr_red, List.foldl_map, reorder_await', Relation.lcomp₁.left_lcomp₂_eq]
      repeat rw [← Set.union_assoc]

      have reorder_await_newInstrs' :
          ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ)
              (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int)) [Expression.var (inbox ++ nameₛ) (.seq τ)])
              .«>» (Expression.nat (toString i)))⟧⊥
            ∪ ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ)
                (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int)) [Expression.var (inbox ++ nameₛ) (.seq τ)])
                .«>» (Expression.nat (toString i)))⟧*
            ∘ᵣ₁ List.foldr (λ x y ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ y) ∅ newInstrs ⊆
          newInstrs.foldr (λ x sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) x.1 x.2⟧* ∘ᵣ₁ sem)
            ⟦NetworkPlusCal.Statement.await (Typ := Typ) (Expression.infix (Typ := Typ)
              (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int)) [Expression.var (inbox ++ nameₛ) (.seq τ)])
              .«>» (Expression.nat (toString (i - newInstrs.length / 2))))⟧⊥ := by
        rw [await_eq, await_eq']
        nth_rw 2 [NetworkPlusCal.Statement.abort_await_congr]
        · exact AtomicBranch.correctness_precond_receive'.reorder_await'.{0} «Σ_disj_Γ» «prims_in_Σ» i_eq newInstrs_len_even newInstrs_shape
        · intros M
          erw [i_eq, Nat.sub_self, TypedSetTheory.eval_plus_gt_eq_gt_minus]
          apply TypedSetTheory.eval_infix_congr rfl
          rw [TypedSetTheory.eval_nat_minus, Nat.sub_self]
          rfl

      -- need to reorder awaits and stuff to be able to use `inv`
      apply StrongRefinement.Aborting.Mono le_rfl
      · apply Set.union_subset_union_right
        apply Relation.lcomp₁.subset_of_subset_right
        apply Set.union_subset_union_left
        apply Set.union_subset_union_left
        apply reorder_await_newInstrs'
      · conv =>
          enter [3, 2, 2, 1, 1]
          rw [← List.foldr_map (f := λ x : _ × _ ↦ NetworkPlusCal.Statement.assign x.1 x.2) (g := λ x sem ↦ ⟦x⟧⊥ ∪ ⟦x⟧* ∘ᵣ₁ sem),
              abort_assoc', List.foldr_map, List.foldr_map]
        conv in (occs := *) List.foldl _ _ _ =>
          all:
            rw [← List.foldl_map (f := λ x : _ × _ ↦ NetworkPlusCal.Statement.assign x.1 x.2) (g := λ x y ↦ x ∘ᵣ₂ ⟦y⟧*),
                foldl_red_eq_foldr_red, List.foldr_map]
        rw [Set.union_assoc, ← Relation.lcomp₁.right_union_eq_union, Set.union_assoc, ← Relation.lcomp₁.right_union_eq_union,
            ← Relation.lcomp₁.right_union_eq_union, Relation.lcomp₁.right_union_eq_union, ← Set.union_assoc, ← Relation.lcomp₁.left_lcomp₂_eq]

        apply StrongRefinement.Aborting.Comp
        · cases B with
          | none =>
            obtain ⟨rfl, _, rfl⟩ := inv
            erw [Set.empty_union, Relation.lcomp₁.left_id_eq]
            apply StrongRefinement.Aborting.Empty
          | some B =>
            exact inv.2
        · rw [i_eq, Nat.sub_self,
              NetworkPlusCal.Statement.sem_await_congr' (e₂ := (Expression.infix
                (Expression.opcall (Expression.var "Len" (.operator [.seq τ] .int))
                  [Expression.var (inbox ++ nameₛ) (.seq τ)])
                .«>» (Expression.nat (toString 0))))]
          · apply GuardedPlusCal.Statement.strong_refinement.receive.{0}
            · apply Set.notMem_subset «prims_in_Σ»
              exact h''
            · assumption
            · rw [GuardedPlusCal.Block.toList, h'] at wf
              obtain ⟨_, _, _, _⟩ := wf _ List.mem_append_cons_self
              assumption
            · assumption
          · intros M
            simp_rw [TypedSetTheory.eval_gt_iff, TypedSetTheory.eval_plus_iff]
            iff_rintro ⟨n₁, n₂, ⟨n₃, n₄, _, h₁, _|_⟩, h₂, h₃⟩ ⟨n₁, n₂, h₁, h₂, h₃⟩
            · obtain rfl : n₂ = n₄ := by erw [h₁] at h₂; cases h₂; rfl

              exists n₃, 0, ‹_›, ?_
              · erw [TypedSetTheory.eval_nat_iff, Nat.repr_toInt!]
                rfl
              · injection h₃ with h₃
                rw [h₃]
                congr 2
                erw [gt_iff_lt, ← Int.sub_lt_iff, Int.sub_self]
            · erw [TypedSetTheory.eval_nat_iff, Nat.repr_toInt!] at h₂
              cases h₂
              exists n₁ + newInstrs.length / 2, newInstrs.length / 2, ?_, ?_
              · exists _, newInstrs.length / 2, h₁, ?_
                · erw [TypedSetTheory.eval_nat_iff, Nat.repr_toInt!]
                  rfl
                · rfl
              · erw [TypedSetTheory.eval_nat_iff, Nat.repr_toInt!]
                rfl
              · injection h₃ with h₃
                congr 1
                rw [true_eq_decide_iff] at h₃ ⊢
                apply Int.lt_add_of_pos_left
                assumption
        · cases B with
          | none =>
            obtain ⟨rfl, _, rfl⟩ := inv
            erw [Relation.lcomp₂.left_id_eq]
            apply StrongRefinement.Terminating.Id
          | some B =>
            conv in (occs := 3) List.foldr _ _ _ =>
              rw [← List.foldr_map (f := λ x : _ × _ ↦ NetworkPlusCal.Statement.assign x.1 x.2) (g := λ x y ↦ ⟦x⟧* ∘ᵣ₂ y),
                  ← foldl_red_eq_foldr_red, List.foldl_map]
            exact inv.1
  }

  set_option maxHeartbeats 500000 in
  theorem AtomicBranch.correctness_precond_spec₁
    {fifosₛ : Std.HashMap String (Typ × List (Expression Typ))}
    {nameₛ : String} {mailboxₛ : Option (Expression Typ)}
    {precondₛ : GuardedPlusCal.Block (GuardedPlusCal.Statement Typ (Expression Typ) true) false}
    {«Σ» Γ Ξ : Scope}
    (wf' : ∀ S ∈ precondₛ.toList, match S with
        -- Every `receive` does so from its mailbox (there must be one) which is well-typed.
        | .receive c _ => ∃ v, mailboxₛ = .some v ∧ match v with
          | .var x (.channel τ) => c.name = x ∧ c.τ = .channel τ ∧ c.args = [] ∧ Prod.fst <$> fifosₛ.find? c.name = .some (.channel τ)
          | .funcall (.var x (.function .address (.channel τ))) [.var "self" .address] => c.name = x ∧ c.τ = .function .address (.channel τ) ∧ c.args = [.var "self" .address] ∧ Prod.fst <$> fifosₛ.find? c.name = .some (.function .address (.channel τ))
          | _ => False
        | .await _ => True
        | .let _ _ _ _ => True)
    (inbox_fresh_in_Br : match (motive := _ → Prop) mailboxₛ with
      | .none => True
      | .some _ => inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ ∀ S ∈ precondₛ.toList, GuardedPlusCal.Statement.FreshIn Expression.FreshIn S (inbox ++ nameₛ))
    {«Σ_disj_Δ» : Disjoint («Σ» \ {"self"}) (fifosₛ.keys.toFinset \ {"self"})} {«Σ_disj_Γ» : Disjoint («Σ» \ {"self"}) (Γ \ {"self"})} {Δ_disj_Γ : Disjoint (fifosₛ.keys.toFinset \ {"self"}) (Γ \ {"self"})}
    {«Σ_disj_Ξ» : Disjoint («Σ» \ {"self"}) Ξ} {Δ_disj_Ξ : Disjoint (fifosₛ.keys.toFinset \ {"self"}) Ξ} {Γ_disj_Ξ : Disjoint (Γ \ {"self"}) Ξ}
    (precondₛ_wellscoped : GuardedPlusCal.AtomicBranch.WellScopedPrecond (flip Expression.WellScoped)
      («Σ» \ {"self"}) (fifosₛ.keys.toFinset \ {"self"}) (Γ \ {"self"}) ‹_› ‹_› ‹_› (.some precondₛ) {"self"} Ξ
      Finset.sdiff_disjoint Finset.sdiff_disjoint Finset.sdiff_disjoint «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ)
    («prims_in_Σ» : TypedSetTheory.prims.keys.toFinset ⊆ «Σ» \ {"self"}) :
      ⦃⌜True⌝⦄
      GuardedPlusCal.Thread.toNetwork.processPrecondition inbox nameₛ fifosₛ (some precondₛ)
      ⦃⇓ (B, Ssₜ, _) => ⌜match (motive := _ → Prop) B with
        | .none => False
        | .some B => StrongRefinement (· ∼[Option.map (λ x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·)
          ⟦precondₛ⟧* ⟦precondₛ⟧⊥ ⟦precondₛ⟧∞
          (⟦B⟧* ∘ᵣ₂ List.foldl (· ∘ᵣ₂ ⟦·⟧*) {(x, e, y) | x = y ∧ e = Trace.τ} Ssₜ)
          (⟦B⟧⊥ ∪ ⟦B⟧* ∘ᵣ₁ List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ssₜ)
          (⟦B⟧∞ ∪ ⟦B⟧* ∘ᵣ₁ List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ssₜ)⌝⦄ := by
    unfold GuardedPlusCal.Thread.toNetwork.processPrecondition
    mintro -

    mspec Std.Do.Spec.forIn_list (⇓ (⟨Ss, Ss', _⟩, r) => match r with
      | ⟨.none, i, newInstrs, _⟩ => ⌜Ss = [] ∧ i = 0 ∧ Ss' ≠ [] ∧ newInstrs = []⌝
      | ⟨.some B, i, newInstrs, _⟩ => ⌜∃ Ξ',
        i = newInstrs.length / 2 ∧
        Even newInstrs.length ∧
        (if h : !Ss.isEmpty then
          ∃ (_ : Disjoint («Σ» \ {"self"}) Ξ') (_ : Disjoint (fifosₛ.keys.toFinset \ {"self"}) Ξ') (_ : Disjoint (Γ \ {"self"}) Ξ'),
            GuardedPlusCal.AtomicBranch.WellScopedPrecond (flip Expression.WellScoped) («Σ» \ {"self"}) (fifosₛ.keys.toFinset \ {"self"}) (Γ \ {"self"}) ‹_› ‹_› ‹_›
              (.some (GuardedPlusCal.Block.ofList Ss (propext List.isEmpty_eq_false_iff ▸ Bool.not_eq_true' _ ▸ h))) {"self"} Ξ'
        else Ξ' = {"self"}) ∧
        (∀ (k : Nat) (_ : k < newInstrs.length),
          (∀ arg ∈ newInstrs[k].1.args, ∀ idx ∈ arg, Expression.WellScoped idx ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ')) ∧
          Expression.WellScoped newInstrs[k].2 ((«Σ» \ {"self"}) ∪ (Γ \ {"self"} ∪ {inbox ++ nameₛ}) ∪ Ξ') ∧
          (Even k → ∃ r τ, r.name ≠ inbox ++ nameₛ ∧ r.name ∈ Γ \ {"self"} ∧ newInstrs[k] = ⟨r ,.opcall (.var "Head" (.operator [.seq τ] τ)) [.var (inbox ++ nameₛ) (.seq τ)]⟩) ∧
          (Odd k → ∃ τ, inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ newInstrs[k] = ⟨⟨inbox ++ nameₛ, .seq τ, []⟩, .opcall (.var "Tail" (.operator [.seq τ] (.seq τ))) [.var (inbox ++ nameₛ) (.seq τ)]⟩)) ∧
        (newInstrs ≠ [] → mailboxₛ.isSome) ∧
        StrongRefinement (· ∼[Option.map (λ x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·)
          (Ss.foldr (⟦·⟧* ∘ᵣ₂ ·) {(x, e, y) | x = y ∧ e = Trace.τ}) (Ss.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅) (Ss.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅)
          (⟦B⟧* ∘ᵣ₂ newInstrs.foldl (λ sem ⟨r, e⟩ ↦ sem ∘ᵣ₂ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧*) {(x, e, y) | x = y ∧ e = Trace.τ})
          (⟦B⟧⊥ ∪ ⟦B⟧* ∘ᵣ₁ newInstrs.foldr (λ ⟨r, e⟩ sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧⊥ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧* ∘ᵣ₁ sem) ∅)
          (⟦B⟧∞ ∪ ⟦B⟧* ∘ᵣ₁ newInstrs.foldr (λ ⟨r, e⟩ sem ↦ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧∞ ∪ ⟦NetworkPlusCal.Statement.assign (Typ := Typ) r e⟧* ∘ᵣ₁ sem) ∅)⌝) ?step

    case pre =>
      simp

    case post.success =>
      split
      · mrename_i h
        mcases h with ⟨-, -, h, -⟩
        contradiction
      · mrename_i h
        simp_rw [GuardedPlusCal.Block.sem_eq_foldr', GuardedPlusCal.Block.abort_eq_foldr', GuardedPlusCal.Block.div_eq_foldr',
                 GuardedPlusCal.Block.toList, List.concat_eq_append, List.map_eq_map, List.foldr_concat,
                 Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]
        mpure h
        rcases h with ⟨_, _, _, _, _, _, h⟩
        mspec Std.Do.Spec.pure
        mpure_intro
        rwa [List.foldl_map, List.foldr_map, List.foldr_map]

    case step =>
      rintro Ss S Ss' h' ⟨_|⟨B⟩, i, newInstrs, rxs⟩
      · -- At the end of the block
        mintro inv
        mpure inv
        obtain ⟨rfl, i_eq, -, -, rfl⟩ := inv
        cases S
        case «let» name τ «=|∈» e =>
          mspec Std.Do.Spec.pure
          mspec Std.Do.Spec.pure
          mspec Std.Do.Spec.pure
          mpure_intro

          have h'' : precondₛ = GuardedPlusCal.Block.ofList ([] ++ GuardedPlusCal.Statement.let name τ «=|∈» e :: Ss') (by simp) := by
            apply GuardedPlusCal.Block.ofList_of_toList
            rwa [← GuardedPlusCal.Block.toList] at h'
          rw [h''] at precondₛ_wellscoped; clear h''
          obtain ⟨Ξ', Ξ'', _, _, _, _, _, _, _|_, let_wellscoped, _⟩ := GuardedPlusCal.wellscopedprecond_of_append _ precondₛ_wellscoped
          obtain ⟨_, _, _, name_not_self, e_wellscoped, rfl⟩ := GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_let_end' _ let_wellscoped

          exists {name, "self"}
          conv => enter [2, 2, 2, 2, 2, 5, 1]; apply Relation.lcomp₂.left_id_eq.symm
          conv =>
            enter [2, 2, 2, 2, 2, 6]
            conv => enter [1]; rw [GuardedPlusCal.Block.abort_end']; apply Relation.lcomp₁.left_id_eq.symm
            conv => enter [1]; apply Set.empty_union _ |>.symm
            conv => enter [2, 1]; rw [GuardedPlusCal.Block.sem_end']; apply Relation.lcomp₂.left_id_eq.symm
          conv =>
            enter [2, 2, 2, 2, 2, 7]
            conv => enter [1]; apply Relation.lcomp₁.left_id_eq.symm
            conv => enter [1]; apply Set.empty_union _ |>.symm
            conv => enter [2, 1]; apply Relation.lcomp₂.left_id_eq.symm
            conv => enter [1, 2]; rw [GuardedPlusCal.Block.div_end']
          repeat rw [GuardedPlusCal.Block.sem_end']
          rw [← Relation.lcomp₂.assoc]

          apply correctness_precond_let' (.none) «prims_in_Σ» e_wellscoped ?_ h'
          · cases mailboxₛ with
            | none => trivial
            | some _ => exact inbox_fresh_in_Br.right
          · assumption
          · apply Even.zero
          · simp
          · nofun
          · nofun
          · trivial
          · repeat rw [Finset.notMem_union]
            trivial
        case await e =>
          mspec Std.Do.Spec.pure
          mspec Std.Do.Spec.pure
          mspec Std.Do.Spec.pure
          simp_rw [GuardedPlusCal.Block.sem_end']
          mpure_intro

          have h'' : precondₛ = GuardedPlusCal.Block.ofList ([] ++ GuardedPlusCal.Statement.await e :: Ss') (by simp) := by
            apply GuardedPlusCal.Block.ofList_of_toList
            rwa [← GuardedPlusCal.Block.toList] at h'
          rw [h''] at precondₛ_wellscoped; clear h''
          obtain ⟨Ξ', Ξ'', _, _, _, _, _, _, _|_, await_wellscoped, _⟩ := GuardedPlusCal.wellscopedprecond_of_append _ precondₛ_wellscoped
          obtain ⟨e_wellscoped, rfl⟩ := GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_await_end' _ await_wellscoped

          exists {"self"}
          conv => enter [2, 2, 2, 2, 2, 5, 1]; apply Relation.lcomp₂.left_id_eq.symm
          conv =>
            enter [2, 2, 2, 2, 2, 6]
            conv => enter [1]; apply Relation.lcomp₁.left_id_eq.symm
            conv => enter [1]; apply Set.empty_union _ |>.symm
            conv => enter [2, 1]; apply Relation.lcomp₂.left_id_eq.symm
            conv => enter [1, 2]; rw [GuardedPlusCal.Block.abort_end']
          conv =>
            enter [2, 2, 2, 2, 2, 7]
            conv => enter [1]; apply Relation.lcomp₁.left_id_eq.symm
            conv => enter [1]; apply Set.empty_union _ |>.symm
            conv => enter [2, 1]; apply Relation.lcomp₂.left_id_eq.symm
            conv => enter [1, 2]; rw [GuardedPlusCal.Block.div_end']
          rw [← Relation.lcomp₂.assoc]

          apply correctness_precond_await' (.none) «prims_in_Σ» e_wellscoped h'
          · cases mailboxₛ with
            | none => apply True.intro
            | some _ => exact inbox_fresh_in_Br.right
          · assumption
          · apply Even.zero
          · rfl
          · nofun
          · nofun
          · trivial
        case receive chan ref =>
          conv => simp_match
          obtain ⟨e, rfl, h⟩ := wf' (.receive chan ref) (by simp_all)

          obtain ⟨«inbox_not_in_Σ», h''⟩ := inbox_fresh_in_Br
          obtain ⟨_, _, _, _⟩ := h'' (.receive chan ref) (by simp_all)

          have h''' : precondₛ = GuardedPlusCal.Block.ofList ([] ++ GuardedPlusCal.Statement.receive chan ref :: Ss') (by simp) := by
            apply GuardedPlusCal.Block.ofList_of_toList
            rwa [GuardedPlusCal.Block.toList]
          rw [h'''] at precondₛ_wellscoped; clear h'''
          obtain ⟨Ξ'', Ξ''', _, _, _, _, _, _, h''', receive_wellscoped, _⟩ := GuardedPlusCal.wellscopedprecond_of_append _ precondₛ_wellscoped
          obtain ⟨ref_name_in, chan_name_in, _, _, rfl⟩ := GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_receive_end' _ receive_wellscoped
          cases h'''

          --obtain ⟨wf'', wf''', e, rfl, h⟩ := wf' (.receive pos chan ref) (by simp_all)
          split at h using e x | e x | _ <;> [
            (obtain ⟨rfl, chan_τ_eq, chan_args_eq, h⟩ := h; rw [h]) ;
            (obtain ⟨rfl, chan_τ_eq, chan_args_eq, h⟩ := h; rw [h]) ;
            contradiction
          ]

          all:
            mspec Std.Do.Spec.pure
            mspec Std.Do.Spec.pure
            mspec Std.Do.Spec.pure
            simp_rw [GuardedPlusCal.Block.sem_end']
            mpure_intro

            exists {"self"}
            conv => enter [2, 2, 2, 2, 2, 5, 1]; apply Relation.lcomp₂.left_id_eq.symm
            conv =>
              enter [2, 2, 2, 2, 2, 6]
              conv => enter [1]; apply Relation.lcomp₁.left_id_eq.symm
              conv => enter [1]; apply Set.empty_union _ |>.symm
              conv => enter [2, 1]; apply Relation.lcomp₂.left_id_eq.symm
              conv => enter [1, 2]; rw [GuardedPlusCal.Block.abort_end']
            conv =>
              enter [2, 2, 2, 2, 2, 7]
              conv => enter [1]; apply Relation.lcomp₁.left_id_eq.symm
              conv => enter [1]; apply Set.empty_union _ |>.symm
              conv => enter [2, 1]; apply Relation.lcomp₂.left_id_eq.symm
              conv => enter [1, 2]; rw [GuardedPlusCal.Block.div_end']
            rw [← Relation.lcomp₂.assoc]

            apply AtomicBranch.correctness_precond_receive' .none
            1-9,14: assumption
            · conv => simp_match
              erw [← chan_args_eq, ← chan_τ_eq]
            · apply Even.zero
            · rfl
            · rintro _ (_|_)
            · trivial

      · -- In the middle of the block
        conv_lhs => dsimp
        mintro inv
        mpure inv
        obtain ⟨Ξ', i_eq, newInstrs_len_even, wellscoped, newInstrs_shape, mailbox_some, inv⟩ := inv
        cases S --<;> mwp
        case «let» name τ «=|∈» e =>
          mspec Std.Do.Spec.pure
          mspec Std.Do.Spec.pure
          mspec Std.Do.Spec.pure
          simp_rw [GuardedPlusCal.Block.sem_concat']
          mpure_intro

          have h'' : precondₛ = GuardedPlusCal.Block.ofList (Ss ++ GuardedPlusCal.Statement.let name τ «=|∈» e :: Ss') (by simp) := by
            apply GuardedPlusCal.Block.ofList_of_toList
            rwa [← GuardedPlusCal.Block.toList] at h'
          rw [h''] at precondₛ_wellscoped; clear h''
          obtain ⟨Ξ, _, _, _, _, _, _, _, h, let_wellscoped, _⟩ := GuardedPlusCal.wellscopedprecond_of_append _ precondₛ_wellscoped
          obtain ⟨_, _, name_not_in_Γ, name_not_in, e_wellscoped, rfl⟩ := GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_let_end' _ let_wellscoped

          have : Ξ = Ξ' := by
            split_ifs at wellscoped h
            · obtain ⟨_, _, _, wellscoped⟩ := wellscoped
              apply GuardedPlusCal.AtomicBranch.WellScopedPrecond_det
              · exact h
              · exact wellscoped
            · subst Ξ Ξ'
              rfl
          subst Ξ'

          exists insert name Ξ

          conv => enter [2, 2, 2, 2, 2, 6, 1]; apply GuardedPlusCal.Block.abort_concat'
          conv => enter [2, 2, 2, 2, 2, 7, 1]; apply GuardedPlusCal.Block.div_concat'
          rw [← Relation.lcomp₂.assoc]

          apply correctness_precond_let' (.some B) «prims_in_Σ» e_wellscoped ?_ h'
          2-7: assumption
          · cases mailboxₛ with
            | none => apply True.intro
            | some _ => exact inbox_fresh_in_Br.right
          · repeat rw [Finset.notMem_union]
            trivial
        case await e =>
          mspec Std.Do.Spec.pure
          mspec Std.Do.Spec.pure
          mspec Std.Do.Spec.pure
          simp_rw [GuardedPlusCal.Block.sem_concat']
          mpure_intro

          have h'' : precondₛ = GuardedPlusCal.Block.ofList (Ss ++ GuardedPlusCal.Statement.await e :: Ss') (by simp) := by
            apply GuardedPlusCal.Block.ofList_of_toList
            rwa [GuardedPlusCal.Block.toList]
          rw [h''] at precondₛ_wellscoped; clear h''
          obtain ⟨Ξ'', Ξ''', _, _, _, _, _, _, h'', await_wellscoped, _⟩ := GuardedPlusCal.wellscopedprecond_of_append _ precondₛ_wellscoped
          obtain ⟨e_wellscoped, rfl⟩ := GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_await_end' _ await_wellscoped

          have : Ξ' = Ξ''' := by
            split_ifs at wellscoped h''
            · obtain ⟨_, _, _, wellscoped⟩ := wellscoped
              obtain rfl := GuardedPlusCal.AtomicBranch.WellScopedPrecond_det _ wellscoped h''
              rfl
            · subst Ξ' Ξ'''
              rfl
          subst Ξ'

          exists Ξ'''

          conv => enter [2, 2, 2, 2, 2, 6, 1]; apply GuardedPlusCal.Block.abort_concat'
          conv => enter [2, 2, 2, 2, 2, 7, 1]; apply GuardedPlusCal.Block.div_concat'
          rw [← Relation.lcomp₂.assoc]

          apply correctness_precond_await' (.some B) «prims_in_Σ» e_wellscoped h'
          2-7: assumption
          · cases mailboxₛ with
            | none => apply True.intro
            | some _ => exact inbox_fresh_in_Br.right
        case receive chan ref =>
          conv => simp_match
          obtain ⟨e, rfl, h⟩ := wf' (.receive chan ref) (by simp_all)

          obtain ⟨«inbox_not_in_Σ», h''⟩ := inbox_fresh_in_Br
          obtain ⟨_, _, _, _⟩ := h'' (.receive chan ref) (by simp_all)

          have h''' : precondₛ = GuardedPlusCal.Block.ofList (Ss ++ GuardedPlusCal.Statement.receive chan ref :: Ss') (by simp) := by
            apply GuardedPlusCal.Block.ofList_of_toList
            rwa [GuardedPlusCal.Block.toList]
          rw [h'''] at precondₛ_wellscoped; clear h'''
          obtain ⟨Ξ'', Ξ''', _, _, _, _, _, _, h''', receive_wellscoped, _⟩ := GuardedPlusCal.wellscopedprecond_of_append _ precondₛ_wellscoped
          obtain ⟨ref_name_in, chan_name_in, _, _, rfl⟩ := GuardedPlusCal.AtomicBranch.WellScopedPrecond.some_receive_end' _ receive_wellscoped

          have : Ξ' = Ξ''' := by
            split_ifs at wellscoped h'''
            · obtain ⟨_, _, _, wellscoped⟩ := wellscoped
              obtain rfl := GuardedPlusCal.AtomicBranch.WellScopedPrecond_det _ wellscoped h'''
              rfl
            · subst Ξ' Ξ'''
              rfl
          subst Ξ'''

          split at h using e pos₁ x | e pos₁ pos₂ x pos₃ | _ <;> [
            (obtain ⟨rfl, chan_τ_eq, chan_args_eq, h⟩ := h; rw [h]) ;
            (obtain ⟨rfl, chan_τ_eq, chan_args_eq, h⟩ := h; rw [h]) ;
            contradiction
          ]

          all:
            mspec Std.Do.Spec.pure
            mspec Std.Do.Spec.pure
            mspec Std.Do.Spec.pure
            simp_rw [GuardedPlusCal.Block.sem_concat']
            mpure_intro

            exists Ξ'

            conv => enter [2, 2, 2, 2, 2, 6, 1]; apply GuardedPlusCal.Block.abort_concat'
            conv => enter [2, 2, 2, 2, 2, 7, 1]; apply GuardedPlusCal.Block.div_concat'
            rw [← Relation.lcomp₂.assoc]

            apply AtomicBranch.correctness_precond_receive' (.some B)
            1-9,11-15:  assumption
            · conv => simp_match
              erw [← chan_args_eq, ← chan_τ_eq]

  theorem AtomicBranch.correctness_precond_spec₂
    {fifosₛ : Std.HashMap String (Typ × List (Expression Typ))}
    {nameₛ : String} :
      ⦃⌜True⌝⦄
      GuardedPlusCal.Thread.toNetwork.processPrecondition inbox nameₛ fifosₛ .none
      ⦃⇓ (B, Ssₜ, _) => ⌜B = .none ∧ Ssₜ = []⌝⦄ := by
    mintro -
    mspec GuardedPlusCal.Thread.toNetwork.processPrecondition_spec₂
    mrename_i h
    mpure h
    mpure_intro
    split at h
    · obtain ⟨h, _⟩ := h
      trivial
    · contradiction

  theorem AtomicBranch.correctness_precond_spec
    {fifosₛ : Std.HashMap String (Typ × List (Expression Typ))}
    {nameₛ : String} {mailboxₛ : Option (Expression Typ)}
    {precondₛ : Option (GuardedPlusCal.Block (GuardedPlusCal.Statement Typ (Expression Typ) true) false)}
    {«Σ» Γ Ξ : Scope}
    (wf' : match (motive := _ → Prop) precondₛ with
      | .some B => ∀ S ∈ B.toList, match S with
        -- Every `receive` does so from its mailbox (there must be one) which is well-typed.
        | .receive c _ => ∃ v, mailboxₛ = .some v ∧ match v with
          | .var x (.channel τ) => c.name = x ∧ c.τ = .channel τ ∧ c.args = [] ∧ Prod.fst <$> fifosₛ.find? c.name = .some (.channel τ)
          | .funcall (.var x (.function .address (.channel τ))) [.var "self" .address] => c.name = x ∧ c.τ = .function .address (.channel τ) ∧ c.args = [.var "self" .address] ∧ Prod.fst <$> fifosₛ.find? c.name = .some (.function .address (.channel τ))
          | _ => False
        | .await _ => True
        | .let _ _ _ _ => True
      | .none => True)
    (inbox_fresh_in_Br : match (motive := _ → Prop) mailboxₛ with
      | .none => True
      | .some _ => inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ ∀ S ∈ precondₛ.elim [] GuardedPlusCal.Block.toList, GuardedPlusCal.Statement.FreshIn Expression.FreshIn S (inbox ++ nameₛ))
    {«Σ_disj_Δ» : Disjoint («Σ» \ {"self"}) (fifosₛ.keys.toFinset \ {"self"})} {«Σ_disj_Γ» : Disjoint («Σ» \ {"self"}) (Γ \ {"self"})} {Δ_disj_Γ : Disjoint (fifosₛ.keys.toFinset \ {"self"}) (Γ \ {"self"})}
    {«Σ_disj_Ξ» : Disjoint («Σ» \ {"self"}) Ξ} {Δ_disj_Ξ : Disjoint (fifosₛ.keys.toFinset \ {"self"}) Ξ} {Γ_disj_Ξ : Disjoint (Γ \ {"self"}) Ξ}
    (precondₛ_wellscoped : GuardedPlusCal.AtomicBranch.WellScopedPrecond (flip Expression.WellScoped)
      («Σ» \ {"self"}) (fifosₛ.keys.toFinset \ {"self"}) (Γ \ {"self"}) ‹_› ‹_› ‹_› precondₛ {"self"} Ξ
      Finset.sdiff_disjoint Finset.sdiff_disjoint Finset.sdiff_disjoint «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ)
    («prims_in_Σ» : TypedSetTheory.prims.keys.toFinset ⊆ «Σ» \ {"self"}) :
      ⦃⌜True⌝⦄
      GuardedPlusCal.Thread.toNetwork.processPrecondition inbox nameₛ fifosₛ precondₛ
      ⦃⇓ (B, Ssₜ, _) => ⌜match precondₛ, B with
        | .none, .none => Ssₜ = []
        | .some precondₛ, .some B =>
          StrongRefinement (· ∼[Option.map (λ x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·)
            ⟦precondₛ⟧* ⟦precondₛ⟧⊥ ⟦precondₛ⟧∞
            (⟦B⟧* ∘ᵣ₂ List.foldl (· ∘ᵣ₂ ⟦·⟧*) {(x, e, y) | x = y ∧ e = Trace.τ} Ssₜ)
            (⟦B⟧⊥ ∪ ⟦B⟧* ∘ᵣ₁ List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ssₜ)
            (⟦B⟧∞ ∪ ⟦B⟧* ∘ᵣ₁ List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ssₜ)
        | .some _, .none | .none, .some _ => False⌝⦄ := by
    mintro -
    cases precondₛ with
    | none =>
      mspec AtomicBranch.correctness_precond_spec₂
      mrename_i h
      mpure h
      mpure_intro
      obtain ⟨h₁, h₂⟩ := h
      rw [h₁, h₂]
    | some val =>
      mspec AtomicBranch.correctness_precond_spec₁ wf' inbox_fresh_in_Br precondₛ_wellscoped «prims_in_Σ»
      mrename_i h
      mpure h
      mpure_intro
      split using _ | h₂ h₁ _ _ _ | h₁ _ _ _ | _
      · contradiction
      · rw [h₁] at h
        injection h₂ with val_eq
        subst val
        apply h
      · rwa [h₁] at h
      · contradiction

  theorem AtomicBranch.correctness_precond
    {fifosₛ : Std.HashMap String (Typ × List (Expression Typ))}
    {nameₛ : String} {mailboxₛ : Option (Expression Typ)}
    {precondₛ : Option (GuardedPlusCal.Block.{0} (GuardedPlusCal.Statement Typ (Expression Typ) true) false)}
    {precondₜ : Option (GuardedPlusCal.Block (NetworkPlusCal.Statement Typ (Expression Typ) true) false)}
    {«Σ» Γ Ξ : Scope}
    {Ssₜ : List (NetworkPlusCal.Statement Typ (Expression Typ) false false)}
    {rxs : List ((_ : String) × Typ × GuardedPlusCal.ChanRef Typ (Expression Typ))}
    (inbox_fresh_in_Br : match (motive := _ → Prop) mailboxₛ with
      | .none => True
      | .some _ => inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ ∀ S ∈ precondₛ.elim [] GuardedPlusCal.Block.toList, GuardedPlusCal.Statement.FreshIn Expression.FreshIn S (inbox ++ nameₛ))
    {«Σ_disj_Δ» : Disjoint («Σ» \ {"self"}) (fifosₛ.keys.toFinset \ {"self"})} {«Σ_disj_Γ» : Disjoint («Σ» \ {"self"}) (Γ \ {"self"})} {Δ_disj_Γ : Disjoint (fifosₛ.keys.toFinset \ {"self"}) (Γ \ {"self"})}
    {«Σ_disj_Ξ» : Disjoint («Σ» \ {"self"}) Ξ} {Δ_disj_Ξ : Disjoint (fifosₛ.keys.toFinset \ {"self"}) Ξ} {Γ_disj_Ξ : Disjoint (Γ \ {"self"}) Ξ}
    (precondₛ_wellscoped : GuardedPlusCal.AtomicBranch.WellScopedPrecond (flip Expression.WellScoped)
      («Σ» \ {"self"}) (fifosₛ.keys.toFinset \ {"self"}) (Γ \ {"self"}) ‹_› ‹_› ‹_› precondₛ {"self"} Ξ
      Finset.sdiff_disjoint Finset.sdiff_disjoint Finset.sdiff_disjoint «Σ_disj_Ξ» Δ_disj_Ξ Γ_disj_Ξ)
    («prims_in_Σ» : TypedSetTheory.prims.keys.toFinset ⊆ «Σ» \ {"self"})
    (compile_eq : GuardedPlusCal.Thread.toNetwork.processPrecondition inbox nameₛ fifosₛ precondₛ = (precondₜ, Ssₜ, rxs))
    --(wf : match (motive := _ → _ → Prop) mailboxₛ, precondₛ with | .none, _ | .some _, .none => True | .some _, .some precondₛ => inbox ++ nameₛ ∉ precondₛ.begin.flatMap (GuardedPlusCal.Statement.freeVars Expression.freeVars) ++ precondₛ.last.freeVars Expression.freeVars ∧ inbox ++ nameₛ ∉ prims)
    (wf' : match precondₛ with
      | .some B => ∀ S ∈ B.toList, match S with
        -- Every `receive` does so from its mailbox (there must be one) which is well-typed.
        | .receive c _ => ∃ v, mailboxₛ = .some v ∧ match v with
          | .var x (.channel τ) => c.name = x ∧ c.τ = .channel τ ∧ c.args = [] ∧ Prod.fst <$> fifosₛ.find? c.name = .some (.channel τ)
          | .funcall (.var x (.function .address (.channel τ))) [.var "self" .address] => c.name = x ∧ c.τ = .function .address (.channel τ) ∧ c.args = [.var "self" .address] ∧ Prod.fst <$> fifosₛ.find? c.name = .some (.function .address (.channel τ))
          | _ => False
        | .await _ => True
        | .let _ _ _ _ => True
      | .none => True) :
      StrongRefinement (· ∼[Option.map (λ x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·)
        (precondₛ.elim {(x, e, y) | x = y ∧ e = Trace.τ} (⟦·⟧*)) (precondₛ.elim ∅ (⟦·⟧⊥)) (precondₛ.elim ∅ (⟦·⟧∞))
        (precondₜ.elim {(x, e, y) | x = y ∧ e = Trace.τ} (⟦·⟧* ∘ᵣ₂ List.foldl (· ∘ᵣ₂ ⟦·⟧*) {(x, e, y) | x = y ∧ e = Trace.τ} Ssₜ))
        (precondₜ.elim ∅ λ precondₜ ↦ (⟦precondₜ⟧⊥ ∪ ⟦precondₜ⟧* ∘ᵣ₁ List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ssₜ))
        (precondₜ.elim ∅ λ precondₜ ↦ (⟦precondₜ⟧∞ ∪ ⟦precondₜ⟧* ∘ᵣ₁ List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ Ssₜ)) := by
    have comp_res_wp : match (motive := _ → Prop) precondₜ with | .none => Ssₜ = [] ∧ precondₛ = Option.none | .some _ => precondₛ.isSome :=
      Std.Do.Id.of_wp_run_eq compile_eq _ GuardedPlusCal.Thread.toNetwork.processPrecondition_spec₂

    cases precondₜ with
    | none =>
      -- This case is uninteresting
      obtain ⟨rfl, rfl⟩ := comp_res_wp
      constructor
      · apply StrongRefinement.Terminating.Id
      · apply StrongRefinement.Aborting.Empty
      · apply StrongRefinement.Diverging.Empty
    | some precondₜ =>
      erw [Option.isSome_iff_exists] at comp_res_wp
      obtain ⟨precondₛ, rfl⟩ := comp_res_wp
      exact Std.Do.Id.of_wp_run_eq compile_eq _ (AtomicBranch.correctness_precond_spec wf' inbox_fresh_in_Br precondₛ_wellscoped «prims_in_Σ»)

  lemma GuardedPlusCal.Statement.abort_goto {label} :
      ⟦@GuardedPlusCal.Statement.goto Typ (Expression Typ) label⟧⊥ = ∅ := by
    ext ⟨⟨Mₛ, Tₛ, Fₛ, lₛ⟩, ε⟩
    iff_rintro ⟨_|_, _, _⟩ (_|_)

  lemma NetworkPlusCal.Statement.abort_goto {label} :
      ⟦@NetworkPlusCal.Statement.goto Typ (Expression Typ) label⟧⊥ = ∅ := by
    ext ⟨⟨Mₜ, Tₜ, Fₜ, lₜ⟩, ε⟩
    iff_rintro ⟨_|_, _, _⟩ (_|_)

  theorem AtomicBranch.correctness_action
    (actionₛ : GuardedPlusCal.Block.{0} (GuardedPlusCal.Statement Typ (Expression Typ) false) true)
    {fifosₛ : Std.HashMap String (Typ × List (Expression Typ))} {mailbox : Option (Expression Typ × String)}
    {«Σ» Γ Ξ : Scope}
    (wf : match mailbox with | .none => True | .some ⟨_, inbox⟩ => ∀ S ∈ actionₛ.begin, GuardedPlusCal.Statement.FreshIn Expression.FreshIn S inbox)
    (self_in_Ξ : "self" ∈ Ξ)
    {«Σ_disj_Δ» : Disjoint («Σ» \ {"self"}) (fifosₛ.keys.toFinset \ {"self"})} {«Σ_disj_Γ» : Disjoint («Σ» \ {"self"}) (Γ \ {"self"})} {Δ_disj_Γ : Disjoint (fifosₛ.keys.toFinset \ {"self"}) (Γ \ {"self"})}
    {«Σ_disj_Ξ» : Disjoint («Σ» \ {"self"}) Ξ} {Δ_disj_Ξ : Disjoint (fifosₛ.keys.toFinset \ {"self"}) Ξ} {Γ_disj_Ξ : Disjoint (Γ \ {"self"}) Ξ}
    (actionₛ_wellscoped : GuardedPlusCal.AtomicBranch.WellScoped (flip Expression.WellScoped) ⟨.none, actionₛ⟩ («Σ» \ {"self"}) (fifosₛ.keys.toFinset \ {"self"}) (Γ \ {"self"}) Ξ) :
      StrongRefinement (· ∼[mailbox] ·)
        ⟦actionₛ⟧* ⟦actionₛ⟧⊥ ⟦actionₛ⟧∞
        ⟦GuardedPlusCal.Thread.toNetwork.processBlock actionₛ⟧* ⟦GuardedPlusCal.Thread.toNetwork.processBlock actionₛ⟧⊥ ⟦GuardedPlusCal.Thread.toNetwork.processBlock actionₛ⟧∞ := by
    set actionₜ := GuardedPlusCal.Thread.toNetwork.processBlock actionₛ with actionₜ_eq

    revert actionₜ_eq
    induction actionₜ using GuardedPlusCal.Block.reducing.induct generalizing actionₛ with
    | case1 B actionₜ_begin_nil =>
      rintro rfl
      apply GuardedPlusCal.Thread.toNetwork.processBlock.begin_empty_if at actionₜ_begin_nil
      conv in (occs := *) actionₛ =>
        all: apply GuardedPlusCal.Block.ext_iff (B' := {begin := [], last := actionₛ.last}) actionₜ_begin_nil rfl

      cases actionₛ.last with | goto label =>
      simp_rw [← GuardedPlusCal.Block.end.eq_def, GuardedPlusCal.Thread.toNetwork.processBlock.end_eq_end]
      conv in (occs := *) ⟦GuardedPlusCal.Block.end _⟧* => all: apply GuardedPlusCal.Block.sem_end

      constructor
      · rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ⟨Mₜ', Tₜ', Fₜ', _⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ sim ⟨_, rfl, ⟨_, _, _, _|_, _|_, rfl⟩, lₛ', _|_, rfl⟩
        left
        sem_exists Mₛ, Tₛ, Fₛ, label
        · match mailbox with
          | .none =>
            obtain ⟨rfl, rfl, rfl, rfl⟩ := sim
            trivial
          | .some ⟨_, inbox⟩ =>
            obtain rfl := relatesTo_eq_label sim
            obtain ⟨p, c, rfl⟩|⟨p₁, p₂, c, es, rfl⟩ := relatesTo_mailbox_shape sim <;> {
              obtain ⟨_, _, _, _⟩ := sim
              trivial
            }
        · exact relatesTo_eq_label sim
      · repeat rw [GuardedPlusCal.Block.abort_end']
        rw [GuardedPlusCal.Statement.abort_goto, NetworkPlusCal.Statement.abort_goto]
        apply StrongRefinement.Aborting.Empty
      · repeat rw [GuardedPlusCal.Block.div_end']
        rw [NetworkPlusCal.Statement.div_empty]
        apply StrongRefinement.Diverging.Empty
    | case2 actionₜ S Ss h IH =>
      rintro rfl
      obtain ⟨S', Ss', actionₛ_begin_eq, rfl, rfl⟩ := GuardedPlusCal.Thread.toNetwork.processBlock.begin_eq_cons_if h

      have process_actionₛ_eq : GuardedPlusCal.Thread.toNetwork.processBlock actionₛ = .cons (match_source (motive := GuardedPlusCal.Statement .. → _ → NetworkPlusCal.Statement ..) S' with
        | GuardedPlusCal.Statement.skip, pos => NetworkPlusCal.Statement.skip @@ pos
        | GuardedPlusCal.Statement.print e, pos => NetworkPlusCal.Statement.print e @@ pos
        | GuardedPlusCal.Statement.assert e, pos => NetworkPlusCal.Statement.assert e @@ pos
        | GuardedPlusCal.Statement.send chan e, pos => NetworkPlusCal.Statement.send chan e @@ pos
        | GuardedPlusCal.Statement.multicast chan bs e, pos => NetworkPlusCal.Statement.multicast chan bs e @@ pos
        | GuardedPlusCal.Statement.assign ref e, pos => NetworkPlusCal.Statement.assign ref e @@ pos) (GuardedPlusCal.Thread.toNetwork.processBlock {actionₛ with begin := Ss'}) := by
          conv in (occs := *) actionₛ =>
            rw [GuardedPlusCal.Block.ext_iff (B' := {begin := S' :: Ss', last := actionₛ.last}) actionₛ_begin_eq rfl,
                ← GuardedPlusCal.Block.cons.eq_1 (B := {actionₛ with begin := Ss'})]
          rw [GuardedPlusCal.Thread.toNetwork.processBlock.cons_eq_cons]

      repeat rw [process_actionₛ_eq] at IH ⊢
      clear process_actionₛ_eq

      conv in ⟦GuardedPlusCal.Block.cons _ _⟧* => apply GuardedPlusCal.Block.sem_cons'
      conv in (occs := *) ⟦GuardedPlusCal.Block.cons _ _⟧∞ => all: apply GuardedPlusCal.Block.div_cons'
      conv in (occs := *) actionₛ =>
        all: apply GuardedPlusCal.Block.ext_iff (B' := {begin := S' :: Ss', last := actionₛ.last}) actionₛ_begin_eq rfl
      rw [← GuardedPlusCal.Block.cons.eq_1 (B := {actionₛ with begin := Ss'}), GuardedPlusCal.Block.sem_cons', GuardedPlusCal.Block.abort_cons',
          GuardedPlusCal.Block.abort_cons', GuardedPlusCal.Block.div_cons']

      conv at wf in actionₛ =>
        apply GuardedPlusCal.Block.ext_iff (B' := {begin := S' :: Ss', last := actionₛ.last}) actionₛ_begin_eq rfl

      have wf' : match (motive := _ → Prop) mailbox with
          | none => True
          | some (fst, inbox) => GuardedPlusCal.Statement.FreshIn Expression.FreshIn S' inbox := by
        cases mailbox with
        | none => apply True.intro
        | some val => apply wf _ List.mem_cons_self

      have wellscoped :
          match (motive := _ → Prop) S' with
          | .skip => True
          | .print e => Expression.WellScoped e ((«Σ» \ {"self"}) ∪ (Γ \ {"self"}) ∪ Ξ)
          | .assert e => Expression.WellScoped e ((«Σ» \ {"self"}) ∪ (Γ \ {"self"}) ∪ Ξ)
          | .send chan e =>
            Expression.WellScoped e ((«Σ» \ {"self"}) ∪ (Γ \ {"self"}) ∪ Ξ) ∧ chan.name ∈ (fifosₛ.keys.toFinset \ {"self"}) ∧ (∀ idx ∈ chan.args, Expression.WellScoped idx ((«Σ» \ {"self"}) ∪ (Γ \ {"self"}) ∪ Ξ))
          | .multicast chan bs e =>
            chan ∈ (fifosₛ.keys.toFinset \ {"self"}) ∧ (∀ r ∈ bs, Expression.WellScoped r.2.2.2 ((«Σ» \ {"self"}) ∪ (Γ \ {"self"}) ∪ Ξ)) ∧ (∀ r ∈ bs, r.1 ∉ («Σ» \ {"self"}) ∧ r.1 ∉ (Γ \ {"self"}) ∧ r.1 ∉ Ξ) ∧
            Expression.WellScoped e ((«Σ» \ {"self"}) ∪ (Γ \ {"self"}) ∪ Ξ ∪ (bs.map Prod.fst).toFinset)
          | .assign ref e =>
            Expression.WellScoped e ((«Σ» \ {"self"}) ∪ (Γ \ {"self"}) ∪ Ξ) ∧ ref.name ∈ (Γ \ {"self"}) ∧ (∀ arg ∈ ref.args, ∀ idx ∈ arg, Expression.WellScoped idx ((«Σ» \ {"self"}) ∪ (Γ \ {"self"}) ∪ Ξ)) := by
        conv at actionₛ_wellscoped =>
          enter [2, 2]
          apply GuardedPlusCal.Block.ext_iff (B' := {begin := S' :: Ss', last := actionₛ.last}) actionₛ_begin_eq rfl
        cases S' <;> {
          unfold GuardedPlusCal.AtomicBranch.WellScoped at actionₛ_wellscoped
          first | obtain ⟨_, _, _, _, _⟩ := actionₛ_wellscoped
                | obtain ⟨_, _, _, _⟩ := actionₛ_wellscoped
                | obtain ⟨_, _, _⟩ := actionₛ_wellscoped
                | obtain ⟨_, _⟩ := actionₛ_wellscoped
                | skip
          trivial
        }

      apply StrongRefinement.Comp
      · exact GuardedPlusCal.Statement.strong_refinement S' self_in_Ξ Γ_disj_Ξ wellscoped wf'
      · apply IH
        · cases mailbox with
          | none => apply True.intro
          | some val => intros _ S_in; apply wf _ (List.mem_cons_of_mem _ S_in)
        · conv at actionₛ_wellscoped =>
            enter [2, 2]
            apply GuardedPlusCal.Block.ext_iff (B' := {begin := S' :: Ss', last := actionₛ.last}) actionₛ_begin_eq rfl
          cases S' <;> {
            unfold GuardedPlusCal.AtomicBranch.WellScoped at actionₛ_wellscoped
            first | obtain ⟨_, _, _, _, _⟩ := actionₛ_wellscoped
                  | obtain ⟨_, _, _, _⟩ := actionₛ_wellscoped
                  | obtain ⟨_, _, _⟩ := actionₛ_wellscoped
                  | obtain ⟨_, _⟩ := actionₛ_wellscoped
                  | skip
            trivial
          }
        · rfl

  theorem AtomicBranch.correctness
    {nameₛ : String} {mailboxₛ : Option (Expression Typ)}
    {Brₛ : GuardedPlusCal.AtomicBranch Typ (Expression Typ)}
    {fifosₛ : Std.HashMap String (Typ × List (Expression Typ))}
    {localsₛ : Std.HashMap String (Typ × Bool × Expression Typ)}
    (Brₛ_wf : Brₛ.wellFormed inbox mailboxₛ nameₛ fifosₛ)
    {precondₜ : Option (GuardedPlusCal.Block (NetworkPlusCal.Statement Typ (Expression Typ) true) false)}
    {newInstrs : List (NetworkPlusCal.Statement Typ (Expression Typ) false false)}
    {«Σ» Ξ : Scope}
    (precond_ref : match Brₛ.precondition, precondₜ with
      | none, none => newInstrs = []
      | some precondₛ, some B =>
        StrongRefinement (· ∼[Option.map (λ x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·) ⟦precondₛ⟧* ⟦precondₛ⟧⊥ ⟦precondₛ⟧∞
          (⟦B⟧* ∘ᵣ₂ List.foldl (· ∘ᵣ₂ ⟦·⟧*) {x | x.1 = x.2.2 ∧ x.2.1 = Trace.τ} newInstrs)
          (⟦B⟧⊥ ∪ ⟦B⟧* ∘ᵣ₁ List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ newInstrs)
          (⟦B⟧∞ ∪ ⟦B⟧* ∘ᵣ₁ List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ newInstrs)
      | some _, none | none, some _ => False)
    {«Σ_disj_Δ» : Disjoint («Σ» \ {"self"}) (fifosₛ.keys.toFinset \ {"self"})} {«Σ_disj_Γ» : Disjoint («Σ» \ {"self"}) (localsₛ.keys.toFinset \ {"self"})} {«Σ_disj_Ξ» : Disjoint («Σ» \ {"self"}) Ξ}
    {Δ_disj_Γ : Disjoint (fifosₛ.keys.toFinset \ {"self"}) (localsₛ.keys.toFinset \ {"self"})} {Δ_disj_Ξ : Disjoint (fifosₛ.keys.toFinset \ {"self"}) Ξ}
    {Γ_disj_Ξ : Disjoint (localsₛ.keys.toFinset \ {"self"}) Ξ}
    (Br_action_wellscoped : GuardedPlusCal.AtomicBranch.WellScoped (flip Expression.WellScoped) { precondition := none, action := Brₛ.action }
      («Σ» \ {"self"}) (fifosₛ.keys.toFinset \ {"self"}) (localsₛ.keys.toFinset \ {"self"}) Ξ)
    (self_in_Ξ : "self" ∈ Ξ)
    (inbox_fresh_in_Brₛ : match (motive := _ → Prop) mailboxₛ with
      | .none => True
      | .some _ => inbox ++ nameₛ ∉ «Σ» ∧ GuardedPlusCal.AtomicBranch.FreshIn Expression.FreshIn Brₛ (inbox ++ nameₛ)) :
      StrongRefinement (· ∼[Option.map (λ x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·) ⟦Brₛ⟧* ⟦Brₛ⟧⊥ ⟦Brₛ⟧∞
        ⟦{ precondition := precondₜ,
           action := newInstrs.foldr GuardedPlusCal.Block.cons (GuardedPlusCal.Thread.toNetwork.processBlock Brₛ.action)
         : NetworkPlusCal.AtomicBranch .. }⟧*
        ⟦{ precondition := precondₜ,
           action := newInstrs.foldr GuardedPlusCal.Block.cons (GuardedPlusCal.Thread.toNetwork.processBlock Brₛ.action)
         : NetworkPlusCal.AtomicBranch .. }⟧⊥
        ⟦{ precondition := precondₜ,
           action := newInstrs.foldr GuardedPlusCal.Block.cons (GuardedPlusCal.Thread.toNetwork.processBlock Brₛ.action)
         : NetworkPlusCal.AtomicBranch .. }⟧∞ := by
    rw [GuardedPlusCal.AtomicBranch.sem_eq, GuardedPlusCal.AtomicBranch.abort_eq, GuardedPlusCal.AtomicBranch.div_eq]
    rw [NetworkPlusCal.AtomicBranch.sem_eq, NetworkPlusCal.AtomicBranch.abort_eq, NetworkPlusCal.AtomicBranch.div_eq]
    split at precond_ref using h₃ | h <;> try contradiction
    · rw [precond_ref, List.foldr_nil, h₃]
      repeat erw [Relation.lcomp₂.left_id_eq, Relation.lcomp₁.left_id_eq, Set.empty_union]
      repeat erw [Relation.lcomp₁.left_id_eq, Set.empty_union]
      apply AtomicBranch.correctness_action
      · cases mailboxₛ with
        | none => apply True.intro
        | some _ =>
          obtain ⟨-, -, inbox_fresh_in_action⟩ := inbox_fresh_in_Brₛ
          assumption
      · assumption
      · assumption
      -- · rw [Finset.subset_sdiff, Finset.disjoint_singleton_right]
      --   refine ⟨«prims_in_Σ», ?_⟩
      --   decide
    · rw [h, GuardedPlusCal.Block.foldr_cons_eq, GuardedPlusCal.Block.sem_left_append_eq_comp']
      rw [GuardedPlusCal.Block.abort_left_append_eq_comp', GuardedPlusCal.Block.div_left_append_eq_comp']
      rw [Relation.lcomp₂.assoc, abort_assoc', div_assoc',
          Relation.lcomp₁.right_union_eq_union, ← Relation.lcomp₁.left_lcomp₂_eq, ← Set.union_assoc,
          Relation.lcomp₁.right_union_eq_union, ← Relation.lcomp₁.left_lcomp₂_eq, ← Set.union_assoc]

      dsimp
      convert StrongRefinement.Comp _ ?_ ?_ using 2
      · congr
        rw [← foldl_red_eq_foldr_red]
        rfl
      · congr
        rw [← foldl_red_eq_foldr_red]
        rfl
      · assumption
      · apply AtomicBranch.correctness_action
        · cases mailboxₛ with
          | none => apply True.intro
          | some _ =>
            obtain ⟨-, -, inbox_fresh_in_action⟩ := inbox_fresh_in_Brₛ
            assumption
        · assumption
        · assumption
        -- · rw [Finset.subset_sdiff, Finset.disjoint_singleton_right]
        --   refine ⟨«prims_in_Σ», ?_⟩
        --   decide

  /-- For all processes `Pₛ` that compile into some `Pₜ`, `Pₜ` refines the behavior of `Pₛ`. -/
  private theorem Process.correctness
    {Pₛ : GuardedPlusCal.Process.{0} Typ (Expression Typ)}
    {Pₜ : NetworkPlusCal.Process.{0} Typ (Expression Typ)}
    {channelsₛ fifosₛ : Std.HashMap String (Typ × List (Expression Typ))}
    {«Σ» : Scope}
    (compileSuccess : GuardedPlusCal.Process.toNetwork inbox (channelsₛ.mergeWith (λ _ v _ ↦ v) fifosₛ) Pₛ = Pₜ)
    (Pₛ_wf : Pₛ.wellFormed inbox (channelsₛ.mergeWith (λ _ v _ ↦ v) fifosₛ))
    («inbox_fresh_in_Pₛ_Σ» : match Pₛ.mailbox with
      | .none => True
      | .some _ => inbox ++ Pₛ.name ∉ «Σ» ∧ GuardedPlusCal.Process.FreshIn Expression.FreshIn Pₛ (inbox ++ Pₛ.name))
    {«Σ_disj_chans» : Disjoint «Σ» (channelsₛ.keys.toFinset ∪ fifosₛ.keys.toFinset)}
    (Pₛ_wellscoped : Pₛ.WellScoped (flip Expression.WellScoped) «Σ» (channelsₛ.keys.toFinset ∪ fifosₛ.keys.toFinset) ‹_›)
    («prims_in_Σ» : TypedSetTheory.prims.keys.toFinset ⊆ «Σ») :
      ProcRefine.{0} (inbox := inbox) Pₛ Pₜ := by
    intros Bₜ Bₜ_in

    apply List.exists_of_mem_flatMap at Bₜ_in
    obtain ⟨⟨blocksₜ⟩|_, Tₜ_in, Bₜ_in⟩ := Bₜ_in
    · obtain ⟨nameₛ, mailboxₛ, localsₛ, threadsₛ⟩ := Pₛ
      obtain ⟨nameₜ, mailboxₜ, localsₜ, threadsₜ⟩ := Pₜ

      injection compileSuccess with _ _ _ _
      dsimp at *
      subst nameₜ mailboxₜ localsₜ threadsₜ

      rw [List.mem_append] at Tₜ_in
      obtain Tₜ_in|Tₜ_in := Tₜ_in
      · exfalso

        conv at Tₜ_in => enter [1, 1, 1]; apply List.unzip₃_snd
        erw [List.unzip_snd, List.unzip_fst, List.mem_flatten] at Tₜ_in
        conv at Tₜ_in => enter [1, l, 1]; rw [List.mem_map]
        conv at Tₜ_in => enter [1, l, 1, 1, a, 1]; rw [List.mem_map]
        conv at Tₜ_in => enter [1, l, 1, 1, a, 1, 1, b, 1]; apply propext List.mem_map

        obtain ⟨-, ⟨⟨rxs', _⟩, ⟨⟨_, _, _⟩, ⟨Tₛ, Tₛ_in, compileSuccess⟩, _|_⟩, rfl⟩, blocksₜ_in⟩ := Tₜ_in

        have all_in_rxs'_isRx := Std.Do.Id.of_wp_run_eq compileSuccess _ GuardedPlusCal.Thread.toNetwork_spec₁
        specialize all_in_rxs'_isRx _ blocksₜ_in
        assumption
      · simp_rw [List.unzip₃_snd, List.unzip_snd, List.mem_map] at Tₜ_in
        conv at Tₜ_in => enter [1, a, 1, 1, b, 1]; apply propext List.mem_map
        obtain ⟨⟨rxs', -⟩, ⟨⟨_, _, _⟩, ⟨Tₛ, Tₛ_in, compileSuccess⟩, _|_⟩, rfl⟩ := Tₜ_in

        suffices h : ∃ Bₛ ∈ Tₛ, StrongRefinement (· ∼[Option.map (λ x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·) ⟦Bₛ⟧* ⟦Bₛ⟧⊥ ⟦Bₛ⟧∞ ⟦Bₜ⟧* ⟦Bₜ⟧⊥ ⟦Bₜ⟧∞ by
          refine Exists.imp ?_ h
          intro Bₛ
          apply And.imp_left
          exact List.mem_flatten_of_mem Tₛ_in

        revert Bₜ
        apply Std.Do.Id.of_wp_run_eq compileSuccess (λ (_, _, C) ↦ ∀ Bₜ ∈ C.toBlocks, ∃ Bₛ ∈ Tₛ, StrongRefinement (· ∼[Option.map (fun x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·) ⟦Bₛ⟧* ⟦Bₛ⟧⊥ ⟦Bₛ⟧∞ ⟦Bₜ⟧* ⟦Bₜ⟧⊥ ⟦Bₜ⟧∞)
        unfold GuardedPlusCal.Thread.toNetwork

        mvcgen

        -- First loop invariant
        case inv1 =>
          exact (⇓ (⟨_, Bsₛ, _⟩, r) =>
            ⌜(∀ Bₜ ∈ r.fst, ∃ Bₛ ∈ Tₛ, StrongRefinement (· ∼[Option.map (fun x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·) ⟦Bₛ⟧* ⟦Bₛ⟧⊥ ⟦Bₛ⟧∞ ⟦Bₜ⟧* ⟦Bₜ⟧⊥ ⟦Bₜ⟧∞) ∧
            ∀ Bₛ ∈ Bsₛ, ∀ Br ∈ Bₛ.branches,
              Br.wellFormed inbox mailboxₛ nameₛ (channelsₛ.mergeWith (λ _ v _ ↦ v) fifosₛ) ∧
              (match (motive := _ → Prop) mailboxₛ with | .none => True | .some _ => inbox ++ nameₛ ∉ «Σ» ∧ Br.FreshIn Expression.FreshIn (inbox ++ nameₛ)) ∧
              Br.WellScoped (flip Expression.WellScoped) («Σ» \ {"self"}) ((channelsₛ.keys.toFinset ∪ fifosₛ.keys.toFinset) \ {"self"}) (localsₛ.keys.toFinset \ {"self"}) {"self"}
                (Finset.disjoint_sdiff_sdiff_of_disjoint ‹_›) (Finset.disjoint_sdiff_sdiff_of_disjoint Pₛ_wellscoped.«Σ_locals_disjoint») (Finset.disjoint_sdiff_sdiff_of_disjoint Pₛ_wellscoped.Δ_locals_disjoint)⌝)
        -- Second loop invariant
        case inv2 =>
          exact (⇓ (⟨Brₛ, _, _⟩, r) => ⌜List.Forall₂ (λ Brₜ Brₛ ↦ StrongRefinement (· ∼[Option.map (λ x ↦ (x, inbox ++ nameₛ)) mailboxₛ] ·) ⟦Brₛ⟧* ⟦Brₛ⟧⊥ ⟦Brₛ⟧∞ ⟦Brₜ⟧* ⟦Brₜ⟧⊥ ⟦Brₜ⟧∞) r.1 Brₛ⌝)

        case vc2.step.pre =>
          apply List.Forall₂.nil

        case pre =>
          simp_all
          simp_rw [forall_and]
          and_intros
          · exact Pₛ_wf.blocks_wf _ Tₛ_in
          · cases mailboxₛ with
            | none => intros _ _ _ _; apply True.intro
            | some val =>
              intros Bₛ Bₛ_in Brₛ Brₛ_in
              exact «inbox_fresh_in_Pₛ_Σ».imp_right (·.fresh_in_blocks _ Tₛ_in _ Bₛ_in _ Brₛ_in)
          · exact Pₛ_wellscoped.threads_ws _ Tₛ_in

        case vc3.step.post.success =>
          rename_i h' r h

          obtain ⟨h'₁, h'₂⟩ := h'

          constructor
          · dsimp at h ⊢
            intros Bₜ Bₜ_in
            rw [List.mem_concat] at Bₜ_in
            obtain Bₜ_in|rfl := Bₜ_in
            · exact h'₁ _ Bₜ_in
            · --rename' x => Bₛ
              rename GuardedPlusCal.AtomicBlock Typ (Expression Typ) => Bₛ

              subst Tₛ
              exists Bₛ
              constructor
              · simp
              · rw [NetworkPlusCal.AtomicBlock.div_empty.{0}]
                apply StrongRefinement.ofNonDiverging
                · rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ⟨Mₜ', Tₜ', Fₜ', lₜ'⟩ ε σₛ rel ⟨Brₜ, Brₜ_in, l, red_Brₜ, rfl, rfl⟩
                  apply List.getElem_of_mem at Brₜ_in
                  obtain ⟨i, i_valid, rfl⟩ := Brₜ_in

                  have : r.fst.length = Bₛ.branches.length := List.Forall₂.length_eq h

                  apply List.Forall₂.get at h
                  specialize h i_valid (this ▸ i_valid)
                  rw [← NetworkPlusCal.LocalState.sem_glue₃] at red_Brₜ
                  obtain ⟨σₛ', rel, red⟩|⟨ε', ε'_le, abort⟩ := h.1 ⟨Mₜ, Tₜ, Fₜ, .none⟩ ⟨Mₜ', Tₜ', Fₜ', .some l⟩ ε σₛ rel red_Brₜ
                  · left
                    exists σₛ', rel, Bₛ.branches.get ⟨i, this ▸ i_valid⟩, List.getElem_mem _
                  · right
                    exists _, ε'_le, Bₛ.branches.get ⟨i, this ▸ i_valid⟩, List.getElem_mem _
                · rintro ⟨Mₜ, Tₜ, Fₜ, lₜ⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ rel ⟨Brₜ, Brₜ_in, red_Brₜ, rfl⟩
                  apply List.getElem_of_mem at Brₜ_in
                  obtain ⟨i, i_valid, rfl⟩ := Brₜ_in

                  have : r.fst.length = Bₛ.branches.length := List.Forall₂.length_eq h

                  apply List.Forall₂.get at h
                  specialize h i_valid (this ▸ i_valid)
                  rw [← NetworkPlusCal.LocalState.abort_glue₂] at red_Brₜ
                  obtain ⟨ε', ε'_le_ε, _⟩ := h.2 ⟨Mₜ, Tₜ, Fₜ, .none⟩ ε ⟨Mₛ, Tₛ, Fₛ, lₛ⟩ rel red_Brₜ
                  exists _, ε'_le_ε, Bₛ.branches.get ⟨i, this ▸ i_valid⟩, List.getElem_mem _
          · intros Bₛ Bₛ_in
            exact h'₂ Bₛ (List.mem_cons_of_mem _ Bₛ_in)

        case post.success =>
          simp_all

        case step =>
          rename GuardedPlusCal.AtomicBlock Typ (Expression Typ) => Bₛ
          rename_i h' _ Br _ Bₛ_branches_eq r _ _ _ _ _

          obtain ⟨inv, h'⟩ := h'

          obtain ⟨Br_wf, inbox_fresh_in_Br, Br_wellscoped⟩ := h' Bₛ (by simp) Br (by simp [Bₛ_branches_eq])
          rw [GuardedPlusCal.AtomicBranch.wellscoped_precond_action_iff_wellscoped] at Br_wellscoped
          obtain ⟨Ξ', Ξ'_supset, «Σ_disj_Ξ'», Δ_disj_Ξ', Γ_disj_Ξ', Br_precond_wellscoped, Br_action_wellscoped⟩ := Br_wellscoped

          have Δ_eq : channelsₛ.keys.toFinset ∪ fifosₛ.keys.toFinset = (channelsₛ.keys ++ fifosₛ.keys).toFinset := by
            rw [List.toFinset_append]
          have Δ'_eq : (channelsₛ.keys ++ fifosₛ.keys).toFinset = (channelsₛ.mergeWith (fun _ v _ ↦ v) fifosₛ).keys.toFinset := by
            rw [List.toFinset_eq_iff_perm_dedup, List.Nodup.dedup (Std.HashMap.keys_Nodup _)]
            symm
            apply Std.HashMap.keys_mergeWith_perm
          conv at Br_precond_wellscoped => enter [3, 1]; apply Eq.trans Δ_eq Δ'_eq
          conv at Br_action_wellscoped => enter [4, 1]; apply Eq.trans Δ_eq Δ'_eq

          have «prims_in_Σ'» : TypedSetTheory.prims.{0}.keys.toFinset ⊆ «Σ» \ {"self"} := by
            rw [Finset.subset_sdiff, Finset.disjoint_singleton_right]
            refine ⟨«prims_in_Σ», ?_⟩
            decide

          have fresh : match (motive := _ → Prop) mailboxₛ with
              | .none => True
              | .some _ => inbox ++ nameₛ ∉ «Σ» \ {"self"} ∧ ∀ S ∈ Br.precondition.elim [] GuardedPlusCal.Block.toList, S.FreshIn Expression.FreshIn (inbox ++ nameₛ) := by
            cases mailboxₛ with
            | none => apply True.intro
            | some _ =>
              refine inbox_fresh_in_Br.imp ?_ (·.fresh_in_precond)
              exact Finset.notMem_sdiff_of_notMem_left

          -- NOTE: inlining the `wellscoped` case makes the elaborator blow up (200k heartbeats reached), somehow?
          mstart
          mspec AtomicBranch.correctness_precond_spec Br_wf.precond_wf fresh ?wellscoped «prims_in_Σ'»
          case wellscoped => apply Br_precond_wellscoped

          rename_i r
          obtain _|⟨⟨x, τ, c⟩, _⟩ := r.2.2 <;> {
            conv => simp_match
            mrename_i h
            mpure h
            try split
            all:
              mspec Std.Do.Spec.pure
              mspec Std.Do.Spec.pure
              mspec Std.Do.Spec.pure
              simp_rw [List.concat_eq_append]
              mpure_intro
              apply List.rel_append
              · assumption
              · rw [List.forall₂_singleton]
                change _ ⊆ _ at Ξ'_supset; rw [Finset.singleton_subset_iff] at Ξ'_supset
                refine AtomicBranch.correctness Br_wf ?_ Br_action_wellscoped Ξ'_supset inbox_fresh_in_Br
                split at h <;> simp [*]
          }
    · contradiction

  -- In practice, we would need to show that the compilation steps before result in a well formed algorithm
  /--
    For all well-formed algorithms `aₛ` that succeed to compile into an algorithm `aₜ`, for each process `Pₜ ∈ aₜ`,
    there exists a process `Pₛ ∈ aₛ` such that `Pₜ` refines the behavior of `Pₛ`.
  -/
  protected theorem Algorithm.correctness
    {aₛ : GuardedPlusCal.Algorithm.{0} Typ (Expression Typ)}
    {aₜ : NetworkPlusCal.Algorithm.{0} Typ (Expression Typ)}
    -- Source algorithm is "well-formed" in some global scope `Σ`
    («Σ» : Scope) (aₛ_wf : GuardedPlusCal.Algorithm.wellFormed aₛ «Σ» inbox)
    -- Compilation succeeded
    (compileSuccess : GuardedPlusCal.Algorithm.toNetwork inbox aₛ = aₜ)
    : ∀ Pₜ ∈ aₜ.procs, ∃ Pₛ ∈ aₛ.procs, ProcRefine (inbox := inbox) Pₛ Pₜ := by
      intros Pₜ Pₜ_in

      obtain ⟨nameₛ, channelsₛ, fifosₛ, procsₛ⟩ := aₛ
      obtain ⟨nameₜ, channelsₜ, fifosₜ, procsₜ⟩ := aₜ

      injection compileSuccess with _ _ _ _
      subst nameₜ channelsₜ fifosₜ procsₜ

      apply List.exists_of_mem_map at Pₜ_in
      obtain ⟨Pₛ, Pₛ_in, compileSuccess⟩ := Pₜ_in

      haveI Pₛ_wf : Pₛ.wellFormed inbox _ := aₛ_wf.procs_wf _ Pₛ_in
      haveI «inbox_fresh_in_Pₛ_Σ» := aₛ_wf.inbox_fresh _ Pₛ_in
      haveI Pₛ_wellscoped := aₛ_wf.A_wellscoped.procs_ws _ Pₛ_in
      haveI «prims_in_Σ» := aₛ_wf.«Σ_contains_prims»

      exists Pₛ, Pₛ_in
      exact Process.correctness compileSuccess Pₛ_wf «inbox_fresh_in_Pₛ_Σ» Pₛ_wellscoped «prims_in_Σ»

end GuardedToNetwork

-- Check that our main correctness theorem is fully proven, i.e. that it does not (transitively) contain occurrences of `sorryAx`
--assert_no_sorry GuardedToNetwork.Algorithm.correctness
