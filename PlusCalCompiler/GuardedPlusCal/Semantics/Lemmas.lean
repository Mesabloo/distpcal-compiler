import PlusCalCompiler.GuardedPlusCal.Semantics.Denotational
import PlusCalCompiler.GuardedPlusCal.Syntax.Lemmas

namespace GuardedPlusCal
  theorem Block.sem_end
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [reduceF : ⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))]
    {S : F b} :
    ⟦«end» S⟧* = ⟦S⟧* := by
      change Block.reducing _ («end» S) = _
      rw [Block.end, Block.reducing]

  theorem Block.sem_cons
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [reduceF : ⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))]
    {B : Block F b} {S : F false} :
    ⟦cons S B⟧* = ⟦S⟧* ∘ᵣ₂ ⟦B⟧* := by
      change Block.reducing _ (cons S B) = _ ∘ᵣ₂ Block.reducing _ B
      rw [Block.cons, Block.reducing]

  theorem Block.sem_concat
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [reduceF : ⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))]
    {B : Block F false} {S : F b} :
    ⟦B.concat S⟧* = ⟦B⟧* ∘ᵣ₂ ⟦S⟧* := by
      induction B using Block.cons_end_induct' with
      | «end» S' =>
        change Block.reducing _ ((Block.end S').concat S) = Block.reducing _ (Block.end S') ∘ᵣ₂ ⟦S⟧*
        unfold Block.reducing
        erw [Block.begin_concat, Block.last_concat, Block.last_end, Block.toList_end]
        change ⟦S'⟧* ∘ᵣ₂ ⟦Block.end S⟧* = _
        rw [Block.sem_end]
      | cons S' B IH =>
        change Block.reducing _ ((Block.cons S' B).concat S) = Block.reducing _ (Block.cons S' B) ∘ᵣ₂ ⟦S⟧*
        unfold Block.reducing
        erw [Block.begin_concat, Block.toList_cons, Block.last_cons, Block.last_concat]
        change ⟦S'⟧* ∘ᵣ₂ ⟦B.concat S⟧* = (⟦S'⟧* ∘ᵣ₂ ⟦B⟧*) ∘ᵣ₂ ⟦S⟧*
        rw [← Relation.lcomp₂.assoc, IH]

  theorem Block.sem_left_append_eq_comp₁
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))]
    {A : List (F false)} {B : Block F b}
    (A_ne_nil : A ≠ []) :
    ⟦{B with begin := A ++ B.begin}⟧* = A.tail.foldl (init := ⟦A.head A_ne_nil⟧*) (λ sem x ↦ sem ∘ᵣ₂ ⟦x⟧*) ∘ᵣ₂ ⟦B⟧* := by
      generalize B'_eq : { B with begin := A ++ B.begin } = B'
      have B'_begin_eq : B'.begin = A ++ B.begin := by subst B'; dsimp

      induction B' using Block.reducing.induct generalizing A with
      | case1 B' B'_begin_eq' =>
        rw [B'_begin_eq'] at B'_begin_eq
        symm at B'_begin_eq
        apply List.append_ne_nil_of_left_ne_nil at B'_begin_eq
        · contradiction
        · assumption
      | case2 B' S Ss h₁ IH =>
        subst B'

        dsimp at h₁
        rw [List.append_eq_cons_iff] at h₁
        obtain ⟨rfl, _⟩|⟨Ss, rfl, rfl⟩ := h₁
        · contradiction
        · dsimp at *

          match (generalizing := false) Ss_eq : Ss with
          | [] => rw [List.foldl_nil, List.nil_append, ← Block.cons, Block.sem_cons]
          | _ :: _ =>
            specialize @IH Ss (Ss_eq ▸ List.cons_ne_nil _ _) rfl rfl
            rw [← Ss_eq, ← Block.cons.eq_def (B := { begin := Ss ++ B.begin, last := B.last}), Block.sem_cons, IH, Relation.lcomp₂.assoc,
              ← List.foldl_hom (f := λ sem ↦ ⟦S⟧* ∘ᵣ₂ sem) (g₁ := λ sem x ↦ sem ∘ᵣ₂ ⟦x⟧*) (g₂ := λ sem x ↦ sem ∘ᵣ₂ ⟦x⟧*)]
            · rw [← List.foldl_cons, List.cons_head_tail]
            · intros x y
              rw [← Relation.lcomp₂.assoc]

  theorem Block.sem_left_append_eq_comp₂
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))]
    {B : Block F b} :
    ⟦{B with begin := [] ++ B.begin}⟧* = ⟦B⟧* := by
      rw [List.nil_append]

  theorem Block.sem_left_append_eq_comp
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))]
    {A : List (F false)} {B : Block F b} :
    ⟦{B with begin := A ++ B.begin}⟧* = A.foldl (init := {⟨x, e, y⟩ | x = y ∧ e = 1}) (λ sem x ↦ sem ∘ᵣ₂ ⟦x⟧*) ∘ᵣ₂ ⟦B⟧* := by
      cases A with
      | nil => rw [List.foldl_nil, Block.sem_left_append_eq_comp₂, Relation.lcomp₂.left_id_eq]
      | cons => rw [List.foldl_cons, Block.sem_left_append_eq_comp₁ (List.cons_ne_nil _ _), Relation.lcomp₂.left_id_eq, List.head_cons, List.tail_cons]

  theorem Block.sem_prepend_eq_comp
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))]
    {A : List (F false)} {B : Block F b} :
    ⟦B.prepend A⟧* = A.foldl (init := {⟨x, e, y⟩ | x = y ∧ e = 1}) (λ sem x ↦ sem ∘ᵣ₂ ⟦x⟧*) ∘ᵣ₂ ⟦B⟧* := Block.sem_left_append_eq_comp

  theorem Block.abort_end
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))] [⦃b : Bool⦄ → Abort (F b) (Set (α false × β))]
    {S : F b} :
    ⟦«end» S⟧⊥ = ⟦S⟧⊥ := by
      change Block.aborting _ _ («end» S) = _
      rw [Block.end, Block.aborting]

  theorem Block.abort_cons
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))] [⦃b : Bool⦄ → Abort (F b) (Set (α false × β))]
    {S : F false} {B : Block F b} :
    ⟦cons S B⟧⊥ = ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ ⟦B⟧⊥ := by
      change Block.aborting _ _ _ = _ ∪ _ ∘ᵣ₁ Block.aborting _ _ _
      rw [Block.cons, Block.aborting]

  theorem Block.div_end
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))] [⦃b : Bool⦄ → Diverge (F b) (Set (α false × β))]
    {S : F b} :
    ⟦«end» S⟧∞ = ⟦S⟧∞ := by
      change Block.diverging _ _ («end» S) = _
      rw [Block.end, Block.diverging]

  theorem Block.div_cons
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))] [⦃b : Bool⦄ → Diverge (F b) (Set (α false × β))]
    {S : F false} {B : Block F b} :
    ⟦cons S B⟧∞ = ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ ⟦B⟧∞ := by
      change Block.diverging _ _ _ = _ ∪ _ ∘ᵣ₁ Block.diverging _ _ _
      rw [Block.cons, Block.diverging]

  theorem Block.sem_eq_foldr
    {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))]
    {B : Block F false} :
    ⟦B⟧* = List.foldr (⟦·⟧* ∘ᵣ₂ ·) {⟨x, e, y⟩ | x = y ∧ e = 1} B.toList := by
      change Block.reducing _ _ = _
      induction B using Block.reducing.induct with
      | case1 B _ =>
        let ⟨[], S⟩ := B
        simp [Block.toList, Block.reducing, Relation.lcomp₂.right_id_eq]
      | case2 B S Ss h IH =>
        let ⟨_ :: _, S'⟩ := B
        obtain _|_ := h

        rw [Block.reducing, Block.toList, List.concat_eq_append, List.cons_append, List.foldr_cons]
        dsimp at IH ⊢
        rw [IH, Block.toList, List.concat_eq_append]

  theorem Block.abort_eq_foldr
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))] [⦃b : Bool⦄ → Abort (F b) (Set (α false × β))]
    {B : Block F b} :
      ⟦B⟧⊥ = List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ⟦B.last⟧⊥ B.begin := by
    change Block.aborting _ _ _ = _
    induction B using Block.aborting.induct with
    | case1 B _ =>
      let ⟨[], S⟩ := B
      simp [Block.aborting]
    | case2 B S Ss h IH =>
      let ⟨_ :: _, S'⟩ := B
      obtain _|_ := h
      simp [Block.aborting, IH]

  theorem Block.div_eq_foldr
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))] [⦃b : Bool⦄ → Diverge (F b) (Set (α false × β))]
    {B : Block F b} :
      ⟦B⟧∞ = List.foldr (λ S sem ↦ ⟦S⟧∞ ∪ ⟦S⟧* ∘ᵣ₁ sem) ⟦B.last⟧∞ B.begin := by
    change Block.diverging _ _ _ = _
    induction B using Block.diverging.induct with
    | case1 B _ =>
      let ⟨[], S⟩ := B
      simp [Block.diverging]
    | case2 B S Ss h IH =>
      let ⟨_ :: _, S'⟩ := B
      obtain _|_ := h
      simp [Block.diverging, IH]

  theorem Block.abort_eq_foldr_toList
    {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))] [⦃b : Bool⦄ → Abort (F b) (Set (α false × β))]
    {B : Block F false} :
      ⟦B⟧⊥ = List.foldr (λ S sem ↦ ⟦S⟧⊥ ∪ ⟦S⟧* ∘ᵣ₁ sem) ∅ B.toList := by
    rw [Block.abort_eq_foldr, Block.toList, List.concat_eq_append, List.foldr_concat, Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]

  theorem Block.abort_concat
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))] [⦃b : Bool⦄ → Abort (F b) (Set (α false × β))]
    {S : F b} {B : Block F false} :
    ⟦B.concat S⟧⊥ = ⟦B⟧⊥ ∪ ⟦B⟧* ∘ᵣ₁ ⟦S⟧⊥ := by
      induction B using Block.aborting.induct with
      | case1 B _ =>
        let ⟨[], S'⟩ := B
        rw [← Block.end, Block.concat_end, Block.abort_cons, Block.abort_end, Block.abort_end, Block.sem_end]
      | case2 B S' Ss h IH =>
        let ⟨_ :: _, S''⟩ := B
        obtain _|_ := h
        change ⟦(Block.cons S' {begin := Ss, last := S''}).concat S⟧⊥ = ⟦Block.cons S' {begin := Ss, last := S''}⟧⊥ ∪ ⟦Block.cons S' {begin := Ss, last := S''}⟧* ∘ᵣ₁ ⟦S⟧⊥
        erw [Block.concat_cons, Block.abort_cons, IH, Block.abort_cons, Relation.lcomp₁.right_union_eq_union, Block.sem_cons, ← Set.union_assoc, Relation.lcomp₁.left_lcomp₂_eq]

  theorem Block.div_concat
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))] [⦃b : Bool⦄ → Diverge (F b) (Set (α false × β))]
    {S : F b} {B : Block F false} :
    ⟦B.concat S⟧∞ = ⟦B⟧∞ ∪ ⟦B⟧* ∘ᵣ₁ ⟦S⟧∞ := by
      induction B using Block.aborting.induct with
      | case1 B _ =>
        let ⟨[], S'⟩ := B
        rw [← Block.end, Block.concat_end, Block.div_cons, Block.div_end, Block.div_end, Block.sem_end]
      | case2 B S' Ss h IH =>
        let ⟨_ :: _, S''⟩ := B
        obtain _|_ := h
        change ⟦(Block.cons S' {begin := Ss, last := S''}).concat S⟧∞ = ⟦Block.cons S' {begin := Ss, last := S''}⟧∞ ∪ ⟦Block.cons S' {begin := Ss, last := S''}⟧* ∘ᵣ₁ ⟦S⟧∞
        erw [Block.concat_cons, Block.div_cons, IH, Block.div_cons, Relation.lcomp₁.right_union_eq_union, Block.sem_cons, ← Set.union_assoc, Relation.lcomp₁.left_lcomp₂_eq]

  theorem Block.abort_left_append_eq_comp
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))] [⦃b : Bool⦄ → Abort (F b) (Set (α false × β))]
    {A : List (F false)} {B : Block F b} :
      ⟦{ B with begin := A ++ B.begin }⟧⊥ = List.foldr (fun x sem ↦ ⟦x⟧⊥ ∪ ⟦x⟧* ∘ᵣ₁ sem) ⟦B⟧⊥ A := by
    simp [Block.abort_eq_foldr]

  theorem Block.div_left_append_eq_comp
    {b : Bool} {α F : Bool → Type _}
    {β} [Monoid β] [⦃b : Bool⦄ → Reduce (F b) (Set (α false × β × α b))] [⦃b : Bool⦄ → Diverge (F b) (Set (α false × β))]
    {A : List (F false)} {B : Block F b} :
      ⟦{ B with begin := A ++ B.begin }⟧∞ = List.foldr (fun x sem ↦ ⟦x⟧∞ ∪ ⟦x⟧* ∘ᵣ₁ sem) ⟦B⟧∞ A := by
    simp [Block.div_eq_foldr]

  -- Inversion lemmas

  theorem Statement.reducing.let.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {x τ «=|∈» e}
    (h : ∃ M T F v, T ∪ M ⊢ e ⇒ v ∧ AList.lookup x (T ∪ M) = none ∧ σ = .running M T F ∧ ε = [] ∧ match «=|∈», v with
      | true, .set vs => ∃ v' ∈ vs, σ' = .running M (T.insert x v') F
      | true, _ => False
      | false, v' => σ' = .running M (T.insert x v') F) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.let.{u} x τ «=|∈» e) := by
    trivial

  theorem Statement.reducing.await.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {e}
    (h : ∃ M T F, σ = .running M T F ∧ σ' = .running M T F ∧ T ∪ M ⊢ e ⇒ .bool true ∧ ε = []) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.await.{u} e) := by
      trivial

  theorem Statement.reducing.receive.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {chan ref}
    (h : ∃ M T F M' vs vss v vs',
        List.Forall₂ (T ∪ M ⊢ · ⇒ ·) chan.args vs ∧ List.Forall₂ (List.Forall₂ (T ∪ M ⊢ · ⇒ ·)) ref.args vss ∧
        F.lookup ⟨chan.name, vs⟩ = .some (v :: vs') ∧
        Memory.updateRef M {ref with args := vss} v = some M' ∧
        σ = .running M T F ∧ σ' = .running M' T (F.replace ⟨chan.name, vs⟩ vs') ∧ ε = []) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.receive.{u} chan ref) := by
    trivial

  theorem Statement.reducing.skip.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior}
    (h : ∃ M T F, σ = .running M T F ∧ σ' = .running M T F ∧ ε = []) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.skip.{u}) := by
    trivial

  theorem Statement.reducing.goto.intro.{u} {σ : LocalState.{u} false} {σ' : LocalState.{u} true} {ε : List Behavior.{u}} {l}
    (h : ∃ M T F, σ = .running M T F ∧ σ' = .done M T F l ∧ ε = []) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.goto.{u} l) := by
    trivial

  theorem Statement.reducing.print.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {e}
    (h : ∃ M T F v, σ = .running M T F ∧ σ' = .running M T F ∧ T ∪ M ⊢ e ⇒ v ∧ ε = [.print v]) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.print.{u} e) := by
    trivial

  theorem Statement.reducing.assert.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {e}
    (h : ∃ M T F, σ = .running M T F ∧ σ' = .running M T F ∧ T ∪ M ⊢ e ⇒ .bool true ∧ ε = []) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.assert.{u} e) := by
    trivial

  theorem Statement.reducing.send.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {chan e}
    (h : ∃ M T F v vs vs',
        T ∪ M ⊢ e ⇒ v ∧ List.Forall₂ (T ∪ M ⊢ · ⇒ ·) chan.args vs ∧
        F.lookup ⟨chan.name, vs⟩ = .some vs' ∧
        σ = .running M T F ∧ σ' = .running M T (F.replace ⟨chan.name, vs⟩ (vs'.concat v)) ∧ ε = [.send {chan with args := vs} v]) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.send.{u} chan e) := by
    trivial

  theorem Statement.reducing.assign.intro.{u} {σ σ' : LocalState.{u} false} {ε : List Behavior.{u}} {ref e}
    (h : ∃ M T F M' v vss,
        T ∪ M ⊢ e ⇒ v ∧ List.Forall₂ (List.Forall₂ (T ∪ M ⊢ · ⇒ ·)) ref.args vss ∧
        Memory.updateRef M {ref with args := vss} v = some M' ∧ ref.name ∉ T ∧
        σ = .running M T F ∧ σ' = .running M' T F ∧ ε = []) :
      (σ, ε, σ') ∈ Statement.reducing (Statement.assign.{u} ref e) := by
    trivial
end GuardedPlusCal

section
  open Lean Parser Tactic

  syntax "sem_redg " term (" ⤳ " term)? ", " term (" ⤳ " term)? ", " term (" ⤳ " term)? (", " term)? : tactic
  macro_rules
  | `(tactic| sem_redg $w₁ $[⤳ $w₂]?, $x₁ $[⤳ $x₂]?, $y₁ $[⤳ $y₂]? $[, $z]?) => do
    let w₂ := w₂.getD w₁
    let x₂ := x₂.getD x₁
    let y₂ := y₂.getD y₁

    match z with
    | .none => `(tactic| first
      | refine ⟨GuardedPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, GuardedPlusCal.Statement.reducing.skip.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨GuardedPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, GuardedPlusCal.Statement.reducing.print.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨GuardedPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, GuardedPlusCal.Statement.reducing.assert.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨GuardedPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, GuardedPlusCal.Statement.reducing.send.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨GuardedPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, GuardedPlusCal.Statement.reducing.await.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨GuardedPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, GuardedPlusCal.Statement.reducing.let.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨GuardedPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, GuardedPlusCal.Statement.reducing.receive.intro ⟨$w₁, $x₁, $y₁, $w₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | refine ⟨GuardedPlusCal.LocalState.running $w₂ $x₂ $y₂, ?_, GuardedPlusCal.Statement.reducing.assign.intro ⟨$w₁, $x₁, $y₁, $w₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try rfl
      | fail "Statement unsupported (yet)"
    )
    | .some z => `(tactic| first
      | refine ⟨GuardedPlusCal.LocalState.done $w₂ $x₂ $y₂ $z, ?_, GuardedPlusCal.Statement.reducing.goto.intro ⟨$w₁, $x₁, $y₁, ?_, ?_, ?_⟩, $z, ?_, ?_⟩ <;> try rfl
    )
