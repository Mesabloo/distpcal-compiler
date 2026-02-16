import PlusCalCompiler.GuardedPlusCal.Syntax
import Mathlib.Data.List.Induction
import Extra.List

namespace GuardedPlusCal
  @[ext] theorem Block.ext_iff.{u} {F : Bool → Type u} {b} {B B' : Block F b} (h₁ : B.begin = B'.begin) (h₂ : B.last = B'.last) : B = B' := by
    erw [Block.mk.injEq]
    trivial

  theorem Block.foldr_cons_eq.{u} {F : Bool → Type u} {b} {B : Block F b} {Ss : List (F false)} :
    List.foldr GuardedPlusCal.Block.cons B Ss = { B with begin := Ss ++ B.begin } := by
      induction Ss with
      | nil => rfl
      | cons S Ss IH => rw [List.foldr_cons, Block.cons, IH]; rfl

  theorem Block.prepend_nil.{u} {F : Bool → Type u} {b} {B : Block F b} : B.prepend [] = B := rfl

  theorem Block.concat_ne_end.{u} {F : Bool → Type u} {b} {B : Block F false} {S S' : F b} : B.concat S ≠ Block.end S' := by
    unfold Block.concat Block.end
    simp_all

  theorem Block.last_end.{u} {F : Bool → Type u} {b} {S : F b} : (Block.end S).last = S := rfl

  theorem Block.last_cons.{u} {F : Bool → Type u} {S : F false} {b} {B : Block F b} : (Block.cons S B).last = B.last := rfl

  theorem Block.last_concat.{u} {F : Bool → Type u} {b} {S : F b} {B : Block F false} : (B.concat S).last = S := rfl

  theorem Block.begin_end.{u} {F : Bool → Type u} {b} {S : F b} : (Block.end S).begin = [] := rfl

  theorem Block.begin_concat.{u} {F : Bool → Type u} {b} {S : F b} {B : Block F false} : (B.concat S).begin = B.toList := rfl

  theorem Block.toList_concat.{u} {F : Bool → Type u} {S : F false} {B : Block F false} : (B.concat S).toList = B.toList.concat S := rfl

  theorem Block.toList_end.{u} {F : Bool → Type u} {S : F false} : (Block.end S).toList = [S] := rfl

  theorem Block.toList_cons.{u} {F : Bool → Type u} {S : F false} {B : Block F false} : (Block.cons S B).toList = S :: B.toList := rfl

  theorem Block.concat_end.{u} {F : Bool → Type u} {S : F false} {b} {S' : F b} : (Block.end S).concat S' = Block.cons S (Block.end S') := rfl

  theorem Block.concat_cons.{u} {F : Bool → Type u} {S : F false} {B : Block F false} {b} {S' : F b} : (Block.cons S B).concat S' = Block.cons S (B.concat S') := rfl

  def Block.cons_end_induct.{u, v}
    {F : Bool → Type u} {motive : ⦃b : Bool⦄ → Block F b → Sort v}
    {b} (B : Block F b)
    («end» : ∀ {b} (S : F b), motive (.end S))
    (cons : ∀ {b} (S : F false) (B : Block F b), motive B → motive (.cons S B)) :
    motive B :=
      let ⟨Ss, S'⟩ := B
      match Ss with
      | [] => «end» S'
      | S :: Ss => cons S ⟨Ss, S'⟩ (Block.cons_end_induct ⟨Ss, S'⟩ «end» cons)

  @[push_cast]
  theorem Block.cast_end_eq_end_cast {F : Bool → Type _} {b b'} {S : F b} (b_eq : b = b') : b_eq ▸ GuardedPlusCal.Block.end S = GuardedPlusCal.Block.end (b_eq ▸ S) := by
    cases b_eq
    rfl

  @[push_cast]
  theorem Block.cast_cons_eq_cons_cast {F : Bool → Type _} {b b'} {S : F false} {B : Block F b} (b_eq : b = b') : b_eq ▸ GuardedPlusCal.Block.cons S B = GuardedPlusCal.Block.cons S (b_eq ▸ B) := by
    cases b_eq
    rfl

  def Block.cons_end_induct'.{u, v}
    {F : Bool → Type u} {motive : Block F false → Sort v}
    (B : Block F false)
    («end» : ∀ (S : F false), motive (.end S))
    (cons : ∀ (S : F false) (B : Block F false), motive B → motive (.cons S B)) :
    motive B :=
      Block.cons_end_induct (motive := λ ⦃b⦄ B ↦ (b_eq : b = false) → motive (b_eq ▸ B))
        B (λ S b_eq ↦ Block.cast_end_eq_end_cast b_eq ▸ «end» (b_eq ▸ S)) (λ S B IH b_eq ↦ Block.cast_cons_eq_cons_cast _ ▸ cons S (b_eq ▸ B) (IH b_eq))
        rfl

  theorem Block.concat_ofList.{u} {F : Bool → Type u} {Ss : List (F false)} {S' : F false} {h : Ss ≠ []} : (Block.ofList Ss h).concat S' = ⟨Ss, S'⟩ := by
    unfold Block.ofList Block.concat
    simp [List.dropLast_concat_getLast]

  theorem Block.sizeOf_ofList.{u} {F : Bool → Type u} {Ss : List (F false)} [inst : (b : Bool) → SizeOf (F b)] {h : Ss ≠ []} :
    sizeOf (Block.ofList Ss h) = 1 + sizeOf Ss.dropLast + sizeOf (Ss.getLast h) := by
      unfold Block.ofList
      rfl

  def Block.concat_end_induct.{u, v} {F : Bool → Type u} [(b : Bool) → SizeOf (F b)] {motive : Block F false → Sort v} (B : Block F false)
    («end» : ∀ (S : F false), motive (.end S)) (concat : ∀ (S : F false) (B : Block F false), motive B → motive (B.concat S)) :
    motive B :=
      match B with
      | ⟨[], S'⟩ => «end» S'
      | ⟨S :: Ss, S'⟩ => Block.concat_ofList ▸ concat S' (Block.ofList (S :: Ss) (by simp_all)) (Block.concat_end_induct _ «end» concat)
  termination_by @sizeOf _ (Block._sizeOf_inst F false) B
  decreasing_by
    all_goals simp_wf
    · simp +arith [Block.sizeOf_ofList, List.dropLast_getLast_add_sizeOf_eq]

  theorem Block.ofList_cons_of_non_empty.{u} {F : Bool → Type u} {Ss : List (F false)} {S : F false} (h : Ss ≠ []):
      Block.ofList (S :: Ss) (List.cons_ne_nil _ _) = Block.cons S (Block.ofList Ss h) := by
    unfold ofList cons
    rw [List.dropLast_cons_of_ne_nil h, List.getLast_cons h]

  theorem Block.ofList_singleton.{u} {F : Bool → Type u} {S : F false} : Block.ofList [S] (List.cons_ne_nil _ _) = Block.end S := rfl

  theorem Block.toList_left_inverse.{u} {F : Bool → Type u} {Ss : List (F false)} (h : Ss ≠ []) : (Block.ofList Ss h).toList = Ss := by
    dsimp [ofList, toList]
    simp [List.dropLast_concat_getLast]

  theorem Block.toList_non_empty.{u} {F : Bool → Type u} {B : Block F false} : B.toList ≠ [] := by
    unfold toList
    simp

  theorem Block.toList_right_inverse.{u} {F : Bool → Type u} {B : Block F false} : Block.ofList B.toList Block.toList_non_empty = B := by
    dsimp [ofList, toList]
    simp

  theorem Block.ofList_of_toList.{u} {F : Bool → Type u} {B : Block F false} {Ss : List (F false)} (h : B.toList = Ss) : B = Block.ofList Ss (h ▸ Block.toList_non_empty) := by
    replace h : Block.ofList B.toList Block.toList_non_empty = Block.ofList Ss (h ▸ Block.toList_non_empty) := by congr
    rwa [Block.toList_right_inverse] at h
