module

meta import CustomPrelude
public import Core.GuardedPlusCal.Syntax
public import Mathlib.Data.List.Induction
public import Extra.List

@[expose] public section

/-!
  Structural facts about `GuardedPlusCal.Block`'s list-like interface, and the two induction
  principles the semantics is proved by. Purely syntactic — nothing here mentions values, memories,
  or the semantics, which is why it sits under `Syntax/` rather than `Semantics/`.

  `Block` is a non-empty list in disguise (`begin ++ [last]`), so it supports both a left-to-right
  view (`cons`/`end`, `Block.cons_end_induct`) and a right-to-left one (`concat`/`end`,
  `Block.concat_end_induct`). `Semantics/Lemmas.lean` needs both: reduction composes left to right,
  while `concat`-shaped rewrites arise from appending a terminal statement.
-/

namespace GuardedPlusCal

@[ext] theorem Block.ext_iff {α : Bool → Type} {b : Bool} {B B' : Block α b}
    (h₁ : B.begin = B'.begin) (h₂ : B.last = B'.last) : B = B' := by
  rw [Block.mk.injEq]
  trivial

theorem Block.foldr_cons_eq {α : Bool → Type} {b : Bool} {B : Block α b} {Ss : List (α false)} :
    List.foldr Block.cons B Ss = { B with begin := Ss ++ B.begin } := by
  induction Ss with
  | nil => rfl
  | cons S Ss IH => rw [List.foldr_cons, Block.cons, IH]; rfl

theorem Block.prepend_nil {α : Bool → Type} {b : Bool} {B : Block α b} : B.prepend [] = B := rfl

/-- Prepending peels one statement at a time into a `cons` — the equation an induction over the
prepended list runs on. -/
theorem Block.prepend_cons {α : Bool → Type} {b : Bool} {S : α false} {Ss : List (α false)}
    {B : Block α b} : B.prepend (S :: Ss) = Block.cons S (B.prepend Ss) := rfl

theorem Block.concat_ne_end {α : Bool → Type} {b : Bool} {B : Block α false} {S S' : α b} :
    B.concat S ≠ Block.end S' := by
  unfold Block.concat Block.end
  simp_all

theorem Block.last_end {α : Bool → Type} {b : Bool} {S : α b} : (Block.end S).last = S := rfl

theorem Block.last_cons {α : Bool → Type} {S : α false} {b : Bool} {B : Block α b} :
    (Block.cons S B).last = B.last := rfl

theorem Block.last_concat {α : Bool → Type} {b : Bool} {S : α b} {B : Block α false} :
    (B.concat S).last = S := rfl

theorem Block.begin_end {α : Bool → Type} {b : Bool} {S : α b} : (Block.end S).begin = [] := rfl

theorem Block.begin_concat {α : Bool → Type} {b : Bool} {S : α b} {B : Block α false} :
    (B.concat S).begin = B.toList := rfl

theorem Block.toList_concat {α : Bool → Type} {S : α false} {B : Block α false} :
    (B.concat S).toList = B.toList.concat S := rfl

theorem Block.toList_end {α : Bool → Type} {S : α false} : (Block.end S).toList = [S] := rfl

theorem Block.toList_cons {α : Bool → Type} {S : α false} {B : Block α false} :
    (Block.cons S B).toList = S :: B.toList := rfl

theorem Block.concat_end {α : Bool → Type} {S : α false} {b : Bool} {S' : α b} :
    (Block.end S).concat S' = Block.cons S (Block.end S') := rfl

theorem Block.concat_cons {α : Bool → Type} {S : α false} {B : Block α false} {b : Bool} {S' : α b} :
    (Block.cons S B).concat S' = Block.cons S (B.concat S') := rfl

/-- Left-to-right induction: a block is either a single (possibly terminal) statement or a
non-terminal statement in front of a smaller block. -/
def Block.cons_end_induct {α : Bool → Type} {motive : ⦃b : Bool⦄ → Block α b → Sort _}
    {b : Bool} (B : Block α b)
    («end» : ∀ {b : Bool} (S : α b), motive (.end S))
    (cons : ∀ {b : Bool} (S : α false) (B : Block α b), motive B → motive (.cons S B)) :
    motive B :=
  let ⟨Ss, S'⟩ := B
  match Ss with
  | [] => «end» S'
  | S :: Ss => cons S ⟨Ss, S'⟩ (Block.cons_end_induct ⟨Ss, S'⟩ «end» cons)

@[push_cast]
theorem Block.cast_end_eq_end_cast {α : Bool → Type} {b b' : Bool} {S : α b} (b_eq : b = b') :
    b_eq ▸ Block.end S = Block.end (b_eq ▸ S) := by
  cases b_eq
  rfl

@[push_cast]
theorem Block.cast_cons_eq_cons_cast {α : Bool → Type} {b b' : Bool} {S : α false} {B : Block α b}
    (b_eq : b = b') : b_eq ▸ Block.cons S B = Block.cons S (b_eq ▸ B) := by
  cases b_eq
  rfl

/-- `Block.cons_end_induct` specialized to non-terminal blocks, where the motive need not be
index-polymorphic. -/
def Block.cons_end_induct' {α : Bool → Type} {motive : Block α false → Sort _}
    (B : Block α false)
    («end» : ∀ (S : α false), motive (.end S))
    (cons : ∀ (S : α false) (B : Block α false), motive B → motive (.cons S B)) :
    motive B :=
  Block.cons_end_induct (motive := λ ⦃b⦄ B ↦ (b_eq : b = false) → motive (b_eq ▸ B))
    B (λ S b_eq ↦ Block.cast_end_eq_end_cast b_eq ▸ «end» (b_eq ▸ S))
    (λ S B IH b_eq ↦ Block.cast_cons_eq_cons_cast _ ▸ cons S (b_eq ▸ B) (IH b_eq))
    rfl

theorem Block.concat_ofList {α : Bool → Type} {Ss : List (α false)} {S' : α false} {h : Ss ≠ []} :
    (Block.ofList Ss h).concat S' = ⟨Ss, S'⟩ := by
  unfold Block.ofList Block.concat
  simp [List.dropLast_concat_getLast]

theorem Block.sizeOf_ofList {α : Bool → Type} {Ss : List (α false)} [(b : Bool) → SizeOf (α b)]
    {h : Ss ≠ []} :
    sizeOf (Block.ofList Ss h) = 1 + sizeOf Ss.dropLast + sizeOf (Ss.getLast h) := by
  unfold Block.ofList
  rfl

/-- Right-to-left induction: a block is either a single statement or a smaller block extended on the
right. The counterpart of `Block.cons_end_induct`, needed wherever a proof peels the *last*
statement off. -/
def Block.concat_end_induct {α : Bool → Type} [(b : Bool) → SizeOf (α b)]
    {motive : Block α false → Sort _} (B : Block α false)
    («end» : ∀ (S : α false), motive (.end S))
    (concat : ∀ (S : α false) (B : Block α false), motive B → motive (B.concat S)) :
    motive B :=
  match B with
  | ⟨[], S'⟩ => «end» S'
  | ⟨S :: Ss, S'⟩ =>
    Block.concat_ofList ▸ concat S' (Block.ofList (S :: Ss) (by simp_all))
      (Block.concat_end_induct _ «end» concat)
termination_by @sizeOf _ (Block._sizeOf_inst α false) B
decreasing_by
  simp +arith [Block.sizeOf_ofList, List.dropLast_getLast_add_sizeOf_eq]

theorem Block.ofList_cons_of_non_empty {α : Bool → Type} {Ss : List (α false)} {S : α false}
    (h : Ss ≠ []) :
    Block.ofList (S :: Ss) (List.cons_ne_nil _ _) = Block.cons S (Block.ofList Ss h) := by
  unfold ofList cons
  rw [List.dropLast_cons_of_ne_nil h, List.getLast_cons h]

theorem Block.ofList_singleton {α : Bool → Type} {S : α false} :
    Block.ofList [S] (List.cons_ne_nil _ _) = Block.end S := rfl

theorem Block.toList_left_inverse {α : Bool → Type} {Ss : List (α false)} (h : Ss ≠ []) :
    (Block.ofList Ss h).toList = Ss := by
  dsimp [ofList, toList]
  simp [List.dropLast_concat_getLast]

theorem Block.toList_non_empty {α : Bool → Type} {B : Block α false} : B.toList ≠ [] := by
  unfold toList
  simp

theorem Block.toList_right_inverse {α : Bool → Type} {B : Block α false} :
    Block.ofList B.toList Block.toList_non_empty = B := by
  dsimp [ofList, toList]
  simp

theorem Block.ofList_of_toList {α : Bool → Type} {B : Block α false} {Ss : List (α false)}
    (h : B.toList = Ss) : B = Block.ofList Ss (h ▸ Block.toList_non_empty) := by
  replace h : Block.ofList B.toList Block.toList_non_empty = Block.ofList Ss (h ▸ Block.toList_non_empty) := by
    congr
  rwa [Block.toList_right_inverse] at h

end GuardedPlusCal

end
