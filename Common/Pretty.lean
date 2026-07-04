universe u v
variable {α : Type u} {β : Type v}

namespace Std.Format
  def paren' (p : Nat -> Bool) (f : Std.Format) (prec : Nat) : Std.Format := bif p prec then .paren f else f

  def «infixl»  (f : α -> Nat -> Std.Format) (p_op : Nat) (op : String) (x y : α) : Nat -> Std.Format := paren' (· > p_op) (f x p_op ++ " " ++ op ++ " " ++ f y (p_op+1))
  def «infixr»  (f : α -> Nat -> Std.Format) (p_op : Nat) (op : String) (x y : α) : Nat -> Std.Format := paren' (· > p_op) (f x (p_op+1) ++ " " ++ op ++ " " ++ f y p_op)
  def «infix»   (f : α -> Nat -> Std.Format) (p_op : Nat) (op : String) (x y : α) : Nat -> Std.Format := paren' (· > p_op) (f x p_op ++ " " ++ op ++ " " ++ f y p_op)
  def «prefix»  (f : α -> Nat -> Std.Format) (p_op : Nat) (op : String) (x : α)   : Nat -> Std.Format := paren' (· > p_op) (op ++ f x p_op)
  def «postfix» (f : α -> Nat -> Std.Format) (p_op : Nat) (op : String) (x : α)   : Nat -> Std.Format := paren' (· > p_op) (f x p_op ++ op)

  def binder (f : α -> Nat -> Std.Format) (p_op : Nat) (p1 : String) (x : String) (p2 : String) (dom : α) (p3 : String) (pred : α) (p4 : String) : Nat -> Std.Format :=
    paren' (· > p_op) (p1 ++ x ++ p2 ++ f dom 0 ++ p3 ++ f pred 0 ++ p4)

  def binder' (f : α -> Nat -> Std.Format) (f' : β -> Nat -> Std.Format) (p_op : Nat) (p1 : String) (x : String) (p2 : String) (dom : α) (p3 : String) (pred : β) (p4 : String) : Nat -> Std.Format :=
    paren' (· > p_op) (p1 ++ x ++ p2 ++ f dom 0 ++ p3 ++ f' pred 0 ++ p4)

  def indent (n : Int) (f : Format) : Format := (.line ++ f).nest n

  /-- Curly brackets. -/
  @[inline] def cbracket (f : Std.Format) : Std.Format :=
    .bracket "{" f "}"
