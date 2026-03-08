import Core.NetworkPlusCal.Syntax
import Core.TypedSetTheory.Syntax

/-! # GoCal -/

namespace GoCal
  namespace Typ
    open TypedSetTheory (Expression Typ)

    protected def initArgs.{v} : Typ → Type v
      | .bool | .int | .str => Option (Expression Typ)
      -- Cannot initialize functions (as in TLA⁺ operators), type variables and opaque types
      | .var _ | .const _ | .operator _ _ | .address => PEmpty.{v + 1}
      -- We can initialize a map (TLA⁺ functions) either by giving it an initial capacity, of by giving it
      -- some basic key-value pairs.
      | .function _ _ => ULift.{v} Nat ⊕ List (Expression.{v} Typ × Expression Typ)
      | .set _ | .seq _ => List (Expression Typ)
      | .tuple _ => List (Expression Typ)
      | .record _ => List (String × Expression Typ) -- Ideally, a list of expressions whose size is the same as the number of fields
      -- The size of the channel is optional: if not specified, it will be synchronous, else buffered (asynchronous)
      | .channel _ => Option (ULift.{v} Nat) ⊕ Expression Typ
  end Typ

  export NetworkPlusCal (
    Block
    Ref ChanRef
  )

  alias LHS := ChanRef

  universe u
  variable (Typ Expr : Type u)

  inductive SelectClause (α : Type u) : Type u
    | receive («to» : List String) (_ : «to».length ≤ 2) («from» : Expr) (B : List α)
    | send («to» : Expr) (e : Expr) (B : List α)
    | default (B : List α)

  inductive SwitchClause (α : Type u) : Type u
    | case (es : List Expr) (B : List α)
    | default (B : List α)

  inductive Statement (init : Typ → Type u) : Type u
    | panic (msg : Expr)
    /-- `var name τ`, `name := make(τ, ...)` or `name := τ(...)` depending on the given `τ` and `args`. -/
    | make (name : String) (τ : Typ) (args : init τ)
    /-- Close the given channel, so that no more messages can be sent through it. -/
    | close (chan : Expr)
    | assign (ref : LHS Typ Expr) (e : Expr)
    | return (e : List Expr)
    | print (e : Expr)
    | go (B : List (Statement init))
    | while (cond : Expr) (B : List (Statement init))
    | if (cond : Expr) (B₁ B₂ : List (Statement init))
    | receive («from» : Expr) («to» : LHS Typ Expr)
    | send («to» : Expr) (e : Expr)
    | select (clauses : List (SelectClause Expr (Statement init)))
    | switch (e : Expr) (clauses : List (SwitchClause Expr (Statement init)))
    deriving Inhabited

  structure Function (init : Typ → Type u) : Type u where
    name : String
    params : List (String × Typ)
    returnType : List Typ
    body : List (Statement Typ Expr init)
