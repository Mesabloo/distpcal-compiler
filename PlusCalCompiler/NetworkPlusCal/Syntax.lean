import CustomPrelude
import PlusCalCompiler.Position
import PlusCalCompiler.CoreTLAPlus.Syntax
import Mathlib.Logic.Equiv.Defs
import Batteries.Data.HashMap.Basic
import Mathlib.Control.Bifunctor
import Mathlib.Control.Bitraversable.Basic
import Mathlib.Control.Bitraversable.Instances
import Extra.HashMap
import PlusCalCompiler.GuardedPlusCal.Syntax

/-! # Network PlusCal
-/

namespace NetworkPlusCal
  export GuardedPlusCal (
    Block Block.map Block.traverse Block.end Block.cons Block.ofList Block.toList Block.concat
    ChanRef Ref
  )

  /--
    A statement in the Guarded PlusCal language.
    The two `Bool` indices respectively indicate whether the statement may appear in block pre-conditions,
    and whether it is terminal (i.e. it appears at the absolute end of the block).
  -/
  inductive Statement.{u} (Typ Expr : Type u) : Bool → Bool → Type u
    -- Statements that appear in pre-conditions
    | «let» (pos : SourceSpan) (name : String) (τ : Typ) («=|∈» : Bool) (e : Expr) : Statement Typ Expr true false
    | await (pos : SourceSpan) (e : Expr) : Statement Typ Expr true false
    -- Other statements
    | skip (pos : SourceSpan) : Statement Typ Expr false false
    | goto (pos : SourceSpan) (label : String) : Statement Typ Expr false true
    | print (pos : SourceSpan) (e : Expr) : Statement Typ Expr false false
    | assert (pos : SourceSpan) (e : Expr) : Statement Typ Expr false false
    | send (pos : SourceSpan) (chan : ChanRef Expr) (e : Expr) : Statement Typ Expr false false
    | multicast (pos : SourceSpan) (chan : String) (filter : List (String × Typ × Bool × Expr)) (e : Expr) : Statement Typ Expr false false
    | assign (pos : SourceSpan) (ref : Ref Expr) (e : Expr) : Statement Typ Expr false false

  instance instBifunctorStatement {b b'} : Bifunctor (Statement · · b b') where
    bimap f g
      | .let pos name τ «=|∈» e => .let pos name (f τ) «=|∈» (g e)
      | .await pos e => .await pos (g e)
      | .skip pos => .skip pos
      | .goto pos label => .goto pos label
      | .print pos e => .print pos (g e)
      | .assert pos e => .assert pos (g e)
      | .send pos chan e => .send pos (g <$> chan) (g e)
      | .multicast pos chan filter e => .multicast pos chan (filter.map λ ⟨name, τ, «=|∈», e⟩ ↦ ⟨name, f τ, «=|∈», g e⟩) (g e)
      | .assign pos ref e => .assign pos (g <$> ref) (g e)
  -- TODO: prove that it is lawful

  instance instBitraversableStatement {b b'} : Bitraversable (Statement · · b b') where
    bitraverse f g
      | .let pos name τ «=|∈» e => (.let pos name · «=|∈» ·) <$> f τ <*> g e
      | .await pos e => .await pos <$> g e
      | .skip pos => pure (.skip pos)
      | .goto pos label => pure (.goto pos label)
      | .print pos e => .print pos <$> g e
      | .assert pos e => .print pos <$> g e
      | .send pos chan e => .send pos <$> traverse g chan <*> g e
      | .multicast pos chan filter e => .multicast pos chan <$> traverse (λ ⟨name, τ, «=|∈», e⟩ ↦ (name, ·, «=|∈», ·) <$> f τ <*> g e) filter <*> g e
      | .assign pos ref e => .assign pos <$> traverse g ref <*> g e
  -- TODO: prove that it is lawful

  structure AtomicBranch.{u} (Typ Expr : Type u) : Type u where
    precondition : Option (Block (Statement Typ Expr true) false)
    action : Block (Statement Typ Expr false) true

  instance : Bifunctor AtomicBranch where
    bimap f g branch := {
      precondition := Block.map (λ ⦃_⦄ ↦ instBifunctorStatement.bimap f g) <$> branch.precondition
      action := Block.map (λ ⦃_⦄ ↦ instBifunctorStatement.bimap f g) branch.action
    }
  -- TODO: prove that it is lawful

  instance : Bitraversable AtomicBranch where
    bitraverse f g branch :=
      AtomicBranch.mk
        <$> traverse (Block.traverse (λ ⦃_⦄ ↦ instBitraversableStatement.bitraverse f g)) branch.precondition
        <*> Block.traverse (λ ⦃_⦄ ↦ instBitraversableStatement.bitraverse f g) branch.action
  -- TODO: prove that it is lawful

  structure AtomicBlock.{u} (Typ Expr : Type u) : Type u where
    label : String
    branches : List (AtomicBranch Typ Expr)

  instance : Bifunctor AtomicBlock where
    bimap f g B := { B with
      branches := bimap f g <$> B.branches
    }
  -- TODO: prove that it is lawful

  instance : Bitraversable AtomicBlock where
    bitraverse f g B :=
      AtomicBlock.mk B.label <$> traverse (bitraverse f g) B.branches
  -- TODO: prove that it is lawful

  inductive Thread.{u} (Typ Expr : Type u) : Type u
    | code (blocks : List (AtomicBlock Typ Expr))
    | rx (chan : ChanRef Expr) (var : String) (τ : Typ) (inbox : String)

  instance : Bifunctor Thread where
    bimap f g
      | .code bs => .code <| bs.map (bimap f g)
      | .rx chan var τ inbox => .rx (g <$> chan) var (f τ) inbox
  -- TODO: prove that it is lawful

  instance : Bitraversable Thread where
    bitraverse f g
      | .code bs => .code <$> traverse (bitraverse f g) bs
      | .rx chan var τ inbox => (.rx · var · inbox) <$> traverse g chan <*> f τ
  -- TODO: prove that it is lawful

  structure Process.{u} (Typ Expr : Type u) : Type u where
    name : String
    mailbox : Option Expr
    locals : Std.HashMap String (Typ × Bool × Expr)
    threads : List (Thread Typ Expr)

  instance : Bifunctor Process where
    bimap f g P := {P with
      mailbox := g <$> P.mailbox
      locals := P.locals.map λ _ ⟨τ, «=|∈», e⟩ ↦ ⟨f τ, «=|∈», g e⟩
      threads := bimap f g <$> P.threads
    }
  -- TODO: prove that it is lawful

  instance : Bitraversable Process where
    bitraverse f g P :=
      Process.mk P.name
        <$> traverse g P.mailbox
        <*> P.locals.traverseWithKey (λ _ ⟨τ, «=|∈», e⟩ ↦ (·, «=|∈», ·) <$> f τ <*> g e)
        <*> traverse (bitraverse f g) P.threads
  -- TODO: prove that it is lawful

  structure Algorithm.{u} (Typ Expr : Type u) : Type u where
    name : String
    channels : Std.HashMap String (Typ × List Expr)
    fifos : Std.HashMap String (Typ × List Expr)
    procs : List (Process Typ Expr)

  instance : Bifunctor Algorithm where
    bimap f g A := {A with
      channels := A.channels.map λ _ ⟨τ, es⟩ ↦ ⟨f τ, g <$> es⟩
      fifos := A.fifos.map λ _ ⟨τ, es⟩ ↦ ⟨f τ, g <$> es⟩
      procs := bimap f g <$> A.procs
    }
  -- TODO: prove that it is lawful

  instance : Bitraversable Algorithm where
    bitraverse f g A :=
      Algorithm.mk A.name
        <$> A.channels.traverseWithKey (λ _ ↦ bitraverse f (traverse g))
        <*> A.fifos.traverseWithKey (λ _ ↦ bitraverse f (traverse g))
        <*> traverse (bitraverse f g) A.procs
  -- TODO: prove that it is lawful

  /-- There are no terminal `Statement`s that can appear in the pre-condition of a block. -/
  private example {Typ Expr} : Statement Typ Expr true true ≃ PEmpty where
    toFun := nofun
    invFun := nofun
    left_inv := by rintro ⟨_|_⟩
    right_inv := by rintro ⟨_|_⟩
