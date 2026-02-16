import CustomPrelude
import PlusCalCompiler.Position
import PlusCalCompiler.CoreTLAPlus.Syntax
import Mathlib.Logic.Equiv.Defs
import Batteries.Data.HashMap.Basic
import Mathlib.Control.Bifunctor
import Mathlib.Control.Bitraversable.Basic
import Mathlib.Control.Bitraversable.Instances
import Extra.HashMap

/-! # Guarded PlusCal
-/

namespace GuardedPlusCal
  /-- A block is a non-empty sequence of non-terminal objects followed by a potentially terminal object. -/
  structure Block.{u} (α : Bool → Type u) (b : Bool) : Type u where
    begin : List (α false)
    last : α b

  def Block.map.{u} {α β : Bool → Type u} (f : ⦃b : Bool⦄ → α b → β b) {b : Bool} (B : Block α b) : Block β b where
    begin := f (b := _) <$> B.begin
    last := f B.last

  nonrec def Block.traverse.{u} {α β : Bool → Type u} {m : Type u → Type u} [Applicative m] (f : ⦃b : Bool⦄ → α b → m (β b)) {b : Bool} (B : Block α b) : m (Block β b) :=
    Block.mk
      <$> traverse (f (b := _)) B.begin
      <*> f B.last

  abbrev Block.end.{u} {α : Bool → Type u} {b : Bool} (x : α b) : Block α b where
    begin := []
    last := x

  abbrev Block.cons.{u} {α : Bool → Type u} {b : Bool} (x : α false) (B : Block α b) : Block α b where
    begin := x :: B.begin
    last := B.last

  def Block.ofList.{u} {α : Bool → Type u} (xs : List (α false)) (xs_nonempty : xs ≠ []) : Block α false where
    begin := xs.dropLast
    last := xs.getLast xs_nonempty

  def Block.prepend.{u} {α : Bool → Type u} {b} (xs : List (α false)) (B : Block α b) : Block α b where
    begin := xs ++ B.begin
    last := B.last

  @[reducible]
  def Block.concat.{u} {α : Bool → Type u} {b} (B : Block α false) (S : α b) : Block α b where
    begin := B.begin.concat B.last
    last := S

  abbrev Block.toList.{u} {α : Bool → Type u} (B : Block α false) : List (α false) := B.begin.concat B.last

  structure ChanRef.{u} (Expr : Type u) where
    name : String
    args : List Expr
    deriving Functor, Traversable, BEq, Inhabited

  def ChanRef.freeVars.{u} {Expr : Type u} (fv : Expr → List String) (c : ChanRef Expr) : List String :=
    c.name :: c.args.flatMap fv

  structure Ref.{u} (Expr : Type u) where
    name : String
    args : List (List Expr)
    deriving Functor, Traversable, Inhabited

  def Ref.freeVars.{u} {Expr : Type u} (fv : Expr → List String) (r : Ref Expr) : List String :=
    r.name :: r.args.flatMap (List.flatMap fv)

  -- instance : Functor Ref where
  --   map f r := {r with
  --     args := (f <$> ·) <$> r.args
  --   }

  -- instance : Traversable Ref where
  --   traverse f r := Ref.mk r.name <$> traverse (traverse f) r.args

  /--
    A statement in the Guarded PlusCal language.
    The two `Bool` indices respectively indicate whether the statement may appear in block pre-conditions,
    and whether it is terminal (i.e. it appears at the absolute end of the block).
  -/
  -- TODO: can we represent ONLY syntax trees that are well-formed according to the rules of PlusCal/TLA+?
  -- For example:
  -- * Is it possible to encode disjointness of variables and `with` binders?
  -- * Can we have that all labels exist somewhere in the algorithm/process?
  -- * etc. etc.
  inductive Statement.{u} (Typ Expr : Type u) : Bool → Bool → Type u
    -- Statements that appear in pre-conditions
    | «let» (pos : SourceSpan) (name : String) (τ : Typ) («=|∈» : Bool) (e : Expr) : Statement Typ Expr true false
    | await (pos : SourceSpan) (e : Expr) : Statement Typ Expr true false
    | receive (pos : SourceSpan) (chan : ChanRef Expr) (ref : Ref Expr) : Statement Typ Expr true false
    -- Other statements
    | skip (pos : SourceSpan) : Statement Typ Expr false false
    | goto (pos : SourceSpan) (label : String) : Statement Typ Expr false true
    | print (pos : SourceSpan) (e : Expr) : Statement Typ Expr false false
    | assert (pos : SourceSpan) (e : Expr) : Statement Typ Expr false false
    | send (pos : SourceSpan) (chan : ChanRef Expr) (e : Expr) : Statement Typ Expr false false
    | multicast (pos : SourceSpan) (chan : String) (filter : List (String × Typ × Bool × Expr)) (e : Expr) : Statement Typ Expr false false
    | assign (pos : SourceSpan) (ref : Ref Expr) (e : Expr) : Statement Typ Expr false false

  -- This is not ONLY the free vars of the statement, but something close
  def Statement.freeVars.{u} {Typ Expr : Type u} (f : Expr → List String) : {b b' : Bool} → Statement Typ Expr b b' → List String
    | false, false, .skip _ => []
    | false, true, .goto _ _ => []
    | false, false, .print _ e => f e
    | false, false, .assert _ e => f e
    | false, false, .send _ chan e => chan.freeVars f ++ f e
    | false, false, .multicast _ chan filter e => chan :: filter.flatMap (λ ⟨_, _, _, e⟩ ↦ f e) ++ (f e \ filter.map Prod.fst)
    | false, false, .assign _ ref e => ref.freeVars f ++ f e
    | true, false, .let _ x _ _ e => x :: f e
    | true, false, .await _ e => f e
    | true, false, .receive _ chan ref => chan.freeVars f ++ ref.freeVars f

  instance instBifunctorStatement {b b'} : Bifunctor (Statement · · b b') where
    bimap f g
      | .let pos name τ «=|∈» e => .let pos name (f τ) «=|∈» (g e)
      | .await pos e => .await pos (g e)
      | .receive pos chan ref => .receive pos (g <$> chan) (g <$> ref)
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
      | .receive pos chan ref => .receive pos <$> traverse g chan <*> traverse g ref
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

  abbrev Thread.{u} (Typ Expr : Type u) : Type u := List (AtomicBlock Typ Expr)

  instance : Bifunctor Thread where
    bimap f g := List.map (bimap f g)
  -- TODO: prove that it is lawful

  instance : Bitraversable Thread where
    bitraverse f g := List.traverse (bitraverse f g)
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
