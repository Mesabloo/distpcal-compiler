import CustomPrelude
import Common.Position
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

  structure ChanRef.{u} (Typ Expr : Type u) where
    name : String
    τ : Typ
    args : List Expr
    deriving BEq, Inhabited

  instance : Bifunctor ChanRef where
    bimap f g c := {
      name := c.name
      τ := f c.τ
      args := g <$> c.args
    }

  instance : Bitraversable ChanRef where
    bitraverse f g c :=
      ChanRef.mk c.name
        <$> f c.τ
        <*> traverse g c.args

  def ChanRef.freeVars.{u} {Expr Typ : Type u} (fv : Expr → List String) (c : ChanRef Typ Expr) : List String :=
    c.name :: c.args.flatMap fv

  structure Ref.{u} (Typ Expr : Type u) where
    name : String
    τ : Typ
    args : List (List Expr)
    deriving Inhabited

  instance : Bifunctor Ref where
    bimap f g r := {
      name := r.name
      τ := f r.τ
      args := (g <$> ·) <$> r.args
    }

  instance : Bitraversable Ref where
    bitraverse f g r :=
      Ref.mk r.name
        <$> f r.τ
        <*> traverse (traverse g) r.args

  def Ref.freeVars.{u} {Expr Typ : Type u} (fv : Expr → List String) (r : Ref Typ Expr) : List String :=
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
    | «let» (name : String) (τ : Typ) («=|∈» : Bool) (e : Expr) : Statement Typ Expr true false
    | await (e : Expr) : Statement Typ Expr true false
    | receive (chan : ChanRef Typ Expr) (ref : Ref Typ Expr) : Statement Typ Expr true false
    -- Other statements
    | skip : Statement Typ Expr false false
    | goto (label : String) : Statement Typ Expr false true
    | print (e : Expr) : Statement Typ Expr false false
    | assert (e : Expr) : Statement Typ Expr false false
    | send (chan : ChanRef Typ Expr) (e : Expr) : Statement Typ Expr false false
    | multicast (chan : String) (filter : List (String × Typ × Bool × Expr)) (e : Expr) : Statement Typ Expr false false
    | assign (ref : Ref Typ Expr) (e : Expr) : Statement Typ Expr false false

  instance instInhabitedTerminalStatement.{u} {Typ Expr : Type u} : Inhabited (Statement Typ Expr false true) where
    default := .goto default
  instance instInhabitedGuardStatement.{u} {Typ Expr : Type u} [Inhabited Expr] : Inhabited (Statement Typ Expr true false) where
    default := .await default
  instance instInhabitedExecutionStatement.{u} {Typ Expr : Type u} : Inhabited (Statement Typ Expr false false) where
    default := .skip

  -- This is not ONLY the free vars of the statement, but something close
  def Statement.freeVars.{u} {Typ Expr : Type u} (f : Expr → List String) : {b b' : Bool} → Statement Typ Expr b b' → List String
    | false, false, .skip => []
    | false, true, .goto _ => []
    | false, false, .print e => f e
    | false, false, .assert e => f e
    | false, false, .send chan e => chan.freeVars f ++ f e
    | false, false, .multicast chan filter e => chan :: filter.flatMap (λ ⟨_, _, _, e⟩ ↦ f e) ++ (f e \ filter.map Prod.fst)
    | false, false, .assign ref e => ref.freeVars f ++ f e
    | true, false, .let x _ _ e => x :: f e
    | true, false, .await e => f e
    | true, false, .receive chan ref => chan.freeVars f ++ ref.freeVars f

  -- def Statement.traverseExpr {Typ Expr Expr' : Type} {F : Type → Type} [Applicative F] [Inhabited Expr'] {b b'} (f : Expr → F Expr') (S : Statement Typ Expr b b') : F (Statement Typ Expr' b b') := match_source (indices := [3]) b, b', S with
  --     | true, false, .let name τ «=|∈» e, pos => (.let name τ «=|∈» · @@ pos) <$> f e
  --     | true, false, .await e, pos => (.await · @@ pos) <$> f e
  --     | true, false, .receive chan ref, pos => (.receive · · @@ pos) <$> traverse f chan <*> traverse f ref
  --     | false, false, .skip, pos => pure (.skip @@ pos)
  --     | false, true, .goto label, pos => pure (.goto label @@ pos)
  --     | false, false, .print e, pos => (.print · @@ pos) <$> f e
  --     | false, false, .assert e, pos => (.assert · @@ pos) <$> f e
  --     | false, false, .send chan e, pos => (.send · · @@ pos) <$> traverse f chan <*> f e
  --     | false, false, .multicast chan filter e, pos => (.multicast chan · · @@ pos) <$> traverse (λ ⟨name, τ, «=|∈», e⟩ ↦ (name, τ, «=|∈», ·) <$> f e) filter <*> f e
  --     | false, false, .assign ref e, pos => (.assign · · @@ pos) <$> traverse f ref <*> f e

  instance instBifunctorStatement {b b'} : Bifunctor (Statement · · b b') where
    bimap f g S := match_source S with
      | .let name τ «=|∈» e, pos => .let name (f τ) «=|∈» (g e) @@ pos
      | .await e, pos => .await (g e) @@ pos
      | .receive chan ref, pos => .receive (bimap f g chan) (bimap f g ref) @@ pos
      | .skip, pos => .skip @@ pos
      | .goto label, pos => .goto label @@ pos
      | .print e, pos => .print (g e) @@ pos
      | .assert e, pos => .assert (g e) @@ pos
      | .send chan e, pos => .send (bimap f g chan) (g e) @@ pos
      | .multicast chan filter e, pos => .multicast chan (filter.map λ ⟨name, τ, «=|∈», e⟩ ↦ ⟨name, f τ, «=|∈», g e⟩) (g e) @@ pos
      | .assign ref e, pos => .assign (bimap f g ref) (g e) @@ pos
  -- TODO: prove that it is lawful

  instance instBitraversableStatement {b b'} : Bitraversable (Statement · · b b') where
    bitraverse f g S := match_source S with
      | .let name τ «=|∈» e, pos => (.let name · «=|∈» · @@ pos) <$> f τ <*> g e
      | .await e, pos => (.await · @@ pos) <$> g e
      | .receive chan ref, pos => (.receive · · @@ pos) <$> bitraverse f g chan <*> bitraverse f g ref
      | .skip, pos => pure (.skip @@ pos)
      | .goto label, pos => pure (.goto label @@ pos)
      | .print e, pos => (.print · @@ pos) <$> g e
      | .assert e, pos => (.assert · @@ pos) <$> g e
      | .send chan e, pos => (.send · · @@ pos) <$> bitraverse f g chan <*> g e
      | .multicast chan filter e, pos => (.multicast chan · · @@ pos) <$> traverse (λ ⟨name, τ, «=|∈», e⟩ ↦ (name, ·, «=|∈», ·) <$> f τ <*> g e) filter <*> g e
      | .assign ref e, pos => (.assign · · @@ pos) <$> bitraverse f g ref <*> g e
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
