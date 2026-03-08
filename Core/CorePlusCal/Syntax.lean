import CustomPrelude
import Extra.Array
import Mathlib.Control.Bifunctor
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Traversable.Instances
import Mathlib.Control.Bitraversable.Basic
import Mathlib.Control.Bitraversable.Instances
import Mathlib.Control.Functor
import Common.Position
import Core.SurfacePlusCal.Syntax

/-! # Core PlusCal

  `SurfacePlusCal`, but with all `goto` statements explicit and at the end of blocks.
-/
namespace CorePlusCal
  open SurfacePlusCal (Ref MulticastFilter Declarations)

  mutual
    inductive Statement (α β : Type) : Bool → Type
      | goto (label : String) : Statement α β true
      | skip : Statement α β false
      | print (e : β) : Statement α β false
      | assign (_ : List (Ref β × β)) : Statement α β false
      | «if» {b} (cond : β) (B₁ B₂ : Block α β b) : Statement α β b
      | await (e : β) : Statement α β false
      | «with» (vars : List (String × Bool × β)) (B : Block α β false) : Statement α β false
      | assert (e : β) : Statement α β false
      | either {b} (branches : Branches α β b) : Statement α β b
      | «while» (cond : β) (B : Block α β false) : Statement α β false
      | receive (c : Ref β) (r : Ref β) : Statement α β false
      | send (c : Ref β) (e : β) : Statement α β false
      | multicast (c : String) (filter : MulticastFilter α β) : Statement α β false
      deriving Repr

    -- mutualize with `List` as well...

    /-- A block is a non-empty sequence of non-terminal objects followed by a potentially terminal object. -/
    inductive Block (α β : Type) : Bool → Type where
      | mk {b} (begin : List (Statement α β false)) («end» : Statement α β b) : Block α β b
      deriving Repr

    inductive Branches (α β : Type) : Bool → Type where
      | either {b} : Block α β b → Branches α β b
      | or {b} : Block α β b → Branches α β b → Branches α β b
  end

  protected abbrev Block.begin {α β b} : Block α β b → List (Statement α β false)
    | ⟨begin, _⟩ => begin

  protected abbrev Block.end {α β b} : Block α β b → Statement α β b
    | ⟨_, «end»⟩ => «end»

  instance {α β b} : Inhabited (Statement α β b) where
    default := match b with
      | true => .goto default
      | false => .skip

  instance {α β b} : Inhabited (Block α β b) where
    default := .mk default default

  instance {α β b} : Inhabited (Branches α β b) where
    default := .either default

  mutual
    partial def Statement.bimap {b} {α β γ δ} (f : α → β) (g : γ → δ) (S : Statement α γ b) : Statement β δ b := match_source S with
      | .skip, pos => .skip @@ pos
      | .goto l, pos => .goto l @@ pos
      | .print e, pos => .print (g e) @@ pos
      | .assign asss, pos => .assign (bimap (g <$> ·) g <$> asss) @@ pos
      | .if e B₁ B₂, pos => .if (g e) (Block.bimap f g B₁) (Block.bimap f g B₂) @@ pos
      | .await e, pos => .await (g e) @@ pos
      | .with vars B, pos => .with (((g <$> ·) <$> ·) <$> vars) (Block.bimap f g B) @@ pos
      | .assert e, pos => .assert (g e) @@ pos
      | .either Bs, pos => .either (Branches.bimap f g Bs) @@ pos
      | .while e B, pos => .while (g e) (Block.bimap f g B) @@ pos
      | .receive c r, pos => .receive (g <$> c) (g <$> r) @@ pos
      | .send c e, pos => .send (g <$> c) (g e) @@ pos
      | .multicast c x, pos => .multicast c (bimap f g x) @@ pos

    partial def Block.bimap {α β γ δ b} (f : α → β) (g : γ → δ) (B : Block α γ b) : Block β δ b :=
      ⟨Statement.bimap f g <$> B.begin, Statement.bimap f g B.«end»⟩

    partial def Branches.bimap {α β γ δ b} (f : α → β) (g : γ → δ) : Branches α γ b → Branches β δ b
      | .either B => .either (Block.bimap f g B)
      | .or B Br => .or (Block.bimap f g B) (Branches.bimap f g Br)
  end

  instance {b} : Bifunctor (Statement · · b) where
    bimap := Statement.bimap

  instance {b} : Bifunctor (Block · · b) where
    bimap := Block.bimap

  instance {b} : Bifunctor (Branches · · b) where
    bimap := Branches.bimap

  local instance {F : Type _ → Type _} [Applicative F] {α} [Inhabited α] : Inhabited (F α) := ⟨pure default⟩ in
  mutual
    partial def Statement.bitraverse {F : Type _ → Type _} [Applicative F] {α β γ δ b} (f : α → F β) (g : γ → F δ) (S : Statement α γ b) : F (Statement β δ b) := match_source S with
      | .skip, pos => pure <| .skip @@ pos
      | .goto l, pos => pure <| .goto l @@ pos
      | .print e, pos => (.print · @@ pos) <$> g e
      | .assign asss, pos =>
        (.assign · @@ pos) <$> traverse (bitraverse (traverse g) g) asss
      | .if e B₁ B₂, pos =>
        (.if · · · @@ pos)
          <$> g e
          <*> Block.bitraverse f g B₁
          <*> Block.bitraverse f g B₂
      | .await e, pos => (.await · @@ pos) <$> g e
      | .with vars B, pos =>
        (.with · · @@ pos)
          <$> traverse (traverse (traverse g)) vars
          <*> Block.bitraverse f g B
      | .assert e, pos => (.assert · @@ pos) <$> g e
      | .either Bs, pos => (.either · @@ pos) <$> Branches.bitraverse f g Bs
      | .while e B, pos => (.while · · @@ pos) <$> g e <*> Block.bitraverse f g B
      | .receive c r, pos => (.receive · · @@ pos) <$> traverse g c <*> traverse g r
      | .send c e, pos => (.send · · @@ pos) <$> traverse g c <*> g e
      | .multicast c x, pos => (.multicast c · @@ pos) <$> bitraverse f g x

    partial def Block.bitraverse {F : Type _ → Type _} [Applicative F] {α β γ δ b} (f : α → F β) (g : γ → F δ) (B : Block α γ b) : F (Block β δ b) :=
      Block.mk
        <$> traverse (Statement.bitraverse f g) B.begin
        <*> Statement.bitraverse f g B.end

    partial def Branches.bitraverse {F : Type _ → Type _} [Applicative F] {α β γ δ b} (f : α → F β) (g : γ → F δ) : Branches α γ b → F (Branches β δ b)
      | .either B => .either <$> Block.bitraverse f g B
      | .or B Br => .or <$> Block.bitraverse f g B <*> Branches.bitraverse f g Br
  end

  instance {b} : Bitraversable (Statement · · b) where
    bitraverse := Statement.bitraverse

  instance {b} : Bitraversable (Block · · b) where
    bitraverse := Block.bitraverse

  instance {b} : Bitraversable (Branches · · b) where
    bitraverse := Branches.bitraverse

  structure Process (α β : Type) : Type where
    ann : α
    isFair : Bool
    name : String
    /-- `true` for `=`, `false` for `∈`. -/
    «=|∈» : Bool
    id : β
    localState : Declarations α β
    threads : List (Block α β true)
    deriving Repr, Inhabited

  instance : Bifunctor Process where
    bimap f g p := { p with
      ann := f p.ann
      id := g p.id
      localState := bimap f g p.localState
      threads := Block.bimap f g <$> p.threads
    } @@ posOf p

  instance : Bitraversable Process where
    bitraverse f g p :=
      (Process.mk · p.isFair p.name p.«=|∈» · · · @@ posOf p)
        <$> f p.ann
        <*> g p.id
        <*> bitraverse f g p.localState
        <*> traverse (Block.bitraverse f g) p.threads

  structure Algorithm (α β : Type) : Type where
    isFair : Bool
    name : String
    globalState : Declarations α β
    processes : List (Process α β)
    deriving Repr, Inhabited

  instance : Bifunctor Algorithm where
    bimap f g a := { a with
      globalState := bimap f g a.globalState
      processes := bimap f g <$> a.processes
    } @@ posOf a

  instance : Bitraversable Algorithm where
    bitraverse f g a :=
      (Algorithm.mk a.isFair a.name · · @@ posOf a)
        <$> bitraverse f g a.globalState
        <*> traverse (bitraverse f g) a.processes
end CorePlusCal
