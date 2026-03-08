import CustomPrelude
import Extra.Array
import Mathlib.Control.Bifunctor
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Traversable.Instances
import Mathlib.Control.Bitraversable.Basic
import Mathlib.Control.Bitraversable.Instances
import Mathlib.Control.Functor
import Common.Position

namespace SurfacePlusCal
  -- open SurfaceTLAPlus (Expression CommentAnnotation)

  structure Ref (β : Type) : Type where
    name : String
    args : List (List β)
    deriving Repr, Functor, Traversable

  /--
    The second argument of the `multicast` instruction isn't necessarily a valid TLA+ function literal.
    For example: `[m = self, n \in Actors \ {self} |-> Hello(m, n)]`.
  -/
  structure MulticastFilter (α β : Type) : Type where
    binds : List (String × α × Bool × β)
    val : β
    deriving Repr, Inhabited -- , Functor, Traversable

  instance : Bifunctor MulticastFilter where
    bimap f g m := {
      binds := m.binds <&> λ ⟨v, anns, «=|∈», e⟩ ↦ ⟨v, f anns, «=|∈», g e⟩
      val := g m.val
    } @@ posOf m

  instance : Bitraversable MulticastFilter where
    bitraverse f g m :=
      (MulticastFilter.mk · · @@ posOf m)
        <$> traverse (λ ⟨v, anns, «=|∈», e⟩ ↦ (v, ·, «=|∈», ·) <$> f anns <*> g e) m.binds
        <*> g m.val

  inductive Statement (α β : Type) : Type
    | skip
    | goto (label : String)
    | print (e : β)
    | assign (_ : List (Ref β × β))
    | «if» (cond : β) (B₁ : List (String ⊕ Statement α β)) (B₂ : Option (List (String ⊕ Statement α β)))
    | await (e : β)
    | «with» (vars : List (String × Bool × β)) (B : List (String ⊕ Statement α β))
    | assert (e : β)
    | either (branches : List (List (String ⊕ Statement α β)))
    | «while» (cond : β) (B : List (String ⊕ Statement α β))
    | receive (c : Ref β) (r : Ref β)
    | send (c : Ref β) (e : β)
    | multicast (c : String) (filter : MulticastFilter α β)
    deriving Repr, Inhabited

  -- TODO: prove termination at some point
  protected partial def Statement.bimap {α β γ δ} (f : α → β) (g : γ → δ) (S : Statement α γ) : Statement β δ := match_source S with
    | .skip, pos => .skip @@ pos
    | .goto l, pos => .goto l @@ pos
    | .print e, pos => .print (g e) @@ pos
    | .assign asss, pos => .assign (bimap (g <$> ·) g <$> asss) @@ pos
    | .if e B₁ B₂, pos => .if (g e) ((Statement.bimap f g <$> ·) <$> B₁) (((Statement.bimap f g <$> ·) <$> ·) <$> B₂) @@ pos
    | .await e, pos => .await (g e) @@ pos
    | .with vars B, pos => .with (((g <$> ·) <$> ·) <$> vars) ((Statement.bimap f g <$> ·) <$> B) @@ pos
    | .assert e, pos => .assert (g e) @@ pos
    | .either Bs, pos => .either (((Statement.bimap f g <$> ·) <$> ·) <$> Bs) @@ pos
    | .while e B, pos => .while (g e) ((Statement.bimap f g <$> ·) <$> B) @@ pos
    | .receive c r, pos => .receive (g <$> c) (g <$> r) @@ pos
    | .send c e, pos => .send (g <$> c) (g e) @@ pos
    | .multicast c x, pos => .multicast c (bimap f g x) @@ pos

  instance : Bifunctor Statement where
    bimap := Statement.bimap

  local instance {F : Type _ → Type _} [Applicative F] {α} [Inhabited α] : Inhabited (F α) := ⟨pure default⟩ in
  -- TODO: prove termination at some point
  protected partial def Statement.bitraverse {F : Type _ → Type _} [Applicative F] {α β γ δ} (f : α → F β) (g : γ → F δ) (S : Statement α γ) : F (Statement β δ) := match_source S with
    | .skip, pos => pure <| .skip @@ pos
    | .goto l, pos => pure <| .goto l @@ pos
    | .print e, pos => (.print · @@ pos) <$> g e
    | .assign asss, pos =>
        (.assign · @@ pos) <$> traverse (bitraverse (traverse g) g) asss
    | .if e B₁ B₂, pos =>
        (.if · · · @@ pos)
          <$> g e
          <*> traverse (traverse (Statement.bitraverse f g)) B₁
          <*> traverse (traverse (traverse (Statement.bitraverse f g))) B₂
    | .await e, pos => (.await · @@ pos) <$> g e
    | .with vars B, pos =>
        (.with · · @@ pos)
          <$> traverse (traverse (traverse g)) vars
            <*> traverse (traverse (Statement.bitraverse f g)) B
    | .assert e, pos => (.assert · @@ pos) <$> g e
    | .either Bs, pos =>
        (.either · @@ pos) <$> traverse (traverse (traverse (Statement.bitraverse f g))) Bs
    | .while e B, pos =>
        (.while · · @@ pos)
          <$> g e
          <*> traverse (traverse (Statement.bitraverse f g)) B
    | .receive c r, pos => (.receive · · @@ pos) <$> traverse g c <*> traverse g r
    | .send c e, pos => (.send · · @@ pos) <$> traverse g c <*> g e
    | .multicast c x, pos => (.multicast c · @@ pos) <$> bitraverse f g x

  instance : Bitraversable Statement where
    bitraverse := Statement.bitraverse

  structure Declarations (α β : Type) : Type where
    /--
      Variable bindings `(* annotations *) v (("=" | "∈") expr)?`.
      The boolean is `true` if the binding is an equality, `false` otherwise.
    -/
    «variables» : List (String × α × Option (Bool × β))
    channels : List (String × α × List β)
    fifos : List (String × α × List β)
    deriving Repr, Inhabited

  instance : Bifunctor Declarations where
    bimap f g decls := {
      «variables» := Bifunctor.snd (bimap f (Bifunctor.snd g <$> ·)) <$> decls.variables
      channels := Bifunctor.snd (bimap f (g <$> ·)) <$> decls.channels
      fifos := Bifunctor.snd (bimap f (g <$> ·)) <$> decls.fifos
    }

  instance : Bitraversable Declarations where
    bitraverse f g decls := ({«variables» := ·, channels := ·, fifos := ·})
      <$> traverse (bitraverse pure (bitraverse f (traverse (bitraverse pure g)))) decls.variables
      <*> traverse (bitraverse pure (bitraverse f (traverse g))) decls.channels
      <*> traverse (bitraverse pure (bitraverse f (traverse g))) decls.fifos

  structure Process (α β : Type) : Type where
    ann : α
    isFair : Bool
    name : String
    /-- `true` for `=`, `false` for `∈`. -/
    «=|∈» : Bool
    id : β
    localState : Declarations α β
    threads : List (List (String ⊕ Statement α β))
    deriving Repr, Inhabited

  instance : Bifunctor Process where
    bimap f g p := { p with
      ann := f p.ann
      id := g p.id
      localState := bimap f g p.localState
      threads := (Bifunctor.snd (bimap f g) <$> ·) <$> p.threads
    } @@ posOf p

  instance : Bitraversable Process where
    bitraverse f g p :=
      (Process.mk · p.isFair p.name p.«=|∈» · · · @@ posOf p)
        <$> f p.ann
        <*> g p.id
        <*> bitraverse f g p.localState
        <*> traverse (traverse (bitraverse pure (bitraverse f g))) p.threads

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
end SurfacePlusCal
