import CustomPrelude
import PlusCalCompiler.SurfaceTLAPlus.Syntax
import Extra.Array

namespace SurfacePlusCal
  abbrev 𝒱 := String
  abbrev ℒ := String

  open SurfaceTLAPlus (Expression CommentAnnotation)

  structure Ref (α : Type) : Type where
    name : 𝒱
    args : List (List (Located (Expression α)))
    deriving Repr, Functor, Traversable

  /--
    The second argument of the `multicast` instruction isn't necessarily a valid TLA+ function literal.
    For example: `[m = self, n \in Actors \ {self} |-> Hello(m, n)]`.
  -/
  structure MulticastFilter (α : Type) : Type where
    binds : List (Located 𝒱 × List α × Bool × Located (Expression α))
    val : Located (Expression α)
    deriving Repr, Inhabited -- , Functor, Traversable

  instance : Functor MulticastFilter where
    map f m := {
      binds := m.binds <&> λ ⟨v, anns, «=|∈», e⟩ ↦ ⟨v, f <$> anns, «=|∈», (f <$> ·) <$> e⟩
      val := (f <$> ·) <$> m.val
    }

  instance : Traversable MulticastFilter where
    traverse f m :=
      MulticastFilter.mk
        <$> traverse (λ ⟨v, anns, «=|∈», e⟩ ↦ (v, ·, «=|∈», ·) <$> traverse f anns <*> traverse (traverse f) e) m.binds
        <*> traverse (traverse f) m.val

  inductive Statement (α : Type) : Type
    | skip
    | goto (label : Located ℒ)
    | print (e : Located (Expression α))
    | assign (_ : List (Located (Ref α) × Located (Expression α)))
    | «if» (cond : Located (Expression α)) (B₁ : List (Located ℒ ⊕ Located (Statement α))) (B₂ : Option (List (Located ℒ ⊕ Located (Statement α))))
    | await (e : Located (Expression α))
    | «with» (vars : List (Located 𝒱 × Located Bool × Located (Expression α))) (B : List (Located ℒ ⊕ Located (Statement α)))
    | assert (e : Located (Expression α))
    | either (branches : List (List (Located ℒ ⊕ Located (Statement α))))
    | «while» (cond : Located (Expression α)) (B : List (Located ℒ ⊕ Located (Statement α)))
    | receive (c : Located (Ref α)) (r : Located (Ref α))
    | send (c : Located (Ref α)) (e : Located (Expression α))
    | multicast (c : Located 𝒱) (filter : Located (MulticastFilter α))
    deriving Repr, Inhabited

  -- TODO: prove termination at some point
  protected partial def Statement.map {α β} (f : α → β) : Statement α → Statement β
    | .skip => .skip
    | .goto l => .goto l
    | .print e => .print ((f <$> ·) <$> e)
    | .assign asss => .assign (bimap ((f <$> ·) <$> ·) ((f <$> ·) <$> ·) <$> asss)
    | .if e B₁ B₂ => .if ((f <$> ·) <$> e) (((Statement.map f <$> ·) <$> ·) <$> B₁) ((((Statement.map f <$> ·) <$> ·) <$> ·) <$> B₂)
    | .await e => .await ((f <$> ·) <$> e)
    | .with vars B => .with (((((f <$> · ) <$> ·) <$> ·) <$> ·) <$> vars) (((Statement.map f <$> ·) <$> ·) <$> B)
    | .assert e => .assert ((f <$> ·) <$> e)
    | .either Bs => .either ((((Statement.map f <$> ·) <$> ·) <$> ·) <$> Bs)
    | .while e B => .while ((f <$> ·) <$> e) (((Statement.map f <$> ·) <$> ·) <$> B)
    | .receive c r => .receive ((f <$> ·) <$> c) ((f <$> ·) <$> r)
    | .send c e => .send ((f <$> ·) <$> c) ((f <$> ·) <$> e)
    | .multicast c g => .multicast c ((f <$> ·) <$> g)

  instance : Functor Statement where
    map := Statement.map

  local instance {F : Type _ → Type _} [Applicative F] {α} : Inhabited (F (Statement α)) := ⟨pure .skip⟩ in
  -- TODO: prove termination at some point
  protected partial def Statement.traverse {F : Type _ → Type _} [Applicative F] {α β} (f : α → F β) : Statement α → F (Statement β)
    | .skip => pure .skip
    | .goto l => pure <| .goto l
    | .print e =>
        .print <$> traverse (traverse f) e
    | .assign asss =>
        .assign <$> traverse (bitraverse (traverse (traverse f)) (traverse (traverse f))) asss
    | .if e B₁ B₂ =>
        .if <$> traverse (traverse f) e
            <*> traverse (traverse (traverse (Statement.traverse f))) B₁
            <*> traverse (traverse (traverse (traverse (Statement.traverse f)))) B₂
    | .await e =>
        .await <$> traverse (traverse f) e
    | .with vars B =>
        .with <$> traverse (traverse (traverse (traverse (traverse f)))) vars
              <*> traverse (traverse (traverse (Statement.traverse f))) B
    | .assert e =>
        .assert <$> traverse (traverse f) e
    | .either Bs =>
        .either <$> traverse (traverse (traverse (traverse (Statement.traverse f)))) Bs
    | .while e B =>
        .while <$> traverse (traverse f) e
               <*> traverse (traverse (traverse (Statement.traverse f))) B
    | .receive c r =>
        .receive <$> traverse (traverse f) c
                 <*> traverse (traverse f) r
    | .send c e =>
        .send <$> traverse (traverse f) c
              <*> traverse (traverse f) e
    | .multicast c g =>
        .multicast c <$> traverse (traverse f) g

  instance : Traversable Statement where
    traverse := Statement.traverse

  structure Declarations (α : Type) : Type where
    /--
      Variable bindings `(* annotations *) v (("=" | "∈") expr)?`.
      The boolean is `true` if the binding is an equality, `false` otherwise.
    -/
    «variables» : List (Located 𝒱 × List α × Option (Bool × Located (Expression α)))
    channels : List (Located 𝒱 × List α × List (Located (Expression α)))
    fifos : List (Located 𝒱 × List α × List (Located (Expression α)))
    deriving Repr, Inhabited

  instance : Functor Declarations where
    map f decls := {
      «variables» := Bifunctor.snd (bimap (f <$> ·) (Bifunctor.snd ((f <$> ·) <$> ·) <$> ·)) <$> decls.variables
      channels := Bifunctor.snd (bimap (f <$> ·) (((f <$> ·) <$> ·) <$> ·)) <$> decls.channels
      fifos := Bifunctor.snd (bimap (f <$> ·) (((f <$> ·) <$> ·) <$> ·)) <$> decls.fifos
    }

  instance : Traversable Declarations where
    traverse f decls := ({«variables» := ·, channels := ·, fifos := ·})
      <$> traverse (bitraverse pure (bitraverse (traverse f) (traverse (bitraverse pure (traverse (traverse f)))))) decls.variables
      <*> traverse (bitraverse pure (bitraverse (traverse f) (traverse (traverse (traverse f))))) decls.channels
      <*> traverse (bitraverse pure (bitraverse (traverse f) (traverse (traverse (traverse f))))) decls.fifos

  structure Process (α : Type) : Type where
    ann : List α
    isFair : Located Bool
    name : Located 𝒱
    /-- `true` for `=`, `false` for `∈`. -/
    «=|∈» : Bool
    id : Located (Expression α)
    localState : Declarations α
    threads : List (List (Located ℒ ⊕ Located (Statement α)))
    deriving Repr, Functor, Traversable, Inhabited

  structure Algorithm (α : Type) : Type where
    isFair : Located Bool
    name : Located 𝒱
    globalState : Declarations α
    processes : List (Process α)
    deriving Repr, Functor, Traversable, Inhabited
end SurfacePlusCal
