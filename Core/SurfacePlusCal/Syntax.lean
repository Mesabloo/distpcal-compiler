module

public import Common.Position
public import Mathlib.Control.Bifunctor
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Control.Traversable.Instances
public import Mathlib.Control.Bitraversable.Basic
public import Mathlib.Control.Bitraversable.Instances

public section


/-!
  The surface syntax of Distributed PlusCal algorithms, as accepted by the parser — not yet
  desugared into explicit-goto form.

  Positions are attached out-of-band via `@@`/`posOf`/`match_source` (`Common/Position.lean`),
  not stored structurally in these types.
-/

namespace SurfacePlusCal

/-- A reference to a (possibly indexed/field-accessed) variable, e.g. `x[1][2].y`. One entry
per path segment, in left-to-right textual order: `.inl` for a `.field` segment, `.inr` for a
`[e₁, …, eₙ]` bracket-index group. -/
structure Ref (β : Type) : Type where
  name : String
  args : List (String ⊕ List β)
  deriving Repr

-- `deriving Functor, Traversable` doesn't apply to structures here -- written by hand instead.
instance : Functor Ref where
  map f r := { r with args := (Sum.map id (f <$> ·)) <$> r.args }

instance : Traversable Ref where
  traverse f r := ({r with args := ·}) <$> traverse (bitraverse pure (traverse f)) r.args

/--
  The filter/value expression of a `multicast`, e.g.
  `[m = self, n \in Actors \ {self} |-> Hello(m, n)]`.
-/
structure MulticastFilter (α β : Type) : Type where
  /-- Each bind is `(name, annotation, isEquality, expr)`; `isEquality` is `true` for `=`, `false` for `\in`. -/
  binds : List (String × α × Bool × β)
  val : β
  deriving Repr, Inhabited

instance : Bifunctor MulticastFilter where
  bimap f g m := {
    binds := m.binds.map λ (v, ann, eq, e) ↦ (v, f ann, eq, g e)
    val := g m.val
  } @@ posOf m

instance : Bitraversable MulticastFilter where
  bitraverse f g m :=
    (MulticastFilter.mk · · @@ posOf m)
      <$> traverse (λ (v, ann, eq, e) ↦ (v, ·, eq, ·) <$> f ann <*> g e) m.binds
      <*> g m.val

/--
  A PlusCal statement. `α` carries comment annotations (as in `SurfaceTLAPlus`), `β` is the
  embedded-expression type. A *block* (the body of `if`/`while`/`with`/`either`/…) is a flat
  `List (String ⊕ Statement α β)`: a leading label and the statement it labels are elements
  of the same list, not yet separated into distinct fields.
-/
inductive Statement (α β : Type) : Type
  | skip
  | goto (label : String)
  | print (e : β)
  | assign (_ : List (Ref β × β))
  | «if» (cond : β) (B₁ : List (String ⊕ Statement α β)) (B₂ : Option (List (String ⊕ Statement α β)))
  | await (e : β)
  /-- `with (* @type: ... *) x = e do B` / `with (* @type: ... *) x ∈ e do B` -- the `Bool` is
  `true` for `=`, `false` for `∈`. -/
  | «with» (vars : List (String × α × Bool × β)) (B : List (String ⊕ Statement α β))
  | assert (e : β)
  | either (branches : List (List (String ⊕ Statement α β)))
  | «while» (cond : β) (B : List (String ⊕ Statement α β))
  | receive (c : Ref β) (r : Ref β)
  | send (c : Ref β) (e : β)
  | multicast (c : String) (filter : MulticastFilter α β)
  deriving Repr, Inhabited

-- `partial`: structural recursion isn't visibly decreasing to Lean here (nested `List`/`Option`
-- occurrences of `Statement`).
protected partial def Statement.bimap {α β γ δ} (f : α → β) (g : γ → δ) (S : Statement α γ) : Statement β δ := match_source S with
  | .skip, pos => .skip @@ pos
  | .goto l, pos => .goto l @@ pos
  | .print e, pos => .print (g e) @@ pos
  | .assign asss, pos => .assign (bimap (g <$> ·) g <$> asss) @@ pos
  | .if e B₁ B₂, pos => .if (g e) ((Statement.bimap f g <$> ·) <$> B₁) (((Statement.bimap f g <$> ·) <$> ·) <$> B₂) @@ pos
  | .await e, pos => .await (g e) @@ pos
  | .with vars B, pos => .with (vars.map λ (x, ann, eq, e) ↦ (x, f ann, eq, g e)) ((Statement.bimap f g <$> ·) <$> B) @@ pos
  | .assert e, pos => .assert (g e) @@ pos
  | .either Bs, pos => .either (((Statement.bimap f g <$> ·) <$> ·) <$> Bs) @@ pos
  | .while e B, pos => .while (g e) ((Statement.bimap f g <$> ·) <$> B) @@ pos
  | .receive c r, pos => .receive (g <$> c) (g <$> r) @@ pos
  | .send c e, pos => .send (g <$> c) (g e) @@ pos
  | .multicast c x, pos => .multicast c (bimap f g x) @@ pos

instance : Bifunctor Statement where
  bimap := Statement.bimap

local instance {F : Type → Type} [Applicative F] {α} [Inhabited α] : Inhabited (F α) := ⟨pure default⟩ in
protected partial def Statement.bitraverse {F : Type → Type} [Applicative F] {α β γ δ} (f : α → F β) (g : γ → F δ) (S : Statement α γ) : F (Statement β δ) := match_source S with
  | .skip, pos => pure <| .skip @@ pos
  | .goto l, pos => pure <| .goto l @@ pos
  | .print e, pos => (.print · @@ pos) <$> g e
  | .assign asss, pos => (.assign · @@ pos) <$> traverse (bitraverse (traverse g) g) asss
  | .if e B₁ B₂, pos =>
    (.if · · · @@ pos) <$> g e
      <*> traverse (traverse (Statement.bitraverse f g)) B₁
      <*> traverse (traverse (traverse (Statement.bitraverse f g))) B₂
  | .await e, pos => (.await · @@ pos) <$> g e
  | .with vars B, pos =>
    (.with · · @@ pos) <$> traverse (λ (x, ann, eq, e) ↦ (x, ·, eq, ·) <$> f ann <*> g e) vars
      <*> traverse (traverse (Statement.bitraverse f g)) B
  | .assert e, pos => (.assert · @@ pos) <$> g e
  | .either Bs, pos => (.either · @@ pos) <$> traverse (traverse (traverse (Statement.bitraverse f g))) Bs
  | .while e B, pos => (.while · · @@ pos) <$> g e <*> traverse (traverse (Statement.bitraverse f g)) B
  | .receive c r, pos => (.receive · · @@ pos) <$> traverse g c <*> traverse g r
  | .send c e, pos => (.send · · @@ pos) <$> traverse g c <*> g e
  | .multicast c x, pos => (.multicast c · @@ pos) <$> bitraverse f g x

instance : Bitraversable Statement where
  bitraverse := Statement.bitraverse

/-- The declarations at the top of an `algorithm` or `process` block. -/
structure Declarations (α β : Type) : Type where
  /-- `(* annotations *) v (("=" | "∈") expr)?`; the `Bool` is `true` for `=`, `false` for `∈`. -/
  «variables» : List (String × α × Option (Bool × β))
  channels : List (String × α × List β)
  fifos : List (String × α × List β)
  deriving Repr, Inhabited

instance : Bifunctor Declarations where
  bimap f g decls := {
    «variables» := decls.variables.map λ (x, ann, e) ↦ (x, f ann, Bifunctor.snd g <$> e)
    channels := decls.channels.map λ (x, ann, es) ↦ (x, f ann, g <$> es)
    fifos := decls.fifos.map λ (x, ann, es) ↦ (x, f ann, g <$> es)
  }

instance : Bitraversable Declarations where
  bitraverse f g decls := ({«variables» := ·, channels := ·, fifos := ·})
    <$> traverse (λ (x, ann, e) ↦ (x, ·, ·) <$> f ann <*> traverse (bitraverse pure g) e) decls.variables
    <*> traverse (λ (x, ann, es) ↦ (x, ·, ·) <$> f ann <*> traverse g es) decls.channels
    <*> traverse (λ (x, ann, es) ↦ (x, ·, ·) <$> f ann <*> traverse g es) decls.fifos

/-- `process(x ∈ S) ⋆ …` / `process(x = e) ⋆ …`. -/
structure Process (α β : Type) : Type where
  ann : α
  /-- Carried through for round-tripping only -- this compiler never acts on it. -/
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

/-- `fifos c₁ : τ₁, …; P₁ ∥ … ∥ Pₙ`. -/
structure Algorithm (α β : Type) : Type where
  /-- Round-tripped only, per `Process.isFair`. -/
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

end
