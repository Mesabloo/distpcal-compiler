module

public import Core.TypedPlusCal.Syntax
public import Core.TypedTLAPlus.Coercion
public import Core.ComputablePlusCal.Syntax
public import Mathlib.Control.Bifunctor
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Control.Bitraversable.Basic
public import Mathlib.Control.Bitraversable.Instances

@[expose] public section


/-!
  The output of `Computable2Guarded`: every guard (`await`/`receive`/`with`) sits at the very
  start of its atomic branch. Reuses `ElaboratedPlusCal.Ref`/`.Multicast` rather than
  redefining them — `Computable2Guarded`'s `Ref` field-access fix (`Core/TypedPlusCal/Syntax.lean`)
  flows through automatically. Unlike `ElaboratedPlusCal`, `Statement` here is genuinely flat: by
  this stage every `if`/`while`/`either` has already been rewritten away into `AtomicBranch`'s
  precondition/action split (`𝒞_cflow`/`𝒞_flat`/`𝒞_reord`), so no constructor embeds a nested
  `Block`/`Branches` the way `CorePlusCal.Statement.if`/`.while`/`.either` do — no `mutual`,
  `partial`, or position tracking is needed anywhere in this file (`ElaboratedPlusCal` carries
  none either, see `Typed2Computable/PlusCal.lean`'s module doc).

  `Block`, unlike every other type here, is generic over an arbitrary index family
  `α : Bool → Type`, not `(Typ Expr : Type)`, since it's purely structural and doesn't reference
  `Typ`/`Expr` at all. `Block (Statement Typ Expr true) false`/`Block (Statement Typ Expr false)
  true` both instantiate it.

  Pinned at `ComputableTLAPlus.Typ`/`ComputablePlusCal.Expression` for this pass's actual use
  (`ComputableGuardedPlusCal` below), the same way `Core/ComputablePlusCal/Syntax.lean` pins the
  shared `ElaboratedPlusCal` layer rather than forking a monomorphic copy.
-/

namespace GuardedPlusCal

/-- A (possibly empty) sequence of non-terminal `α false` objects followed by a potentially
terminal `α b`. Generic over the index family `α` itself, not `Typ`/`Expr` — see the module doc
above. -/
structure Block (α : Bool → Type) (b : Bool) : Type where
  begin : List (α false)
  last : α b

/-- `deriving Repr` can't discharge this — `α`'s `Repr` instance is only known per-index
(`∀ b, Repr (α b)`), not as one instance for the whole family. -/
instance {α : Bool → Type} [∀ b, Repr (α b)] {b : Bool} : Repr (Block α b) where
  reprPrec B n := reprPrec (B.begin, B.last) n

def Block.map {α β : Bool → Type} (f : ⦃b : Bool⦄ → α b → β b) {b : Bool} (B : Block α b) : Block β b where
  begin := f (b := _) <$> B.begin
  last := f B.last

def Block.traverse {α β : Bool → Type} {m : Type → Type} [Applicative m]
    (f : ⦃b : Bool⦄ → α b → m (β b)) {b : Bool} (B : Block α b) : m (Block β b) :=
  Block.mk <$> B.begin.traverse (f (b := _)) <*> f B.last

abbrev Ref (Typ Expr : Type) := ElaboratedPlusCal.Ref Typ Expr
abbrev Multicast (Typ Expr : Type) := CorePlusCal.Multicast Typ Expr

/-- `ElaboratedPlusCal.Ref` carries no `Bifunctor`/`Bitraversable` instance (it has an extra
`baseType : τ` field, same reason `Typed2Computable/PlusCal.lean`'s `Ref.toComputable` is
hand-written rather than a generic `bitraverse` call) — small local helpers instead, used only by
`Statement`'s instances below, not registered as global instances. -/
def Ref.bimap {Typ Typ' Expr Expr'} (f : Typ → Typ') (g : Expr → Expr') (r : Ref Typ Expr) :
    Ref Typ' Expr' :=
  { name := r.name, args := Sum.map id g <$> r.args, baseType := f r.baseType }

def Ref.bitraverse {Typ Typ' Expr Expr'} {m : Type → Type} [Applicative m]
    (f : Typ → m Typ') (g : Expr → m Expr') (r : Ref Typ Expr) : m (Ref Typ' Expr') :=
  (λ args baseType ↦ { name := r.name, args, baseType }) <$> traverse (Sum.bitraverse pure g) r.args <*> f r.baseType

/-- A statement in the Guarded PlusCal language. The first `Bool` (`guardClass`) is `true` for a
statement allowed in a branch's precondition (`with`/`await`/`receive`); the second (`terminal`)
is `true` only for `goto`, which always ends a branch's action block. -/
inductive Statement (Typ Expr : Type) : Bool → Bool → Type
  /-- Body-less: a `with`'s nested body is un-nested into flat sequencing by `𝒞_flat`/`𝒞_reord`
  before reaching this type (`bound` is `true` for `=`, `false` for `∈`). `ann` carries `name`'s
  type through unchanged from `ComputablePlusCal.Statement.with` — every earlier pass keeps a
  fresh binder's type available this way, so this stage shouldn't be the one that drops it. -/
  | «with» (name : String) (ann : Typ) (bound : Bool) (e : Expr) : Statement Typ Expr true false
  | await (e : Expr) : Statement Typ Expr true false
  | receive (c r : Ref Typ Expr) (coe : TypedTLAPlus.Coercion) : Statement Typ Expr true false
  | skip : Statement Typ Expr false false
  | print (e : Expr) : Statement Typ Expr false false
  | assert (e : Expr) : Statement Typ Expr false false
  | send (c : Ref Typ Expr) (e : Expr) : Statement Typ Expr false false
  | multicast (c : String) (filter : Multicast Typ Expr) : Statement Typ Expr false false
  /-- Single target — parallel assignment is eliminated by `𝒞_par` before reaching this type. -/
  | assign (r : Ref Typ Expr) (e : Expr) : Statement Typ Expr false false
  | goto (label : String) : Statement Typ Expr false true
  deriving Repr

instance {Typ Expr} : Inhabited (Statement Typ Expr false true) where
  default := .goto default

instance {Typ Expr} [Inhabited Expr] : Inhabited (Statement Typ Expr true false) where
  default := .await default

instance {Typ Expr} : Inhabited (Statement Typ Expr false false) where
  default := .skip

instance instBifunctorStatement {b b'} : Bifunctor (Statement · · b b') where
  bimap f g := λ
    | .with name ann bound e => .with name (f ann) bound (g e)
    | .await e => .await (g e)
    | .receive c r coe => .receive (Ref.bimap f g c) (Ref.bimap f g r) coe
    | .skip => .skip
    | .print e => .print (g e)
    | .assert e => .assert (g e)
    | .send c e => .send (Ref.bimap f g c) (g e)
    | .multicast c filter => .multicast c (bimap f g filter)
    | .assign r e => .assign (Ref.bimap f g r) (g e)
    | .goto label => .goto label

instance instBitraversableStatement {b b'} : Bitraversable (Statement · · b b') where
  bitraverse f g := λ
    | .with name ann bound e => (.with name · bound ·) <$> f ann <*> g e
    | .await e => .await <$> g e
    | .receive c r coe => (.receive · · coe) <$> Ref.bitraverse f g c <*> Ref.bitraverse f g r
    | .skip => pure .skip
    | .print e => .print <$> g e
    | .assert e => .assert <$> g e
    | .send c e => (.send · ·) <$> Ref.bitraverse f g c <*> g e
    | .multicast c filter => .multicast c <$> bitraverse f g filter
    | .assign r e => (.assign · ·) <$> Ref.bitraverse f g r <*> g e
    | .goto label => pure (.goto label)

structure AtomicBranch (Typ Expr : Type) : Type where
  precondition : Option (Block (Statement Typ Expr true) false)
  action : Block (Statement Typ Expr false) true
  deriving Repr

instance : Bifunctor AtomicBranch where
  bimap f g branch := {
    precondition := Block.map (λ ⦃_⦄ ↦ instBifunctorStatement.bimap f g) <$> branch.precondition
    action := Block.map (λ ⦃_⦄ ↦ instBifunctorStatement.bimap f g) branch.action
  }

instance : Bitraversable AtomicBranch where
  bitraverse f g branch :=
    AtomicBranch.mk
      <$> traverse (Block.traverse (λ ⦃_⦄ ↦ instBitraversableStatement.bitraverse f g)) branch.precondition
      <*> Block.traverse (λ ⦃_⦄ ↦ instBitraversableStatement.bitraverse f g) branch.action

structure AtomicBlock (Typ Expr : Type) : Type where
  label : String
  branches : List (AtomicBranch Typ Expr)
  deriving Repr

instance : Bifunctor AtomicBlock where
  bimap f g B := { B with branches := bimap f g <$> B.branches }

instance : Bitraversable AtomicBlock where
  bitraverse f g B := AtomicBlock.mk B.label <$> traverse (bitraverse f g) B.branches

/-- One parallel `{...}` thread — a sequence of labelled atomic blocks, in program order.
`AtomicBlock` already carries a `label`, unlike `ElaboratedPlusCal.Process.threads`'s
`List (String × Block τ ε true)` pairing, so no separate label pairing is needed here. -/
abbrev Thread (Typ Expr : Type) : Type := List (AtomicBlock Typ Expr)

/-- A fresh copy of `ElaboratedPlusCal.Declarations`'s shape. -/
structure Declarations (Typ Expr : Type) : Type where
  «variables» : List (String × Typ × Bool × Option (Bool × Expr))
  channels : List (String × Typ × List Expr)
  fifos : List (String × Typ × List Expr)
  deriving Repr

instance : Bifunctor Declarations where
  bimap f g decls := {
    «variables» := decls.variables.map λ (x, ann, isParam, e) ↦ (x, f ann, isParam, Bifunctor.snd g <$> e)
    channels := decls.channels.map λ (x, ann, es) ↦ (x, f ann, g <$> es)
    fifos := decls.fifos.map λ (x, ann, es) ↦ (x, f ann, g <$> es)
  }

instance : Bitraversable Declarations where
  bitraverse f g decls :=
    ({«variables» := ·, channels := ·, fifos := ·})
      <$> traverse (λ (x, ann, isParam, e) ↦ (x, ·, isParam, ·) <$> f ann <*> traverse (bitraverse pure g) e) decls.variables
      <*> traverse (λ (x, ann, es) ↦ (x, ·, ·) <$> f ann <*> traverse g es) decls.channels
      <*> traverse (λ (x, ann, es) ↦ (x, ·, ·) <$> f ann <*> traverse g es) decls.fifos

/-- A fresh copy of `ElaboratedPlusCal.Process`'s shape, `threads` reshaped to `List (Thread Typ
Expr)` per the module doc above. -/
structure Process (Typ Expr : Type) : Type where
  mailbox : Option (String × List Expr)
  isFair : Bool
  name : String
  «=|∈» : Bool
  id : Expr
  localState : Declarations Typ Expr
  threads : List (Thread Typ Expr)
  deriving Repr

instance : Bifunctor Process where
  bimap f g p := { p with
    mailbox := Bifunctor.snd (g <$> ·) <$> p.mailbox
    id := g p.id
    localState := bimap f g p.localState
    threads := ((bimap f g <$> ·) <$> ·) p.threads
  }

instance : Bitraversable Process where
  bitraverse f g p :=
    (Process.mk · p.isFair p.name p.«=|∈» · · ·)
      <$> traverse (λ (n, es) ↦ (n, ·) <$> traverse g es) p.mailbox
      <*> g p.id
      <*> bitraverse f g p.localState
      <*> p.threads.traverse (List.traverse (bitraverse f g))

structure Algorithm (Typ Expr : Type) : Type where
  isFair : Bool
  name : String
  globalState : Declarations Typ Expr
  processes : List (Process Typ Expr)
  deriving Repr

instance : Bifunctor Algorithm where
  bimap f g a := { a with
    globalState := bimap f g a.globalState
    processes := bimap f g <$> a.processes
  }

instance : Bitraversable Algorithm where
  bitraverse f g a :=
    (Algorithm.mk a.isFair a.name · ·)
      <$> bitraverse f g a.globalState
      <*> traverse (bitraverse f g) a.processes

end GuardedPlusCal

-- Pinned for `Computable2Guarded`'s actual use, mirroring `Core/ComputablePlusCal/Syntax.lean`.
namespace ComputableGuardedPlusCal

abbrev Ref := GuardedPlusCal.Ref ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev Multicast := GuardedPlusCal.Multicast ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev Statement := GuardedPlusCal.Statement ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev AtomicBranch := GuardedPlusCal.AtomicBranch ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev AtomicBlock := GuardedPlusCal.AtomicBlock ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev Thread := GuardedPlusCal.Thread ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev Declarations := GuardedPlusCal.Declarations ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev Process := GuardedPlusCal.Process ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev Algorithm := GuardedPlusCal.Algorithm ComputableTLAPlus.Typ ComputablePlusCal.Expression

end ComputableGuardedPlusCal

end
