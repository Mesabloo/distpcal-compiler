module

public import Core.GuardedPlusCal.Syntax
public import Mathlib.Control.Bifunctor
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Control.Bitraversable.Basic
public import Mathlib.Control.Bitraversable.Instances

public section


/-!
  The output of `Guarded2Network`: a `receive` is no longer an abstract guard statement — it's
  compiled into a genuine second kind of thread, `Thread.rx`, that loops reading a process-local
  `inbox` sequence variable, and every later `await`/`with` guard that referenced the received
  value now reads that `inbox` instead. Reuses `GuardedPlusCal.Block`/`Ref`/`MulticastFilter`/
  `Declarations` unchanged — none of those shapes are affected by this pass, only `Statement`
  (drops `receive`) and `Thread` (gains a second, non-`code` constructor) are.

  - No separate `ChanRef` type: `GuardedPlusCal.Statement` already reuses one uniform `Ref` for
    both a channel argument and an ordinary reference (`Core/GuardedPlusCal/Syntax.lean`'s
    `send`/`assign`), so `NetworkPlusCal.Statement` carries that same uniformity forward.
  - Real `Bifunctor`/`Bitraversable` instances throughout, matching
    `Core/GuardedPlusCal/Syntax.lean`'s instances (`Ref.bimap`/`Ref.bitraverse` reused directly,
    since `Ref` itself has no generic instance).
  - `Thread` is a genuine sum (`.code (blocks : List AtomicBlock)` | `.rx (chan : Ref Typ Expr)
    (var : String) (τ : Typ) (inbox : String)`) — a receiving thread is a real second kind of
    thread, not folded into `.code`.
  - `deriving Repr` throughout — no `Pretty.lean` needed yet: `-d dump-network` renders via
    `reprStr`, the same way `-d dump-guarded` does today (`Fugue.lean`'s existing debug-dump
    wiring). A real pretty-printer is only worth adding once a backend needs one.
  - Lives under the existing `Fugue.Core` `lean_lib` target (its `roots := #[`Core`]` glob picks
    this file up automatically) — no new `lakefile.lean` target needed, unlike `Fugue.G2N`,
    already declared for the pass itself.
-/

namespace NetworkPlusCal

open GuardedPlusCal (Block Ref Ref.bimap Ref.bitraverse MulticastFilter Declarations)

/-- A statement in the Network PlusCal language — identical to `GuardedPlusCal.Statement` minus
`receive` (compiled away into `Thread.rx` by this pass), including `with`'s `ann : Typ` field
(`GuardedPlusCal.Statement.with`'s doc comment explains why it's kept). The first `Bool`
(`guardClass`) is `true` for a statement allowed in a branch's precondition (`with`/`await`); the
second (`terminal`) is `true` only for `goto`. -/
inductive Statement (Typ Expr : Type) : Bool → Bool → Type
  | «with» (name : String) (ann : Typ) (bound : Bool) (e : Expr) : Statement Typ Expr true false
  | await (e : Expr) : Statement Typ Expr true false
  | skip : Statement Typ Expr false false
  | print (e : Expr) : Statement Typ Expr false false
  | assert (e : Expr) : Statement Typ Expr false false
  | send (c : Ref Typ Expr) (e : Expr) : Statement Typ Expr false false
  | multicast (c : String) (filter : MulticastFilter Typ Expr) : Statement Typ Expr false false
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

/-- One parallel `{...}` thread — either ordinary code (a sequence of labelled atomic blocks, in
program order, same shape as `GuardedPlusCal.Thread`) or a dedicated receiving loop: reads `chan`
into `var : τ` by repeatedly waiting on and draining a process-local `inbox` sequence variable
(named `inbox`, fresh per `Guarded2Network.freshName`). A real second kind of thread, not folded
into `.code`, since its body isn't a `List AtomicBlock` — see the module doc. -/
inductive Thread (Typ Expr : Type) : Type
  | code (blocks : List (AtomicBlock Typ Expr))
  | rx (chan : Ref Typ Expr) (var : String) (τ : Typ) (inbox : String)
  deriving Repr

instance : Bifunctor Thread where
  bimap f g
    | .code blocks => .code (bimap f g <$> blocks)
    | .rx chan var τ inbox => .rx (Ref.bimap f g chan) var (f τ) inbox

instance : Bitraversable Thread where
  bitraverse f g
    | .code blocks => .code <$> traverse (bitraverse f g) blocks
    | .rx chan var τ inbox => (.rx · var · inbox) <$> Ref.bitraverse f g chan <*> f τ

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
    threads := bimap f g <$> p.threads
  }

instance : Bitraversable Process where
  bitraverse f g p :=
    (Process.mk · p.isFair p.name p.«=|∈» · · ·)
      <$> traverse (λ (n, es) ↦ (n, ·) <$> traverse g es) p.mailbox
      <*> g p.id
      <*> bitraverse f g p.localState
      <*> p.threads.traverse (bitraverse f g)

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

end NetworkPlusCal

-- Pinned for `Guarded2Network`'s use, mirroring `Core/GuardedPlusCal/Syntax.lean`'s
-- `ComputableGuardedPlusCal` pinning.
namespace ComputableNetworkPlusCal

abbrev Ref := GuardedPlusCal.Ref ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev MulticastFilter := GuardedPlusCal.MulticastFilter ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev Statement := NetworkPlusCal.Statement ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev AtomicBranch := NetworkPlusCal.AtomicBranch ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev AtomicBlock := NetworkPlusCal.AtomicBlock ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev Thread := NetworkPlusCal.Thread ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev Declarations := GuardedPlusCal.Declarations ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev Process := NetworkPlusCal.Process ComputableTLAPlus.Typ ComputablePlusCal.Expression
abbrev Algorithm := NetworkPlusCal.Algorithm ComputableTLAPlus.Typ ComputablePlusCal.Expression

end ComputableNetworkPlusCal

end
