import CustomPrelude
import Extra.Array
import Mathlib.Control.Bifunctor
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Traversable.Instances
import Mathlib.Control.Bitraversable.Basic
import Mathlib.Control.Bitraversable.Instances
import Common.Position
import Core.SurfaceTLAPlus.Syntax
import Core.SurfacePlusCal.Syntax

/-!
  `SurfacePlusCal`, but with every `goto` explicit and at the end of a block (§5.2) — the output
  of statement desugaring (`Desugarer/PlusCal.lean`).

  Ported from prior art's `Core/CorePlusCal/Syntax.lean` — its `Statement`/`Block`/`Branches`
  triple, indexed by a `Bool` tracking whether a statement/block is "terminal" (ends in `goto`)
  at the *type* level, is a genuinely good design worth carrying forward verbatim (`CLAUDE.md`,
  `PLAN.md` §2): "every block ends in exactly one terminal statement" becomes a structural
  invariant instead of a side condition to maintain by hand.

  **One fix relative to prior art, confirmed necessary by the thesis's own account of Network
  PlusCal** ("Each thread of the process is a list of labelled atomic blocks", thesis §8.3):
  prior art's `Process.threads : List (Block α β true)` has no way to attach a *label* to each
  block at all, even though every block needs one (it's the target `goto` statements name). Fixed
  here by pairing each block with its label: `threads : List (List (String × Block α β true))` —
  the outer list is `SurfacePlusCal`'s parallel `{...} {...}` threads, the inner list is the
  sequence of labelled atomic blocks *within* one thread.

  **`Process`/`Declarations`/`Algorithm` share the very same `α`/`β` that `Statement`/`Block`/
  `Branches`/`MulticastFilter` do — not a separate type-of-types parameter, and not `Option`-
  wrapped in `Declarations`' own fields.** `α` denotes "the declared-type annotation at
  whatever stage of checking it currently is" everywhere it appears: `List Annotation` fresh
  out of statement desugaring, `Option SurfaceTLAPlus.Typ` after the uniform, still-independent
  `stripEmbeddedTypeAnnotations` pass (`Desugarer/PlusCal.lean`) — which, because `Declarations`
  shares this one `α` rather than a second, independently-evolving parameter, strips
  `Declarations`' `variables`/`channels`/`fifos` entries for free, via the exact same
  `Bitraversable` walk that already covers `MulticastFilter`'s per-bind annotations and a
  `with`-bound variable's own annotation — no special-casing needed. Content that genuinely
  *can't* be expressed via this shared `α` — `@mailbox`'s channel name/index expressions,
  `@parameter`'s presence-as-a-`Bool` — is instead extracted early, as its own concrete field
  (`Process.mailbox`, `Declarations.variables`' `isParameter`), by bespoke validation fused
  directly into statement desugaring (`Process.desugar`/`Declarations.desugarCheck`, per the
  project owner, rather than keeping a second "raw, still-generic" `CorePlusCal`-shaped type
  around purely to bridge the gap between structural desugaring and this bespoke validation) —
  there is exactly one `CorePlusCal.Algorithm` shape throughout. Keeping everything else on one
  shared `α` (rather than splitting it out) is what lets `Process`/`Algorithm` stay ordinary,
  unambiguous two-parameter `Bifunctor`/`Bitraversable` instances.
-/
namespace CorePlusCal
  open SurfacePlusCal (MulticastFilter)

  /-- `SurfacePlusCal.Ref`, but each bracket group's own index is unary — `x[e₁, …, eₙ]` (`n >
  1`) desugars to `x[<<e₁, …, eₙ>>]`, exactly `CoreTLAPlus.Expression.fnCall`/`.except`'s own
  rule (`Desugarer/TLAPlus.lean`'s `wrapIndices`), for the same reason: every downstream
  consumer should be able to rely on "one index expression per bracket group" directly, not
  re-derive it from a list. `x[e₁][e₂]` (two separate bracket groups) is unaffected either way
  — `args`' *outer* list (one entry per bracket group) doesn't change shape, only each group's
  own inner list collapses. -/
  structure Ref (β : Type) : Type where
    name : String
    args : List β
    deriving Repr

  instance : Functor Ref where
    map f r := { r with args := f <$> r.args }

  instance : Traversable Ref where
    traverse f r := (λ args ↦ { r with args }) <$> traverse f r.args

  mutual
    inductive Statement (α β : Type) : Bool → Type
      | goto (label : String) : Statement α β true
      | skip : Statement α β false
      | print (e : β) : Statement α β false
      | assign (_ : List (Ref β × β)) : Statement α β false
      | «if» {b} (cond : β) (B₁ B₂ : Block α β b) : Statement α β b
      | await (e : β) : Statement α β false
      /-- Binds exactly one variable — unlike `SurfacePlusCal.Statement.with`'s `vars : List
      (…)`, a genuine comma list at the surface syntax level (`with (x = 3, y ∈ S) {…}`),
      statement desugaring (`Desugarer/PlusCal.lean`) always flattens a multi-binder `with`
      into a nested chain of single-binder ones (`with (x = 3) { with (y ∈ S) {…} }`) — a
      structural invariant enforced here at the type level, per this project's convention of
      preferring that over a runtime check or a comment asserting it holds. -/
      | «with» (var : String) (ann : α) («=|∈» : Bool) (val : β) (B : Block α β false) : Statement α β false
      | assert (e : β) : Statement α β false
      | either {b} (branches : Branches α β b) : Statement α β b
      /-- `while`'s own body may be either terminal or not: non-terminal in the common case
      (looping is implicit — one atomic step per full loop, however many iterations), but
      terminal when statement desugaring (`Desugarer/PlusCal.lean`) has extracted a labelled
      step out of the loop body, in which case the body ends in an explicit `goto` back to
      whatever label re-enters the loop's own condition check. The `while` statement *itself*
      stays non-terminal either way — falling out of the loop always continues normally to
      whatever follows it in its own enclosing block. -/
      | «while» {b} (cond : β) (B : Block α β b) : Statement α β false
      | receive (c : Ref β) (r : Ref β) : Statement α β false
      | send (c : Ref β) (e : β) : Statement α β false
      | multicast (c : String) (filter : MulticastFilter α β) : Statement α β false
      deriving Repr

    /-- A block is a (possibly empty) sequence of non-terminal statements followed by a
    potentially-terminal one. -/
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
      | .with x ann eq e B, pos => .with x (f ann) eq (g e) (Block.bimap f g B) @@ pos
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
      | .with x ann eq e B, pos =>
        (.with x · eq · · @@ pos) <$> f ann <*> g e <*> Block.bitraverse f g B
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

  /-- The declarations at the top of an `algorithm` or `process` block — the annotation-carrying
  counterpart is `SurfacePlusCal.Declarations`. Shares the *same* `α` as `Statement`/`Block`/
  `Branches`/`MulticastFilter` (not a separate type-of-types parameter, and not `Option`-wrapped
  in its own fields, matching how `MulticastFilter`'s/`with`'s own binder-annotation slots are
  bare `α`, since `α` already denotes "the declared-type annotation" at whatever stage of
  checking it's currently at — `List Annotation` fresh out of statement desugaring, `Option
  SurfaceTLAPlus.Typ` after `stripEmbeddedTypeAnnotations`, `Desugarer/PlusCal.lean`). Keeping
  one shared `α` (rather than a second, independently-evolving parameter) is what lets
  `Process`/`Algorithm` stay ordinary two-parameter `Bifunctor`/`Bitraversable` instances, with
  no currying/instance-resolution ambiguity. -/
  structure Declarations (α β : Type) : Type where
    /-- `(name, declared-type annotation, isParameter — from `@parameter`, only ever `true` on
    a `∈`-initialized entry — initializer)`; the initializer's own `Bool` is `true` for `=`,
    `false` for `∈`, matching `SurfacePlusCal.Declarations`. `isParameter` is a genuinely
    separate field, not folded into `α`, since it's populated by bespoke validation
    (`Declarations.desugarCheck`, `Desugarer/PlusCal.lean`) rather than the uniform
    `@type`-only rule `α` itself follows. -/
    «variables» : List (String × α × Bool × Option (Bool × β))
    channels : List (String × α × List β)
    fifos : List (String × α × List β)
    deriving Repr, Inhabited

  def Declarations.bimap {α β γ δ} (f : α → β) (g : γ → δ) (decls : Declarations α γ) : Declarations β δ := {
    «variables» := decls.variables.map λ (x, ann, isParam, e) ↦ (x, f ann, isParam, Bifunctor.snd g <$> e)
    channels := decls.channels.map λ (x, ann, es) ↦ (x, f ann, g <$> es)
    fifos := decls.fifos.map λ (x, ann, es) ↦ (x, f ann, g <$> es)
  }

  nonrec def Declarations.bitraverse {F : Type → Type} [Applicative F] {α β γ δ} (f : α → F β) (g : γ → F δ)
      (decls : Declarations α γ) : F (Declarations β δ) :=
    ({«variables» := ·, channels := ·, fifos := ·})
      <$> traverse (λ (x, ann, isParam, e) ↦ (x, ·, isParam, ·) <$> f ann <*> traverse (bitraverse pure g) e) decls.variables
      <*> traverse (λ (x, ann, es) ↦ (x, ·, ·) <$> f ann <*> traverse g es) decls.channels
      <*> traverse (λ (x, ann, es) ↦ (x, ·, ·) <$> f ann <*> traverse g es) decls.fifos

  instance : Bifunctor Declarations where
    bimap := Declarations.bimap

  instance : Bitraversable Declarations where
    bitraverse := Declarations.bitraverse

  structure Process (α β : Type) : Type where
    /-- `(channel name, filter/index args)`, from at most one `@mailbox` annotation
    (`Desugarer/PlusCal.lean`); `none` if the process has no mailbox. Always concrete, unlike
    every other annotation-carrying slot here — a mailbox's content (a channel name plus index
    expressions) isn't expressible as "the same `α` as everywhere else", so it's extracted
    early (`extractMailbox`) rather than participating in the generic `α` machinery at all. -/
    mailbox : Option (String × List β)
    isFair : Bool
    name : String
    /-- `true` for `=`, `false` for `∈`. -/
    «=|∈» : Bool
    id : β
    localState : Declarations α β
    /-- One entry per parallel `{...}` thread; each thread is its own sequence of labelled
    atomic blocks (§8.3's "list of labelled atomic blocks"), in program order. -/
    threads : List (List (String × Block α β true))
    deriving Repr, Inhabited

  instance : Bifunctor Process where
    bimap f g p := { p with
      mailbox := Bifunctor.snd (g <$> ·) <$> p.mailbox
      id := g p.id
      localState := bimap f g p.localState
      threads := ((Bifunctor.snd (Block.bimap f g) <$> ·) <$> ·) p.threads
    } @@ posOf p

  instance : Bitraversable Process where
    bitraverse f g p :=
      (Process.mk · p.isFair p.name p.«=|∈» · · · @@ posOf p)
        <$> traverse (λ (n, es) ↦ (n, ·) <$> traverse g es) p.mailbox
        <*> g p.id
        <*> bitraverse f g p.localState
        <*> traverse (traverse (bitraverse pure (Block.bitraverse f g))) p.threads

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
