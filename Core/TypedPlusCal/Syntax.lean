import Core.TypedTLAPlus.Coercion
import Core.CorePlusCal.Syntax

/-!
  The output of PlusCal statement checking (§5.3, thesis §3.1.5) — a *fresh* AST, deliberately not
  reusing `CorePlusCal.Statement`/`Block`/`Branches`/`Declarations`/`Process`/`Algorithm` via
  `abbrev` the way an earlier draft of this file did (the "DONE" entry this replaces, `.claude/
  tasklist.md`'s task 2).

  **Why the reversal, given `PLAN.md` §5.3 itself says statement checking "produces no type
  information" of its own.** That claim is what justified the abbrev in the first place — the
  statement *shape* never changes, only its embedded expressions do (`CoreTLAPlus.Expression` →
  checked `TypedTLAPlus.Expression`), so reusing `CorePlusCal`'s shape wholesale, just
  re-instantiated at `α := Typ`/`β := Expr`, seemed to cost nothing. `[Receive]`'s channel/
  reference coercion (`PLAN.md` §5.3/§9.15) is a genuine counterexample: checking a `receive`
  statement really does produce one new piece of information no `CoreTLAPlus`-expression-level
  change can carry (there is no sub-expression to attach it to — the received value doesn't exist
  as a term until runtime), which has to live on the `receive` node itself. An abbrev can't express
  "this one node gets an extra field once checked" without either (a) making that field's type a
  function of the shared, still-generic `β` (impossible — `Coercion` is fixed at the checker's own
  concrete output type, not a function of whatever `β` a given instantiation happens to use), or
  (b) polluting the *pre-check* `CorePlusCal.Statement.receive` with a field that's meaningless
  (always `none`) until checking happens. Both were tried and rejected in this session before
  landing here — a real, dedicated `TypedPlusCal.Statement` is the only shape where `receive`'s
  `coe` field can be mandatory and *always mean something*, exactly mirroring
  `Core/TypedTLAPlus/Syntax.lean`'s own relationship to `Core/CoreTLAPlus/Syntax.lean` (a genuine
  second copy, not an abbrev, even though most constructors line up 1:1 with an extra `Typ` field
  bolted on here and there).

  **Monomorphic, unlike `CorePlusCal`'s own `Statement α β`.** `CorePlusCal`'s two type parameters
  track "whatever stage of checking `α`/`β` currently are" across statement desugaring →
  `stripEmbeddedTypeAnnotations` → this checker. Once checking is done, both are pinned forever
  at `Typ`/`Expression Typ` — nothing downstream ever re-instantiates a `TypedPlusCal.Statement`
  at some other `α`/`β`, so keeping the parameters (the way `TypedTLAPlus.Expression` keeps its
  own single `α`, purely for `Bifunctor`/`Bitraversable`-convention uniformity) would buy nothing
  here: no call site needs `TypedPlusCal.Statement` to *be* a `Bifunctor`, only `Elaborator/
  PlusCal.lean` ever constructs one (by checking), and `Driver/Modules.lean`'s only use of it
  (`TypedTLAPlus.Module TypedPlusCal.Algorithm TypedTLAPlus.Typ`) needs it to be an ordinary
  concrete type, not a two-parameter family. `terminal : Bool`, `CorePlusCal`'s own genuinely
  reused structural-invariant trick, stays exactly as it was.

  Only `Statement.receive` differs in shape from its `CorePlusCal` counterpart (module doc above);
  every other constructor is a plain transcription at `α := Typ`, `β := Expression Typ`.
  `Ref`/`MulticastFilter` are still reused generically (`CorePlusCal.Ref`/`SurfacePlusCal.
  MulticastFilter` instantiated at this file's own `Expression`) — neither has any per-stage
  asymmetry the way `receive` does, so there's nothing a fresh copy of either would buy.
-/

namespace TypedPlusCal

/-- Checked PlusCal expressions — always `TypedTLAPlus.Expression` at the checker's own `Typ`. -/
abbrev Expression := TypedTLAPlus.Expression TypedTLAPlus.Typ

/-- `CorePlusCal.Ref`, checked — reused generically (module doc: no per-stage asymmetry to a
`Ref` the way `receive` has). -/
abbrev Ref := CorePlusCal.Ref Expression

/-- `SurfacePlusCal.MulticastFilter`, checked — reused generically, same reasoning as `Ref`. -/
abbrev MulticastFilter := SurfacePlusCal.MulticastFilter TypedTLAPlus.Typ Expression

mutual
  /-- Checked PlusCal statements — a fresh copy of `CorePlusCal.Statement` (module doc), not an
  `abbrev`. -/
  inductive Statement : Bool → Type
    | goto (label : String) : Statement true
    | skip : Statement false
    | print (e : Expression) : Statement false
    | assign (_ : List (Ref × Expression)) : Statement false
    | «if» {b} (cond : Expression) (B₁ B₂ : Block b) : Statement b
    | await (e : Expression) : Statement false
    | «with» (var : String) (ann : TypedTLAPlus.Typ) («=|∈» : Bool) (val : Expression) (B : Block false) :
        Statement false
    | assert (e : Expression) : Statement false
    | either {b} (branches : Branches b) : Statement b
    | «while» {b} (cond : Expression) (B : Block b) : Statement false
    /-- The one constructor that genuinely differs from `CorePlusCal.Statement.receive`: `coe`
    is the checked-element-vs-reference-type upcast for the value this `receive` will read off
    the channel at runtime (`PLAN.md` §5.3/§9.15's `[Receive]` note) — always a real, already-
    computed `Coercion` here (unlike a hypothetical pre-check placeholder), since every
    `TypedPlusCal.Statement.receive` that exists came from `Elaborator/PlusCal.lean` actually
    checking one. `Typed2Guarded`'s four subpasses carry it through unapplied (none of them
    touch `receive`'s own shape); only `Guarded2Network` actually splices it into the generated
    buffered read. -/
    | receive (c r : Ref) (coe : TypedTLAPlus.Coercion) : Statement false
    | send (c : Ref) (e : Expression) : Statement false
    | multicast (c : String) (filter : MulticastFilter) : Statement false
    deriving Repr

  /-- Checked PlusCal atomic blocks — a fresh copy of `CorePlusCal.Block`. -/
  inductive Block : Bool → Type where
    | mk {b} (begin : List (Statement false)) («end» : Statement b) : Block b
    deriving Repr

  /-- Checked PlusCal `either`/`or` branches — a fresh copy of `CorePlusCal.Branches`. -/
  inductive Branches : Bool → Type where
    | either {b} : Block b → Branches b
    | or {b} : Block b → Branches b → Branches b
    deriving Repr
end

protected abbrev Block.begin {b} : Block b → List (Statement false)
  | ⟨begin, _⟩ => begin

protected abbrev Block.end {b} : Block b → Statement b
  | ⟨_, «end»⟩ => «end»

instance {b} : Inhabited (Statement b) where
  default := match b with
    | true => .goto default
    | false => .skip

instance {b} : Inhabited (Block b) where
  default := .mk default default

instance {b} : Inhabited (Branches b) where
  default := .either default

/-- Checked declarations (`variables`/`channels`/`fifos`) — a fresh copy of `CorePlusCal.
Declarations` at `α := Typ`, `β := Expression`, per this file's own module doc. Field-for-field
identical to `CorePlusCal.Declarations`'s own shape (no `receive`-style asymmetry here). -/
structure Declarations : Type where
  «variables» : List (String × TypedTLAPlus.Typ × Bool × Option (Bool × Expression))
  channels : List (String × TypedTLAPlus.Typ × List Expression)
  fifos : List (String × TypedTLAPlus.Typ × List Expression)
  deriving Repr, Inhabited

/-- A checked process — a fresh copy of `CorePlusCal.Process`. -/
structure Process : Type where
  mailbox : Option (String × List Expression)
  isFair : Bool
  name : String
  «=|∈» : Bool
  id : Expression
  localState : Declarations
  threads : List (List (String × Block true))
  deriving Repr, Inhabited

/-- A checked algorithm — a fresh copy of `CorePlusCal.Algorithm`, the type finally handed to
`Typed2Guarded`. -/
structure Algorithm : Type where
  isFair : Bool
  name : String
  globalState : Declarations
  processes : List Process
  deriving Repr, Inhabited

end TypedPlusCal
