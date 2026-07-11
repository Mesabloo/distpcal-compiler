import Core.TypedTLAPlus.Coercion
import Core.CorePlusCal.Syntax

/-!
  The output of PlusCal statement checking — a fresh, monomorphic AST mirroring
  `CorePlusCal.Statement`/`Block`/`Branches`/`Declarations`/`Process`/`Algorithm`, with every
  embedded expression checked (`CoreTLAPlus.Expression` → `TypedTLAPlus.Expression`) and every
  type parameter pinned at `Typ`/`Expression Typ`.

  `Statement.receive` and `Ref` both differ in shape from their `CorePlusCal` counterparts:
  `Statement.receive` carries an extra `Coercion` field for the channel-element-vs-reference-type
  upcast, and `Ref` carries its own resolved `type` (`inferRef`'s `Γ`-lookup result,
  `Elaborator/PlusCal.lean`) rather than being reused generically — needed so a later pass
  (`WellFormedness/Restrictions.lean`'s check 1) can tell whether a bare Ref position (`assign`'s
  LHS, `receive`'s destination) is itself Channel-shaped without needing `Γ`, which is gone by
  then. Every other constructor is a plain transcription at `α := Typ`, `β := Expression Typ`.
  `MulticastFilter` is reused generically from `SurfacePlusCal` (its target is a bare `String`,
  not a `Ref`, so it has no type to carry either way).
-/

namespace TypedPlusCal

/-- Checked PlusCal expressions — always `TypedTLAPlus.Expression` at the checker's own `Typ`. -/
abbrev Expression := TypedTLAPlus.Expression TypedTLAPlus.Typ

/-- A checked `Ref` — unlike `CorePlusCal.Ref`, carries its own resolved `type` (see the module
doc above). -/
structure Ref : Type where
  name : String
  args : List Expression
  type : TypedTLAPlus.Typ
  deriving Repr

/-- `SurfacePlusCal.MulticastFilter`, checked — reused generically. -/
abbrev MulticastFilter := SurfacePlusCal.MulticastFilter TypedTLAPlus.Typ Expression

mutual
  /-- Checked PlusCal statements — a fresh copy of `CorePlusCal.Statement`, not an `abbrev`. -/
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
    /-- Differs from `CorePlusCal.Statement.receive`: `coe` is the checked-element-vs-reference-
    type upcast for the value this `receive` will read off the channel at runtime. -/
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

/-- Checked declarations (`variables`/`channels`/`fifos`) — a fresh copy of
`CorePlusCal.Declarations` at `α := Typ`, `β := Expression`. -/
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

/-- A checked algorithm — a fresh copy of `CorePlusCal.Algorithm`. -/
structure Algorithm : Type where
  isFair : Bool
  name : String
  globalState : Declarations
  processes : List Process
  deriving Repr, Inhabited

end TypedPlusCal
