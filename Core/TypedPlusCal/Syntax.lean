module

public import Core.TypedTLAPlus.Coercion
public import Core.CorePlusCal.Syntax

@[expose] public section


/-!
  The output of PlusCal statement checking. `ElaboratedPlusCal.Statement`/`Block`/`Branches`/
  `Declarations`/`Process`/`Algorithm` mirror `CorePlusCal`'s shape node-for-node, but parameterized
  over `(τ ε : Type)` rather than `CorePlusCal`'s `(α β : Type)`: `Ref` carries an extra resolved
  `type : τ`, and `Statement.receive` an extra `coe : TypedTLAPlus.Coercion`, so a later pass
  (`WellFormedness/Restrictions.lean` check 1) can tell whether a bare `Ref` position (`assign`'s
  LHS, `receive`'s destination) is Channel-shaped without `Γ`, which is gone by then. `Coercion`
  isn't a third parameter — its shape is TLA⁺-expression-specific regardless of instantiation.

  `TypedPlusCal` pins this layer at `τ := TypedTLAPlus.Typ`, `ε := TypedTLAPlus.Expression
  TypedTLAPlus.Typ`. `Core/ComputablePlusCal/Syntax.lean` pins the same layer at
  `ComputableTLAPlus`'s types, reusing these definitions rather than re-copying them: neither
  `Ref.type` nor `receive`'s `Coercion` field change shape across the two, so no second
  monomorphic copy is needed. `MulticastFilter` is reused generically from `SurfacePlusCal` (its
  target is a bare `String`, not a `Ref`, so no type to carry either way).
-/

-- The shared generic layer both `TypedPlusCal` and `ComputablePlusCal` pin — see the module doc
-- above for why this doesn't need a monomorphic copy per stage.
namespace ElaboratedPlusCal

/-- Carries its own resolved `baseType` (unlike `CorePlusCal.Ref`). `args` follows
`CorePlusCal.Ref`'s shape: one entry per path segment, `.inl` for a `.field` segment, `.inr` for a
(unary) bracket-index segment.

`baseType` is the *base variable*'s type (`name`'s `Γ`-lookup result), before any `.args` segment
is applied — kept this way rather than the result type because the result type is always cheap to
recompute from `baseType` (`Ref.stepType`/`.resultType` below), but recovering `baseType` from the
result type isn't possible in general (a record access or tuple projection isn't invertible). -/
structure Ref (τ ε : Type) : Type where
  name : String
  args : List (String ⊕ ε)
  baseType : τ
  deriving Repr

/-- `SurfacePlusCal.MulticastFilter`, reused generically. -/
abbrev MulticastFilter (τ ε : Type) := SurfacePlusCal.MulticastFilter τ ε

mutual
  /-- A fresh copy of `CorePlusCal.Statement`'s shape, not an `abbrev` over it: parameterized over
  `(τ ε : Type)` instead of `(α β : Type)`, since `receive` needs an extra field
  `CorePlusCal.Statement.receive` has no room for. -/
  inductive Statement (τ ε : Type) : Bool → Type
    | goto (label : String) : Statement τ ε true
    | skip : Statement τ ε false
    | print (e : ε) : Statement τ ε false
    | assign (_ : List (Ref τ ε × ε)) : Statement τ ε false
    | «if» {b} (cond : ε) (B₁ B₂ : Block τ ε b) : Statement τ ε b
    | await (e : ε) : Statement τ ε false
    | «with» (var : String) (ann : τ) («=|∈» : Bool) (val : ε) (B : Block τ ε false) :
        Statement τ ε false
    | assert (e : ε) : Statement τ ε false
    | either {b} (branches : Branches τ ε b) : Statement τ ε b
    | «while» {b} (cond : ε) (B : Block τ ε b) : Statement τ ε false
    /-- Differs from `CorePlusCal.Statement.receive` by `coe`: the checked element→reference-type
    upcast for the value read off the channel at runtime. -/
    | receive (c r : Ref τ ε) (coe : TypedTLAPlus.Coercion) : Statement τ ε false
    | send (c : Ref τ ε) (e : ε) : Statement τ ε false
    | multicast (c : String) (filter : MulticastFilter τ ε) : Statement τ ε false
    deriving Repr

  /-- A fresh copy of `CorePlusCal.Block`'s shape. -/
  inductive Block (τ ε : Type) : Bool → Type where
    | mk {b} (begin : List (Statement τ ε false)) («end» : Statement τ ε b) : Block τ ε b
    deriving Repr

  /-- A fresh copy of `CorePlusCal.Branches`'s shape. -/
  inductive Branches (τ ε : Type) : Bool → Type where
    | either {b} : Block τ ε b → Branches τ ε b
    | or {b} : Block τ ε b → Branches τ ε b → Branches τ ε b
    deriving Repr
end

protected abbrev Block.begin {τ ε b} : Block τ ε b → List (Statement τ ε false)
  | ⟨begin, _⟩ => begin

protected abbrev Block.end {τ ε b} : Block τ ε b → Statement τ ε b
  | ⟨_, «end»⟩ => «end»

/-- Runs `act` over every non-terminal statement in `B` (`B.begin`, in order), then its terminal
one (`B.end`). Shared shape for `WellFormedness`'s per-check walkers
(`Restrictions.checkRestrictions`, `WellScoped.checkWellScoped`, `Labelling.checkGotoTargets`),
each supplying its own `act`. -/
def Block.forStatements {τ ε b} {m : Type → Type} [Monad m]
    (act : ∀ {b'}, Statement τ ε b' → m Unit) (B : Block τ ε b) : m Unit := do
  B.begin.forM act
  act B.end

/-- `Block.forStatements`, distributed over `either`/`or` branches. -/
def Branches.forStatements {τ ε b} {m : Type → Type} [Monad m]
    (act : ∀ {b'}, Statement τ ε b' → m Unit) : Branches τ ε b → m Unit
  | .either B => Block.forStatements act B
  | .or B rest => do
    Block.forStatements act B
    Branches.forStatements act rest

instance {τ ε b} : Inhabited (Statement τ ε b) where
  default := match b with
    | true => .goto default
    | false => .skip

instance {τ ε b} : Inhabited (Block τ ε b) where
  default := .mk default default

instance {τ ε b} : Inhabited (Branches τ ε b) where
  default := .either default

/-- A fresh copy of `CorePlusCal.Declarations`'s shape. -/
structure Declarations (τ ε : Type) : Type where
  «variables» : List (String × τ × Bool × Option (Bool × ε))
  channels : List (String × τ × List ε)
  fifos : List (String × τ × List ε)
  deriving Repr, Inhabited

/-- A fresh copy of `CorePlusCal.Process`'s shape. -/
structure Process (τ ε : Type) : Type where
  mailbox : Option (String × List ε)
  isFair : Bool
  name : String
  «=|∈» : Bool
  id : ε
  localState : Declarations τ ε
  threads : List (List (String × Block τ ε true))
  deriving Repr, Inhabited

/-- A fresh copy of `CorePlusCal.Algorithm`'s shape. -/
structure Algorithm (τ ε : Type) : Type where
  isFair : Bool
  name : String
  globalState : Declarations τ ε
  processes : List (Process τ ε)
  deriving Repr, Inhabited

end ElaboratedPlusCal

-- `ElaboratedPlusCal` pinned at the type checker's own output — see the module doc above.
namespace TypedPlusCal

/-- Checked PlusCal expressions — always `TypedTLAPlus.Expression` at the checker's own `Typ`. -/
abbrev Expression := TypedTLAPlus.Expression TypedTLAPlus.Typ

abbrev Ref := ElaboratedPlusCal.Ref TypedTLAPlus.Typ Expression
abbrev MulticastFilter := ElaboratedPlusCal.MulticastFilter TypedTLAPlus.Typ Expression
abbrev Statement := ElaboratedPlusCal.Statement TypedTLAPlus.Typ Expression
abbrev Block := ElaboratedPlusCal.Block TypedTLAPlus.Typ Expression
abbrev Branches := ElaboratedPlusCal.Branches TypedTLAPlus.Typ Expression
abbrev Declarations := ElaboratedPlusCal.Declarations TypedTLAPlus.Typ Expression
abbrev Process := ElaboratedPlusCal.Process TypedTLAPlus.Typ Expression
abbrev Algorithm := ElaboratedPlusCal.Algorithm TypedTLAPlus.Typ Expression

/-- The type after one `Ref` path segment, given the type before it. A pure structural pattern
match — every segment is already elaborated, so this replays the same step-rule
`Elaborator/Expressions.lean`'s `stepInto`/`indexInto` use at check time, without re-checking.
Total: the fallback (`τ` unchanged) only triggers on a `Ref` no well-typed input can produce. -/
def Ref.stepType (τ : TypedTLAPlus.Typ) : String ⊕ Expression → TypedTLAPlus.Typ
  | .inl field => match τ with
    | .record fs => (fs.lookup field).getD τ
    | _ => τ
  | .inr idx => match τ with
    | .function _ rng => rng
    | .seq elem => elem
    | .tuple τs => match idx with
      | .nat n => (n.toNat?.bind (τs[· - 1]?)).getD τ
      | _ => τ
    | _ => τ

/-- A `Ref`'s final/result type — what `assign r e`/`receive c r` check `e`'s type against —
recomputed from `baseType` by walking `args` left to right via `stepType`. -/
def Ref.resultType (r : Ref) : TypedTLAPlus.Typ := r.args.foldl Ref.stepType r.baseType

end TypedPlusCal

end
