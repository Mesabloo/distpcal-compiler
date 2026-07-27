module

public import Core.TypedPlusCal.Syntax
public import Core.ComputableTLAPlus.Syntax

public section


/-!
  `ElaboratedPlusCal` pinned at `Typed2Computable`'s output rather than the type checker's — the
  same `Statement`/`Block`/`Branches`/`Ref`/`Declarations`/`Process`/`Algorithm` layer
  `TypedPlusCal` pins, but at `ComputableTLAPlus`'s types. See `Core/TypedPlusCal/Syntax.lean`'s
  module doc for why this pass needs no separate monomorphic copy.
-/

namespace ComputablePlusCal

/-- Computable PlusCal expressions — always `ComputableTLAPlus.Expression` at
`ComputableTLAPlus.Typ`. -/
abbrev Expression := ComputableTLAPlus.Expression ComputableTLAPlus.Typ

abbrev Ref := ElaboratedPlusCal.Ref ComputableTLAPlus.Typ Expression
abbrev Multicast := ElaboratedPlusCal.Multicast ComputableTLAPlus.Typ Expression
abbrev Statement := ElaboratedPlusCal.Statement ComputableTLAPlus.Typ Expression
abbrev Block := ElaboratedPlusCal.Block ComputableTLAPlus.Typ Expression
abbrev Branches := ElaboratedPlusCal.Branches ComputableTLAPlus.Typ Expression
abbrev Declarations := ElaboratedPlusCal.Declarations ComputableTLAPlus.Typ Expression
abbrev Process := ElaboratedPlusCal.Process ComputableTLAPlus.Typ Expression
abbrev Algorithm := ElaboratedPlusCal.Algorithm ComputableTLAPlus.Typ Expression

/-- `TypedPlusCal.Ref.stepType`'s counterpart at this pin's types; see that def and
`ElaboratedPlusCal.Ref.baseType` (same file) for why this is cheap and necessary. -/
def Ref.stepType (τ : ComputableTLAPlus.Typ) : String ⊕ Expression → ComputableTLAPlus.Typ
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

/-- The type a `Ref`'s bracket-index expression must have at one particular `.inr` step, given
the type *before* that step (unlike `stepType`, which gives the type *after*). Used by
`Computable2Guarded/Par.lean`'s `parRef` to annotate hoisted index-temp `with`-bindings. -/
def Ref.indexType : ComputableTLAPlus.Typ → ComputableTLAPlus.Typ
  | .function dom _ => dom
  | .seq _ => .int
  | .tuple _ => .int
  | τ => τ

/-- `TypedPlusCal.Ref.resultType`'s own counterpart at this pin's types. -/
def Ref.resultType (r : Ref) : ComputableTLAPlus.Typ := r.args.foldl Ref.stepType r.baseType

end ComputablePlusCal

end
