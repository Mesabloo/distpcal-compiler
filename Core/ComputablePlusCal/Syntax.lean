module

public import Core.TypedPlusCal.Syntax
public import Core.ComputableTLAPlus.Syntax

@[expose] public section


/-!
  `ElaboratedPlusCal` (`Core/TypedPlusCal/Syntax.lean`) pinned at `Typed2Computable`'s own
  output, instead of the type checker's — the same shared `Statement`/`Block`/`Branches`/`Ref`/
  `Declarations`/`Process`/`Algorithm` layer `TypedPlusCal` pins, at `ComputableTLAPlus`'s types
  instead. See `Core/TypedPlusCal/Syntax.lean`'s module doc for why this pass doesn't need its
  own monomorphic copy the way `TypedPlusCal` itself needed one over `CorePlusCal`.
-/

namespace ComputablePlusCal

/-- Computable PlusCal expressions — always `ComputableTLAPlus.Expression` at
`ComputableTLAPlus.Typ`. -/
abbrev Expression := ComputableTLAPlus.Expression ComputableTLAPlus.Typ

abbrev Ref := ElaboratedPlusCal.Ref ComputableTLAPlus.Typ Expression
abbrev MulticastFilter := ElaboratedPlusCal.MulticastFilter ComputableTLAPlus.Typ Expression
abbrev Statement := ElaboratedPlusCal.Statement ComputableTLAPlus.Typ Expression
abbrev Block := ElaboratedPlusCal.Block ComputableTLAPlus.Typ Expression
abbrev Branches := ElaboratedPlusCal.Branches ComputableTLAPlus.Typ Expression
abbrev Declarations := ElaboratedPlusCal.Declarations ComputableTLAPlus.Typ Expression
abbrev Process := ElaboratedPlusCal.Process ComputableTLAPlus.Typ Expression
abbrev Algorithm := ElaboratedPlusCal.Algorithm ComputableTLAPlus.Typ Expression

/-- `TypedPlusCal.Ref.stepType`'s own counterpart at this pin's types — see that def's doc
comment (`Core/TypedPlusCal/Syntax.lean`) and `Ref.baseType`'s (`ElaboratedPlusCal`, same file)
for why this is always cheap and why it's needed at all. -/
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

/-- The type a `Ref`'s own bracket-index expression must have at the point of one particular
`.inr` step, given the type *before* that step (unlike `stepType`, which gives the type *after*
it) — `Computable2Guarded/Par.lean`'s `parRef` is the one consumer, annotating each hoisted
index-temp `with`-binding correctly instead of reusing the referenced `Ref`'s own (unrelated)
result type. -/
def Ref.indexType : ComputableTLAPlus.Typ → ComputableTLAPlus.Typ
  | .function dom _ => dom
  | .seq _ => .int
  | .tuple _ => .int
  | τ => τ

/-- `TypedPlusCal.Ref.resultType`'s own counterpart at this pin's types. -/
def Ref.resultType (r : Ref) : ComputableTLAPlus.Typ := r.args.foldl Ref.stepType r.baseType

end ComputablePlusCal

end
