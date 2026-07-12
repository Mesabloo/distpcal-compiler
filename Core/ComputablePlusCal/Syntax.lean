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

end ComputablePlusCal

end
