module

public import Core.Declaration
public import Core.SurfaceTLAPlus.Syntax
public import Core.SurfaceTLAPlus.Pretty
public import Core.SurfacePlusCal.Syntax
public import Core.SurfacePlusCal.Pretty
public import Core.CoreTLAPlus.Syntax
public import Core.CorePlusCal.Syntax
public import Core.TypedTLAPlus.Syntax
public import Core.TypedTLAPlus.Coercion
public import Core.TypedTLAPlus.Builtins
public import Core.TypedPlusCal.Syntax
public import Core.ComputableTLAPlus.Syntax
public import Core.ComputableTLAPlus.Coercion
public import Core.ComputableTLAPlus.Subst
public import Core.ComputableTLAPlus.Semantics.Interface
public import Core.ComputablePlusCal.Syntax
public import Core.GuardedPlusCal.Syntax
public import Core.GuardedPlusCal.Syntax.Lemmas
public import Core.GuardedPlusCal.Semantics.Denotational
public import Core.GuardedPlusCal.Semantics.Lemmas
public import Core.GuardedPlusCal.Semantics.Process
public import Core.NetworkPlusCal.Syntax
public import Core.NetworkPlusCal.Semantics.Denotational
public import Core.NetworkPlusCal.Semantics.Lemmas
public import Core.NetworkPlusCal.Semantics.Process
public import Core.Go.Syntax
public import Core.Go.Pretty

public section

/-!
  The `Fugue.Core` library's root module: every AST layer, in pipeline order, plus the semantics
  modules that hang off them. Nothing imports this file — each pass imports the individual layers it
  needs. It exists so that the `lean_lib Fugue.Core` target (`roots := #[`Core]`) resolves, which
  makes `lake build Fugue.Core` a usable check that the whole AST tier compiles, and gives
  `doc-gen4` a single entry point covering it.
-/

end
