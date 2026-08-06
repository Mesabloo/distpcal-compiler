module

public import VerifiedCompiler.Trace
public import VerifiedCompiler.Relation
public import VerifiedCompiler.Denotational.Notations
public import VerifiedCompiler.Denotational.StrongRefinement

public section

/-!
  The `VerifiedCompiler` library's root module: the trace algebra, the relation combinators built
  on it, and the refinement framework the passes' correctness proofs are stated in. Nothing imports
  this file — each pass imports the individual pieces it needs. It exists so that the
  `lean_lib VerifiedCompiler` target (`lakefile.lean`) resolves, which makes `lake build
  VerifiedCompiler` a usable check that the whole framework compiles, and gives `doc-gen4` a single
  entry point covering it.

  Without it the library claims no modules, so `lake build VerifiedCompiler` fails with "some
  modules have bad imports" and the only way to check this tier was to name every module by hand.
  Worth having precisely because the default target (`lean_exe fugue`) does not reach any of these
  files: the CLI imports no proofs, so a plain `lake build` stays green no matter what happens
  here.
-/

end
