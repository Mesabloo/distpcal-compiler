module

public import VerifiedCompiler.Trace
public import VerifiedCompiler.ClosedForm
public import VerifiedCompiler.Relation
public import VerifiedCompiler.Denotational.Notations
public import VerifiedCompiler.Denotational.Tactics
public import VerifiedCompiler.Denotational.StrongRefinement
public import VerifiedCompiler.Denotational.Correctness

public section

/-!
  The `VerifiedCompiler` library's root module: the trace algebra, the relation combinators built
  on it, and the refinement framework the passes' correctness proofs are stated in. Nothing imports
  this file — each pass imports the individual pieces it needs. It exists so that the
  `lean_lib VerifiedCompiler` target (`lakefile.lean`) resolves, which makes `lake build
  VerifiedCompiler` a usable check that the whole framework compiles, and gives `doc-gen4` a single
  entry point covering it.

  It is what makes this tier checkable at all: the default target (`lean_exe fugue`) reaches none
  of these files, since the CLI imports no proofs, so a plain `lake build` stays green no matter
  what happens here.
-/

end
