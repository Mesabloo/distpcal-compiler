module

public import Common.Diagnostics.Code
public import Common.Diagnostics.Stage
public import Common.Diagnostics.Registry
public import Common.Errors
public import Common.Flags
public import Common.Fresh
public import Common.Position
public import Common.Pretty

public section

/-!
  `Fugue.Common`'s root module: the infrastructure every stage shares, none of it specific to a
  language or a pass — source positions, the diagnostic registry and its rendering, CLI flags as a
  reader environment, and hygienic fresh names.

  Nothing in the compiler imports this file. It exists so that `lake build Fugue.Common` resolves
  the target (Lake looks for a module named after each `lean_lib` root) and so `doc-gen4` has one
  entry point per library, same as `Core.lean` and the per-pass roots.
-/

end
