module

public import Tests.Expectation
public import Tests.Check
public import Tests.Report
public import Tests.Main

/-!
  Root of `lean_lib Fugue.Tests` — the regression runner. Re-exports its modules so the library
  target resolves (`lake build Fugue.Tests`) and `doc-gen4` has one entry point for it, matching
  every other library in this package. `Tests/Main.lean` is the executable's root; nothing imports
  this file.
-/
