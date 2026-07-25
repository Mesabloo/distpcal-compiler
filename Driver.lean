module

public import Driver.Builtins
public import Driver.Errors
public import Driver.Modules
public import Driver.Pipeline

/-!
  `lean_lib Fugue.Driver`'s root: driver-level orchestration around the passes — the builtin
  module table, the errors every stage up to type checking reports through, recursive `EXTENDS`
  resolution, and the whole compile as one function.
-/
