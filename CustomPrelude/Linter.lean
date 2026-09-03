module

public meta import CustomPrelude.Linter.Basic
public meta import CustomPrelude.Linter.Syntax
public meta import CustomPrelude.Linter.Semantic
public meta import CustomPrelude.Linter.Text
public meta import CustomPrelude.Linter.External

/-!
# Fugue style linters

Re-export of the `linter.fugue.*` family. `CustomPrelude` pulls this in with `public meta import`,
so every downstream module elaborates with the linters registered.
-/
