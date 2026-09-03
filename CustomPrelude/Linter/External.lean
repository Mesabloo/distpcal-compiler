module

public meta import Mathlib.Tactic.Linter.FlexibleLinter
public meta import Mathlib.Tactic.Linter.Style
public meta import Mathlib.Tactic.Linter.Whitespace
public meta import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter
public meta import Mathlib.Tactic.Linter.EmptyLine
public meta import Mathlib.Tactic.Linter.DocString
public meta import Mathlib.Tactic.Linter.OldObtain
public meta import Mathlib.Tactic.Linter.GlobalAttributeIn
public meta import Mathlib.Tactic.Linter.AuxLemma
public meta import Mathlib.Tactic.Linter.OverlappingInstances
public meta import Mathlib.Tactic.Linter.UnusedInstancesInType

/-!
# External linters this project opts into

Importing these modules registers their `@[linter]`s and their `register_option`s; the *values*
are set in `lakefile.lean`'s `linterOptions` block, which is where the deliberate on/off choice
for each lives. This module only makes the linters reachable in the CLI's build closure.

Linters that are text-script (`linter.trailingWhitespace`, `linter.style.longLine`) rather than
`@[linter]`, and the `tacticAnalysis.*` family (a `simp`/`grind`/`aesop` run at every proof
step), are deliberately not here — the Stop hook is a `lake build`, not a script runner.
-/
