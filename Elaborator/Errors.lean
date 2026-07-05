import Common.Errors

/-!
  `TCError`/`TCWarning` — the type checker's diagnostics (§5.3), following `Desugarer/
  Errors.lean`'s exact convention: one named variant per violation, not a generic catch-all.

  **Deliberately incomplete for now.** The real vocabulary (`unboundVariable`,
  `failedToConvertTypes`, `expectedTypeAnnotation`, `duplicateTypeAnnotation`, …) only makes
  sense to name once the corresponding checking rule actually exists — until then both types
  carry a single `todo` variant, an escape hatch that wraps an arbitrary message, so pass code
  under active development can report *something* without the whole vocabulary existing up
  front. Every real rule added to `Elaborator/Expressions.lean`/`Declarations.lean`/`.../
  PlusCal.lean` should retire part of `todo`'s call sites in favour of a properly named variant
  here, not grow around it.
-/

/-- The type checker's errors (§5.3). See the module doc — `todo` is a placeholder, to be
replaced by named variants as checking rules are implemented. -/
inductive TCError : Type
  /-- Escape hatch: an arbitrary message at a position, standing in for a real named variant. -/
  | todo (pos : SourceSpan) (msg : String)
  deriving Repr, Inhabited, BEq

instance : CompilerDiagnostic TCError String where
  isError := true
  posOf | .todo pos _ => pos
  msgOf | .todo _ msg => msg

/-- The type checker's non-fatal diagnostics (§5.3) — collected out-of-band, matching
`Desugarer/Errors.lean`'s `DesugarWarning`. See the module doc — `todo` is a placeholder. -/
inductive TCWarning : Type
  /-- Escape hatch: an arbitrary message at a position, standing in for a real named variant. -/
  | todo (pos : SourceSpan) (msg : String)
  deriving Repr, Inhabited, BEq

/-- The `-W<name>`/`-Wno-<name>` name a given warning is filtered under. -/
def TCWarning.name : TCWarning → String
  | .todo .. => "todo"

instance : CompilerDiagnostic TCWarning String where
  isError := false
  posOf | .todo pos _ => pos
  msgOf | .todo _ msg => msg
