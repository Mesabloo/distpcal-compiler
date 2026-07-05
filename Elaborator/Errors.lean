import Common.Errors
import Core.TypedTLAPlus.Syntax

/-!
  `TCError`/`TCWarning` — the type checker's diagnostics (§5.3), following `Desugarer/
  Errors.lean`'s exact convention: one named variant per violation, not a generic catch-all.

  `todo` remains as an escape hatch for whatever hasn't gotten a named variant yet (currently:
  everything `Elaborator/Declarations.lean`/`PlusCal.lean` will need, §5.3 tasks 7/9, not yet
  written) — but `Elaborator/Expressions.lean`'s own violations (bidirectional expression
  checking, Figs. 3.1.1–3.1.6) are named here for real, retiring `todo`'s call sites for that
  file's scope per this module's own original plan.
-/

/-- The type checker's errors (§5.3). See the module doc — `todo` is a placeholder, to be
replaced by named variants as checking rules are implemented. -/
inductive TCError : Type
  /-- Escape hatch: an arbitrary message at a position, standing in for a real named variant. -/
  | todo (pos : SourceSpan) (msg : String)
  /-- A `Γ`-lookup miss (thesis Fig. 3.1.1's `VAR`). -/
  | unboundVariable (pos : SourceSpan) (name : String)
  /-- The `[Subtype]` fallback (thesis Fig. 3.1.7) found no coercion from the synthesized type
  to the expected one. -/
  | failedToConvertTypes (pos : SourceSpan) (expected got : TypedTLAPlus.Typ)
  /-- A construct that can only synthesize when annotated (unbounded `\A`/`\E`/temporal
  quantification, thesis Fig. 3.1.5/3.1.6) was used with no annotation present. -/
  | expectedTypeAnnotation (pos : SourceSpan) (what : String)
  /-- A checking-only construct (empty set, unbounded `CHOOSE`) was hit in a position that
  needs a synthesized type. -/
  | cannotInferType (pos : SourceSpan) (reason : String)
  /-- A `Set(τ)` type was expected here, but something else was found. -/
  | notASetType (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- A record type was expected here, but something else was found. -/
  | notARecordType (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- Indexing (`e[e']`) requires a function, tuple, or sequence type. -/
  | notIndexable (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- A record access/update named a field the record's type doesn't have. -/
  | unknownField (pos : SourceSpan) (field : String) (available : List String)
  /-- A tuple access/update's index wasn't a literal natural number in range (thesis Fig.
  3.1.3's `TUPLE ACCESS`/`TUPLE OVERLOADING` — unlike sequence access, the index is part of the
  judgment itself, so it must be a literal). -/
  | invalidTupleIndex (pos : SourceSpan) (index : String) (arity : Nat)
  /-- An operator call's callee didn't synthesize an operator type at all. -/
  | notAnOperatorType (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- An operator call's argument count didn't match its type's parameter count. -/
  | arityMismatch (pos : SourceSpan) (expected got : Nat)
  /-- A `lub`-based synthesis rule (`ENUMERATION`, `CONDITIONAL`, `CONDITIONAL CHOICE`, thesis
  Fig. 3.1.8's addendum) found no common type across its branches/elements. -/
  | ambiguousType (pos : SourceSpan)
  /-- A function type (`τ -> τ'`) was expected here (a function definition's own annotation,
  `Elaborator/Declarations.lean`'s `FUNCTION DEFINITION` rule), but something else was found. -/
  | notAFunctionType (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- A tuple type was expected here (a multi-argument function definition's domain,
  `Elaborator/Declarations.lean`), but something else was found. -/
  | notATupleType (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- A higher-order operator-definition parameter's declared arity (from `F(_,...,_)`'s `_`
  count) didn't match its annotated type's own operator-arity (`Elaborator/Declarations.lean`'s
  `checkParamArity`). -/
  | paramArityMismatch (pos : SourceSpan) (param : String) (declared inferred : Nat)
  /-- A `receive`/`send`/`multicast` statement's channel reference didn't synthesize a
  `Channel(τ)`-shaped type (thesis Fig. 3.1.13's `[Receive]`/`[Send]`/`[Multicast]`,
  `Elaborator/PlusCal.lean`). -/
  | notAChannelType (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- A `print` statement's argument didn't synthesize a `showable` type (thesis Fig. 3.1.14,
  `Elaborator/PlusCal.lean`'s `[Print]`). -/
  | notShowable (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- A metavariable left over at the end of a declaration's checking (`PLAN.md` §5.3's
  single end-of-check defaulting point, `Elaborator/Expressions.lean`'s `resolveMVars`) had no
  pending upper bound recorded on it at all — it was never actually constrained by anything
  during checking, not a case to silently default away. -/
  | unconstrainedMetavariable (pos : SourceSpan)
  deriving Repr, Inhabited, BEq

instance : CompilerDiagnostic TCError String where
  isError := true
  posOf
    | .todo pos _ => pos
    | .unboundVariable pos _ => pos
    | .failedToConvertTypes pos _ _ => pos
    | .expectedTypeAnnotation pos _ => pos
    | .cannotInferType pos _ => pos
    | .notASetType pos _ => pos
    | .notARecordType pos _ => pos
    | .notIndexable pos _ => pos
    | .unknownField pos _ _ => pos
    | .invalidTupleIndex pos _ _ => pos
    | .notAnOperatorType pos _ => pos
    | .arityMismatch pos _ _ => pos
    | .ambiguousType pos => pos
    | .notAFunctionType pos _ => pos
    | .notATupleType pos _ => pos
    | .paramArityMismatch pos _ _ _ => pos
    | .notAChannelType pos _ => pos
    | .notShowable pos _ => pos
    | .unconstrainedMetavariable pos => pos
  msgOf
    | .todo _ msg => msg
    | .unboundVariable _ name => s!"Unbound variable `{name}`."
    | .failedToConvertTypes _ expected got =>
      s!"Expected type `{expected}`, got `{got}`, and no coercion exists between the two."
    | .expectedTypeAnnotation _ what =>
      s!"`{what}` needs an explicit type annotation here — its type cannot otherwise be inferred."
    | .cannotInferType _ reason => s!"Cannot infer a type here: {reason}."
    | .notASetType _ got => s!"Expected a `Set(_)` type, got `{got}`."
    | .notARecordType _ got => s!"Expected a record type, got `{got}`."
    | .notIndexable _ got => s!"`{got}` is not a function, tuple, or sequence type — it cannot be indexed."
    | .unknownField _ field available =>
      s!"No field `{field}` in this record (available: {String.intercalate ", " available})."
    | .invalidTupleIndex _ index arity =>
      s!"Invalid tuple index `{index}` for a tuple of arity {arity} — tuple access requires a literal index between 1 and {arity}."
    | .notAnOperatorType _ got => s!"Expected an operator type, got `{got}`."
    | .arityMismatch _ expected got => s!"Expected {expected} argument(s), got {got}."
    | .ambiguousType _ => "Ambiguous type: the branches/elements here don't share a common type."
    | .notAFunctionType _ got => s!"Expected a function type (`τ -> τ'`), got `{got}`."
    | .notATupleType _ got => s!"Expected a tuple type, got `{got}`."
    | .paramArityMismatch _ param declared inferred =>
      s!"Parameter `{param}` was declared with arity {declared}, but its annotated type has arity {inferred}."
    | .notAChannelType _ got => s!"Expected a `Channel(_)` type, got `{got}`."
    | .notShowable _ got => s!"`{got}` is not a showable type — it cannot be passed to `print`."
    | .unconstrainedMetavariable _ =>
      "A metavariable was left unconstrained at the end of checking — an explicit type annotation is needed here."

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
