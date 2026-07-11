import Common.Errors
import Core.TypedTLAPlus.Syntax

/-! The type checker's diagnostics: one named error/warning variant per violation. -/

/-- The type checker's errors. `todo` is a placeholder, to be replaced by named variants as
checking rules are implemented. -/
inductive TCError : Type
  /-- Escape hatch: an arbitrary message at a position, standing in for a real named variant. -/
  | todo (pos : SourceSpan) (msg : String)
  /-- A `Γ`-lookup miss. -/
  | unboundVariable (pos : SourceSpan) (name : String)
  /-- No coercion exists from the synthesized type to the expected one. -/
  | failedToConvertTypes (pos : SourceSpan) (expected got : TypedTLAPlus.Typ)
  /-- A construct that can only synthesize when annotated was used with no annotation present. -/
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
  /-- A tuple access/update's index wasn't a literal natural number in range. -/
  | invalidTupleIndex (pos : SourceSpan) (index : String) (arity : Nat)
  /-- An operator call's callee didn't synthesize an operator type at all. -/
  | notAnOperatorType (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- An operator call's argument count didn't match its type's parameter count. -/
  | arityMismatch (pos : SourceSpan) (expected got : Nat)
  /-- A `lub`-based synthesis rule found no common type across its branches/elements. -/
  | ambiguousType (pos : SourceSpan)
  /-- A function type (`τ -> τ'`) was expected here, but something else was found. -/
  | notAFunctionType (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- A tuple type was expected here, but something else was found. -/
  | notATupleType (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- A higher-order operator-definition parameter's declared arity (from `F(_,...,_)`'s `_`
  count) didn't match its annotated type's own operator-arity. -/
  | paramArityMismatch (pos : SourceSpan) (param : String) (declared inferred : Nat)
  /-- A `receive`/`send`/`multicast` statement's channel reference didn't synthesize a
  `Channel(τ)`-shaped type. -/
  | notAChannelType (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- A `print` statement's argument didn't synthesize a `showable` type. -/
  | notShowable (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- A channel's declared element type isn't `sendable` — `Operator`/`Channel`/`Const`/rigid
  type variables, or anything containing one, can't be sent over a channel. -/
  | notSendable (pos : SourceSpan) (got : TypedTLAPlus.Typ)
  /-- A metavariable left over at the end of a declaration's checking had no pending upper bound
  recorded on it at all — it was never actually constrained by anything during checking. -/
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
    | .notSendable pos _ => pos
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
    | .notSendable _ got => s!"`{got}` is not a sendable type — it cannot be a channel's element type."
    | .unconstrainedMetavariable _ =>
      "A metavariable was left unconstrained at the end of checking — an explicit type annotation is needed here."

/-- The type checker's non-fatal diagnostics, collected out-of-band. `todo` is a placeholder. -/
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
