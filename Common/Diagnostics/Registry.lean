module

public import Common.Diagnostics.Code
public import Common.Diagnostics.Stage
public meta import Common.Diagnostics.Code

public section

/-!
  Every diagnostic code the compiler can emit, with the stage that emits it and a one-line
  summary. This is the *only* place a number is bound to a meaning: each `CompilerDiagnostic`
  instance names an entry here (`Diagnostics.unexpectedToken.code`) rather than writing a literal,
  so a code that a diagnostic uses but the registry does not list cannot exist.

  Numbers are allocated sequentially and are **permanent**: never renumbered, never reused. A
  diagnostic that disappears keeps its entry, marked `retired`, so an old build log or an old
  `fugue explain E0042` stays meaningful. Add new diagnostics at the end.

  `fugue explain <code>` prints `docs/diagnostics/<code>.md`; the summary here is what
  `fugue explain --list` shows, and what the regression runner's coverage report labels a code
  with.
-/

namespace Diagnostics

/-- One diagnostic's registry entry. -/
structure Entry : Type where
  /-- Its code. -/
  code : DiagnosticCode
  /-- The stage that emits it. -/
  stage : Stage
  /-- The `-W<name>` this is filtered under. Warnings only; empty for an error, which `-W` never
  suppresses. -/
  warningName : String := ""
  /-- One line, imperative-free: what the diagnostic means, not how to fix it (that is what
  `docs/diagnostics/<code>.md` is for). -/
  summary : String
  deriving Repr, Inhabited

/-- An error code, by number. -/
private def e (n : Fin 10000) : DiagnosticCode := { severity := .error, number := n }

/-- A warning code, by number. -/
private def w (n : Fin 10000) : DiagnosticCode := { severity := .warning, number := n }

/-! ## Lexing -/

/-- `Parser_`'s lexer rejected a character. -/
def unexpectedCharacter : Entry :=
  { code := e 1, stage := .lex, summary := "A character the lexer cannot start any token with." }

/-! ## Parsing -/

/-- `Parser_`'s parser rejected a token. -/
def unexpectedToken : Entry :=
  { code := e 2, stage := .parse, summary := "A token that cannot continue the construct being parsed." }

/-! ## Annotation resolution -/

/-- `@type`/`@mailbox`/`@parameter` given the wrong number of arguments. -/
def annotationArity : Entry :=
  { code := e 3, stage := .annotation, summary := "An annotation was given the wrong number of arguments." }

/-- An annotation's argument is not the kind of thing that annotation takes. -/
def annotationArgumentKind : Entry :=
  { code := e 4, stage := .annotation, summary := "An annotation's argument is not of the kind it expects." }

/-- A `@type` annotation's payload does not parse as a type. -/
def annotationTypeParse : Entry :=
  { code := e 5, stage := .annotation, summary := "The type inside an annotation does not parse." }

/-- An annotation's payload does not parse as an expression. -/
def annotationExpressionParse : Entry :=
  { code := e 6, stage := .annotation, summary := "The expression inside an annotation does not parse." }

/-- `@mailbox` was not given a `var[e₁, …, eₙ]`-shaped expression. -/
def annotationMailboxShape : Entry :=
  { code := e 7, stage := .annotation, summary := "A @mailbox annotation is not of the form 'var[e₁, …, eₙ]'." }

/-! ## Desugaring -/

/-- `@` used outside an `EXCEPT` update. -/
def misplacedAt : Entry :=
  { code := e 8, stage := .desugar, summary := "'@' appears outside the EXCEPT update it would refer to." }

/-- `goto` somewhere other than the end of its statement list. -/
def gotoNotInTailPosition : Entry :=
  { code := e 9, stage := .desugar, summary := "A goto is not the last statement of its list." }

/-- A statement with no label reachable above it. -/
def unlabelledStatement : Entry :=
  { code := e 10, stage := .desugar, summary := "A statement belongs to no labelled atomic block." }

/-- A label inside a `with` body. -/
def nestedLabel : Entry :=
  { code := e 11, stage := .desugar, summary := "A label appears inside a 'with' body, which cannot contain one." }

/-- A `while` inside a `with` body. -/
def whileInWith : Entry :=
  { code := e 12, stage := .desugar, summary := "A 'while' appears inside a 'with' body." }

/-- A `while` not immediately preceded by a label. -/
def whileNotLabelled : Entry :=
  { code := e 13, stage := .desugar, summary := "A 'while' is not immediately preceded by a label." }

/-- An `if`/`either` that needs a label after it and does not have one. -/
def notFollowedByLabel : Entry :=
  { code := e 14, stage := .desugar, summary := "A statement that ends an atomic block is not followed by a label." }

/-- A write to a `with`-bound name. -/
def withBoundVarWritten : Entry :=
  { code := e 15, stage := .desugar, summary := "A 'with'-bound name is assigned to or received into." }

/-- An annotation of the wrong kind for the site it sits at. -/
def wrongAnnotationKind : Entry :=
  { code := e 16, stage := .desugar, summary := "An annotation of a kind this site does not accept." }

/-- The same annotation twice on one site. -/
def duplicateAnnotation : Entry :=
  { code := e 17, stage := .desugar, summary := "The same annotation kind appears twice on one declaration." }

/-- Two assignments to the same variable in one atomic block. -/
def conflictingAssignment : Entry :=
  { code := e 18, stage := .desugar, summary := "A variable is assigned more than once within one atomic block." }

/-- A record field access whose field is not an identifier. -/
def invalidRecordFieldAccess : Entry :=
  { code := e 19, stage := .desugar, summary := "A record field access whose field is not an identifier." }

-- E0020 is unallocated: it was drafted for a fatal repeated `@parameter`, which turned out to be
-- a warning (`W0003`) and nothing else. Left as a gap rather than handed to the next diagnostic —
-- numbers are never reused, including ones that never shipped.

/-! ## `EXTENDS` resolution -/

/-- `EXTENDS` names a module no search path provides. -/
def moduleNotFound : Entry :=
  { code := e 21, stage := .resolve, summary := "An EXTENDS-ed module was not found on any search path." }

/-- `EXTENDS` names a module found in more than one place. -/
def ambiguousModule : Entry :=
  { code := e 22, stage := .resolve, summary := "An EXTENDS-ed module name resolves to more than one candidate." }

/-- `EXTENDS` forms a cycle. -/
def cyclicExtends : Entry :=
  { code := e 23, stage := .resolve, summary := "EXTENDS forms a cycle." }

/-! ## Type checking -/

/-- Placeholder for a checking rule with no named diagnostic yet. -/
def typeCheckTodo : Entry :=
  { code := e 24, stage := .typeCheck, summary := "An unnamed type-checking failure (placeholder)." }

/-- A name with no binding in scope. -/
def unboundVariable : Entry :=
  { code := e 25, stage := .typeCheck, summary := "A name with no binding in scope." }

/-- Two types that do not convert. -/
def typeMismatch : Entry :=
  { code := e 26, stage := .typeCheck, summary := "A value's type is not compatible with the type expected here." }

/-- A type annotation is required and absent. -/
def missingTypeAnnotation : Entry :=
  { code := e 27, stage := .typeCheck, summary := "A type annotation is required at this position." }

/-- A type could not be inferred. -/
def cannotInferType : Entry :=
  { code := e 28, stage := .typeCheck, summary := "No type could be inferred for this expression." }

/-- A set was expected. -/
def notASetType : Entry :=
  { code := e 29, stage := .typeCheck, summary := "A set was expected here." }

/-- A record was expected. -/
def notARecordType : Entry :=
  { code := e 30, stage := .typeCheck, summary := "A record was expected here." }

/-- Indexing into something that cannot be indexed. -/
def notIndexable : Entry :=
  { code := e 31, stage := .typeCheck, summary := "This type cannot be indexed." }

/-- A record field that the record type does not have. -/
def unknownField : Entry :=
  { code := e 32, stage := .typeCheck, summary := "A record field this record type does not have." }

/-- A tuple index outside the tuple's range, or not a literal. -/
def invalidTupleIndex : Entry :=
  { code := e 33, stage := .typeCheck, summary := "A tuple index that is not a literal within the tuple's range." }

/-- An operator was expected. -/
def notAnOperatorType : Entry :=
  { code := e 34, stage := .typeCheck, summary := "An operator was expected here." }

/-- An operator applied to the wrong number of arguments. -/
def arityMismatch : Entry :=
  { code := e 35, stage := .typeCheck, summary := "An operator applied to the wrong number of arguments." }

/-- A type that stayed ambiguous. -/
def ambiguousType : Entry :=
  { code := e 36, stage := .typeCheck, summary := "More than one type fits, with nothing to choose between them." }

/-- A function was expected. -/
def notAFunctionType : Entry :=
  { code := e 37, stage := .typeCheck, summary := "A function was expected here." }

/-- A tuple was expected. -/
def notATupleType : Entry :=
  { code := e 38, stage := .typeCheck, summary := "A tuple was expected here." }

/-- A higher-order parameter used at an arity its declared type does not have. -/
def paramArityMismatch : Entry :=
  { code := e 39, stage := .typeCheck, summary := "A higher-order parameter used at an arity its type does not allow." }

/-- A channel was expected. -/
def notAChannelType : Entry :=
  { code := e 40, stage := .typeCheck, summary := "A channel was expected here." }

/-- `print` given something with no printable form. -/
def notShowable : Entry :=
  { code := e 41, stage := .typeCheck, summary := "This type has no printable form." }

/-- A value that cannot be sent over a channel. -/
def notSendable : Entry :=
  { code := e 42, stage := .typeCheck, summary := "This type cannot be sent over a channel." }

/-- A metavariable left unconstrained at the end of checking. -/
def unconstrainedMetavariable : Entry :=
  { code := e 43, stage := .typeCheck, summary := "A type was left undetermined at the end of checking." }

/-! ## Well-formedness -/

/-- A `goto` to a label no process defines. -/
def unknownLabel : Entry :=
  { code := e 44, stage := .wellFormedness, summary := "A goto targets a label that is never defined." }

/-- `Done` redefined as an ordinary label. -/
def redefinedDone : Entry :=
  { code := e 45, stage := .wellFormedness, summary := "The reserved label 'Done' is redefined." }

/-- Two declarations of one name in one scope. -/
def duplicateName : Entry :=
  { code := e 46, stage := .wellFormedness, summary := "A name is declared twice in the same scope." }

/-- An inner declaration shadowing an outer one. -/
def shadowedName : Entry :=
  { code := e 47, stage := .wellFormedness, summary := "A declaration shadows an outer one of the same name." }

/-- A channel value inside an ordinary expression. -/
def channelInExpression : Entry :=
  { code := e 48, stage := .wellFormedness, summary := "A channel appears where an ordinary value is expected." }

/-- A `variables` entry with a channel type. -/
def channelTypedVariable : Entry :=
  { code := e 49, stage := .wellFormedness, summary := "A 'variables' entry has a channel type." }

/-- A process declaring its own `channels`/`fifos`. -/
def nonEmptyLocalChannels : Entry :=
  { code := e 50, stage := .wellFormedness, summary := "A process declares process-local channels." }

/-- An algorithm-level PlusCal `variables` block. -/
def globalPlusCalVariable : Entry :=
  { code := e 51, stage := .wellFormedness, summary := "An algorithm-level 'variables' block: no shared memory." }

/-- A reference to a module-level TLA⁺ `VARIABLE`. -/
def globalTLAPlusVariable : Entry :=
  { code := e 52, stage := .wellFormedness, summary := "A reference to a module-level VARIABLE: no shared memory." }

/-- A temporal or action operator reachable from a statement. -/
def bareTemporalOrAction : Entry :=
  { code := e 53, stage := .wellFormedness, summary := "A temporal or action operator is reachable from a statement." }

/-- An unbounded quantifier where a finite one is required. -/
def unboundedQuantifier : Entry :=
  { code := e 54, stage := .wellFormedness, summary := "An unbounded quantifier, which has no finite runtime meaning." }

/-! ## `Typed2Computable` -/

/-- A construct with no finite runtime representation. -/
def notComputable : Entry :=
  { code := e 55, stage := .computable, summary := "A construct with no finite runtime representation." }

/-- An invariant `Typed2Computable` relies on did not hold — a compiler bug, not a program error. -/
def computableInternalInvariant : Entry :=
  { code := e 56, stage := .computable, summary := "Internal invariant violated in Typed2Computable (compiler bug)." }

/-! ## `Computable2Guarded` -/

/-- An invariant `Computable2Guarded` relies on did not hold — a compiler bug. -/
def guardedInternalInvariant : Entry :=
  { code := e 57, stage := .guarded, summary := "Internal invariant violated in Computable2Guarded (compiler bug)." }

/-! ## `Guarded2Network` -/

/-- An invariant `Guarded2Network` relies on did not hold — a compiler bug. -/
def networkInternalInvariant : Entry :=
  { code := e 58, stage := .network, summary := "Internal invariant violated in Guarded2Network (compiler bug)." }

/-! ## `Network2Go` -/

/-- An invariant `Network2Go` relies on did not hold — a compiler bug. -/
def goInternalInvariant : Entry :=
  { code := e 60, stage := .go, summary := "Internal invariant violated in Network2Go (compiler bug)." }

/-- A well-typed construct the Go backend has no way to compile. -/
def goUnsupported : Entry :=
  { code := e 61, stage := .go,
    summary := "A construct with no Go counterpart (infinite set, Bags, function equality)." }

/-! ## Module identity -/

/-- A file whose `MODULE` name is not the file's own name. -/
def moduleNameMismatch : Entry :=
  { code := e 59, stage := .parse,
    summary := "A module's declared name does not match the name of the file it is in." }

/-! ## Warnings -/

/-- `fair`/`fair+` parsed and ignored. -/
def fairIgnored : Entry :=
  { code := w 1, stage := .parse, warningName := "fair",
    summary := "'fair'/'fair+' is parsed but never acted on." }

/-- An annotation nothing consumes. -/
def unusedAnnotation : Entry :=
  { code := w 2, stage := .parse, warningName := "unused-annotation",
    summary := "A well-formed annotation sits where nothing reads it." }

/-- `@parameter` repeated harmlessly. -/
def duplicateParameterAnnotation : Entry :=
  { code := w 3, stage := .desugar, warningName := "duplicate-parameter",
    summary := "A repeated @parameter annotation, which is redundant rather than ambiguous." }

/-- Placeholder for an unnamed checker warning. -/
def typeCheckTodoWarning : Entry :=
  { code := w 4, stage := .typeCheck, warningName := "todo",
    summary := "An unnamed type-checking warning (placeholder)." }

/-- A `multicast` filter annotating only some of its components. -/
def partialMulticastAnnotation : Entry :=
  { code := w 5, stage := .desugar, warningName := "partial-multicast-annotation",
    summary := "Only some components of a multicast recipient carry a @type annotation." }

/-- Every registered diagnostic, in code order. `fugue explain --list` prints this; the regression
runner's coverage report walks it to find codes no fixture exercises. -/
def entries : List Entry :=
  [ unexpectedCharacter, unexpectedToken,
    annotationArity, annotationArgumentKind, annotationTypeParse, annotationExpressionParse,
    annotationMailboxShape,
    misplacedAt, gotoNotInTailPosition, unlabelledStatement, nestedLabel, whileInWith,
    whileNotLabelled, notFollowedByLabel, withBoundVarWritten, wrongAnnotationKind,
    duplicateAnnotation, conflictingAssignment, invalidRecordFieldAccess,
    moduleNotFound, ambiguousModule, cyclicExtends,
    typeCheckTodo, unboundVariable, typeMismatch, missingTypeAnnotation, cannotInferType,
    notASetType, notARecordType, notIndexable, unknownField, invalidTupleIndex, notAnOperatorType,
    arityMismatch, ambiguousType, notAFunctionType, notATupleType, paramArityMismatch,
    notAChannelType, notShowable, notSendable, unconstrainedMetavariable,
    unknownLabel, redefinedDone, duplicateName, shadowedName, channelInExpression,
    channelTypedVariable, nonEmptyLocalChannels, globalPlusCalVariable, globalTLAPlusVariable,
    bareTemporalOrAction, unboundedQuantifier,
    notComputable, computableInternalInvariant, guardedInternalInvariant, networkInternalInvariant,
    goInternalInvariant, goUnsupported,
    moduleNameMismatch,
    fairIgnored, unusedAnnotation, duplicateParameterAnnotation, typeCheckTodoWarning,
    partialMulticastAnnotation ]

-- No two entries may share a number: the whole point of a code is that it identifies exactly one
-- diagnostic. Checked here, at build time, rather than trusted.
#guard entries.length == (entries.map (·.code) |>.eraseDups).length

/-- The entry for `code`, if it is registered. -/
def find? (code : DiagnosticCode) : Option Entry := entries.find? (·.code == code)

end Diagnostics

end
