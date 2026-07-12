module

public import Elaborator
public import Parser_
public import Desugarer

public section

/-!
  `Driver/Modules.lean`'s own errors/warnings — every way driving the pipeline up to and
  including the checker can fail. Wraps each lower-level pass's own error type (`lex`/`parse`/
  `annotation`/`desugar`/`typeCheck`) plus the resolution-specific conditions (`moduleNotFound`/
  `ambiguousModule`/`cyclicExtends`), so `Fugue.lean` only has to handle one error type for the
  driver's own portion of the pipeline. Passes past the checker (`WellFormedness`,
  `Typed2Computable`, everything after) run outside the driver, on its returned `TypedModule`, and
  report through their own error types directly — not wrapped here.
-/

/-- `moduleId` is the *offending module's own* key into the source registry
(`Driver/Modules.lean`'s `MonadSourceRegistry`) — not necessarily the main module's: an error
inside an `EXTENDS`-ed dependency must render against that dependency's own lines, not whichever
module `Fugue.lean` originally started with. -/
inductive DriverError : Type
  /-- A lexing failure. -/
  | lex (moduleId : String) (e : Unexpected Char)
  /-- A parsing failure. -/
  | parse (moduleId : String) (e : Unexpected (SurfaceTLAPlus.Token (Located' SurfacePlusCal.Token)))
  /-- A `@type`/`@mailbox`/`@parameter` annotation-resolution failure. -/
  | annotation (moduleId : String) (e : ResolverError)
  /-- A Surface→Core desugaring failure (TLA⁺ expressions or the embedded PlusCal algorithm). -/
  | desugar (moduleId : String) (e : DesugarError)
  /-- `EXTENDS name` didn't resolve to any file (searched: the extending module's own directory,
  `-I`'s search path, and the builtin table). -/
  | moduleNotFound (name : String)
  /-- `EXTENDS name` resolved to more than one candidate — no silent shadowing. -/
  | ambiguousModule (name : String) (foundAt : List String)
  /-- `EXTENDS` forms a cycle; `chain` is the resolution stack at the point the cycle was found,
  outermost first, with the repeated name appended at the end for a readable `A -> B -> A`. -/
  | cyclicExtends (chain : List String)
  /-- A real type-checking failure. -/
  | typeCheck (moduleId : String) (e : TCError)

-- Needed for `DriverError.lex`'s wrapped `Unexpected Char` — no global `ToString Char` exists on
-- purpose (`Fugue.lean` needs the identical local instance for the same reason).
private instance : ToString Char := ⟨λ c ↦ s!"'{c}'"⟩

-- Needed for `DriverError.parse`'s wrapped `Unexpected (Token (Located' SurfacePlusCal.Token))`.
private instance {α} [ToString α] : ToString (Located' α) := ⟨λ x ↦ toString x.data⟩

@[no_expose]
instance : CompilerDiagnostic DriverError String where
  isError := true
  posOf
    | .lex _ e => CompilerDiagnostic.posOf e
    | .parse _ e => CompilerDiagnostic.posOf e
    | .annotation _ e => CompilerDiagnostic.posOf e
    | .desugar _ e => CompilerDiagnostic.posOf e
    | .moduleNotFound .. | .ambiguousModule .. | .cyclicExtends .. => SourceSpan.placeholder
    | .typeCheck _ e => CompilerDiagnostic.posOf e
  msgOf
    | .lex _ e => CompilerDiagnostic.msgOf e
    | .parse _ e => CompilerDiagnostic.msgOf e
    | .annotation _ e => CompilerDiagnostic.msgOf e
    | .desugar _ e => CompilerDiagnostic.msgOf e
    | .moduleNotFound name => s!"Could not find module '{name}'."
    | .ambiguousModule name foundAt =>
      s!"Module '{name}' is ambiguous: found at {String.intercalate ", " foundAt}."
    | .cyclicExtends chain => s!"Cyclic EXTENDS: {String.intercalate " -> " chain}."
    | .typeCheck _ e => CompilerDiagnostic.msgOf e

/-- `DriverError`'s non-fatal counterpart — carries a warning from any pass, plus its owning
`moduleId`, through `Driver/Modules.lean`'s accumulate-then-flush machinery. -/
inductive DriverWarning : Type
  | parser (moduleId : String) (w : ParserWarning)
  | desugar (moduleId : String) (w : DesugarWarning)
  | typeCheck (moduleId : String) (w : TCWarning)

/-- The `-W<name>`/`-Wno-<name>` name a given warning is filtered under — forwards to whichever
wrapped warning's own `.name`. -/
def DriverWarning.name : DriverWarning → String
  | .parser _ w => ParserWarning.name w
  | .desugar _ w => DesugarWarning.name w
  | .typeCheck _ w => TCWarning.name w

/-- The `moduleId` a given warning is tagged with — every variant carries one, unlike
`DriverError` (whose `moduleNotFound`/`ambiguousModule`/`cyclicExtends` carry none). -/
def DriverWarning.moduleId : DriverWarning → String
  | .parser moduleId _ | .desugar moduleId _ | .typeCheck moduleId _ => moduleId

instance : CompilerDiagnostic DriverWarning String where
  isError := false
  posOf
    | .parser _ w => CompilerDiagnostic.posOf w
    | .desugar _ w => CompilerDiagnostic.posOf w
    | .typeCheck _ w => CompilerDiagnostic.posOf w
  msgOf
    | .parser _ w => CompilerDiagnostic.msgOf w
    | .desugar _ w => CompilerDiagnostic.msgOf w
    | .typeCheck _ w => CompilerDiagnostic.msgOf w

end
