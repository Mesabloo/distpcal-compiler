import Elaborator.Elaborator
import Parser_.TLAPlus
import Parser_.Annotations
import Desugarer.TLAPlus
import Desugarer.PlusCal

/-!
  `Driver/Modules.lean`'s own errors/warnings — **not** `TCError`/`TCWarning`: nothing here is a
  type-checking-rule violation, it's every way *driving* the pipeline up to and around the checker
  can fail. Wraps each lower-level pass's own error type directly (`lex`/`parse`/`annotation`/
  `desugar`) plus the resolution-specific conditions (`moduleNotFound`/`ambiguousModule`/
  `cyclicExtends`), plus `typeCheck`, wrapping whatever `TCError` the checker itself raises — so
  `Fugue.lean` only ever has to handle one error type across the whole pipeline.
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

/-- A placeholder position for diagnostics with no real one to report (`moduleNotFound`/
`ambiguousModule`/`cyclicExtends`) — line `1`, not `(0, 0)`, since every real position in this
codebase is 1-indexed and line `0` would render a wrong (off-by-one) line number. -/
private def noPos : SourceSpan := ⟨⟨1, 0⟩, ⟨1, 0⟩⟩

instance : CompilerDiagnostic DriverError String where
  isError := true
  posOf
    | .lex _ e => CompilerDiagnostic.posOf e
    | .parse _ e => CompilerDiagnostic.posOf e
    | .annotation _ e => CompilerDiagnostic.posOf e
    | .desugar _ e => CompilerDiagnostic.posOf e
    | .moduleNotFound .. | .ambiguousModule .. | .cyclicExtends .. => noPos
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

/-- `DriverError`'s non-fatal counterpart — carries a warning from any pass (plus its owning
`moduleId`) through `Driver/Modules.lean`'s accumulate-then-flush machinery
(`MonadWarningAccumulator`), uniformly regardless of which pass produced it. -/
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
