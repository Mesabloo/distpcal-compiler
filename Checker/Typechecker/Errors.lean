import PlusCalCompiler.Position
import PlusCalCompiler.CoreTLAPlus.Syntax
import PlusCalCompiler.Passes.SourceCodeToSurface.Annotations

inductive TCWarning.{u} : Type u

inductive TCError.{u} : Type u
  | unboundVariable (x : String) (pos : SourceSpan)
  | typeInferenceFailure (e : CoreTLAPlus.Expression CoreTLAPlus.Typ) (pos : SourceSpan)
  | recordHasNoField (y : String) (fields : List String) (pos : SourceSpan)
  | expectedRecordType (pos : SourceSpan) (τ : CoreTLAPlus.Typ)
  /-- Expression was infered to have type `τ'` but was expected to have type `τ` which is incompatible. -/
  | failedToConvertTypes (τ τ' : CoreTLAPlus.Typ) (pos : SourceSpan)

  | metavarCycle (m : Nat)

  | expectedTypeAnnotation (pos : SourceSpan)
  | tooManyTypeAnnotations (pos : SourceSpan)
  | unexpectedNonTypeAnnotations (pos : SourceSpan) (anns : List Annotation)
