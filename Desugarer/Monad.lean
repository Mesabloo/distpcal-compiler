import Desugarer.Errors
import Core.CoreTLAPlus.Syntax
import Common.Fresh

/-- The effects expression desugaring needs: a `Reader` of "what `@` currently refers to" (`none`
outside any `EXCEPT` update), error reporting, and fresh-name generation (for the tuple-pattern
and multi-binder-collapse transformations, `Desugarer/TLAPlus.lean`). -/
class abbrev MonadDesugarerExpr (α : outParam Type) (m : Type → Type) :=
  MonadReaderOf (Option (CoreTLAPlus.Expression α)) m,
  MonadWithReaderOf (Option (CoreTLAPlus.Expression α)) m,
  MonadDiagnostic DesugarWarning DesugarError m,
  MonadFresh m
