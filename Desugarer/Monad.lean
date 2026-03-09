import Desugarer.Errors
import Core.CoreTLAPlus.Syntax

class abbrev MonadDesugarerExpr (α : outParam Type) (m : Type → Type) :=
  MonadReader (Option (CoreTLAPlus.Expression α)) m,
  MonadWithReader (Option (CoreTLAPlus.Expression α)) m,
  MonadExcept DesugarError m
