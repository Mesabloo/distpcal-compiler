import PlusCalCompiler.Passes.Typechecker.Expressions
import PlusCalCompiler.GuardedPlusCal.Syntax

section
  open GuardedPlusCal CoreTLAPlus

  variable {m} [MonadTC m] [Monad m]

  def checkAlgorithm (a : Algorithm Typ (Expression Typ)) : m (Algorithm Typ (TypedTLAPlus.Expression Typ)) := do

    sorry
end
