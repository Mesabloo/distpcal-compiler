import Elaborator.Monad

open TypedTLAPlus (Typ)

variable {m : Type → Type} [Monad m] [MonadElaborator m]

/-- Extend `Γ` with one more binding for the scope of `act`. -/
def extend {α} (x : String) (τ : Typ) (act : m α) : m α :=
  withTheReader Context (·.insert x τ) act

/-- Extend `Γ` with every binding in `bindings` for the scope of `act`, later entries shadowing
earlier ones on conflict. -/
def extendAll {α} (bindings : List (String × Typ)) (act : m α) : m α :=
  withTheReader Context (λ ctx ↦ bindings.foldl (init := ctx) λ ctx' (x, τ) ↦ ctx'.insert x τ) act

/-- Requires that an annotation be present, erroring at `pos` with `what` otherwise. -/
def requireAnnotation (pos : SourceSpan) (what : String) : Option Typ → m Typ
  | some τ => return τ
  | none => throw (.expectedTypeAnnotation pos what)
