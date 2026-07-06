import Elaborator.Monad

open TypedTLAPlus (Typ)

variable {m : Type → Type} [Monad m] [MonadElaborator m]

/-- Extend `Γ` with one more binding for the scope of `act` — the rightmost/most-recent
`Std.HashMap.insert` wins on lookup, matching `Elaborator/Monad.lean`'s `Context` doc. -/
def extend {α} (x : String) (τ : Typ) (act : m α) : m α :=
  withTheReader Context (·.insert x τ) act

/-- Extend `Γ` with every binding in `bindings` for the scope of `act`, later entries shadowing
earlier ones on conflict — `extend`, just folded over a list (operator and function definitions
bind more than one name at once: the parameters, and — for function definitions only — the
function's own name too). -/
def extendAll {α} (bindings : List (String × Typ)) (act : m α) : m α :=
  withTheReader Context (λ ctx ↦ bindings.foldl (init := ctx) λ ctx' (x, τ) ↦ ctx'.insert x τ) act

/-- A declaration/statement-level annotation is mandatory wherever the thesis's own grammar
extension makes one required (`CONSTANTS`/`VARIABLES`/operator- and function-definitions,
`with`/`variables`/channel declarations) — callers pass a placeholder position for the entries
that have no real expression to report against. -/
def requireAnnotation (pos : SourceSpan) (what : String) : Option Typ → m Typ
  | some τ => return τ
  | none => throw (.expectedTypeAnnotation pos what)
