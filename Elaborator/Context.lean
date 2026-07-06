import Elaborator.Monad

open TypedTLAPlus (Typ)

variable {m : Type → Type} [Monad m] [MonadElaborator m]

/-- Extend `Γ` with one more binding for the scope of `act` — always monomorphic (`isScheme :=
false`, the `Binding` default): every caller of `extend`/`extendAll` is introducing a binder, not
a top-level declaration. -/
def extend {α} (x : String) (τ : Typ) (act : m α) : m α :=
  withTheReader Context (·.insert x { type := τ }) act

/-- Extend `Γ` with every binding in `bindings` for the scope of `act`, later entries shadowing
earlier ones on conflict. -/
def extendAll {α} (bindings : List (String × Typ)) (act : m α) : m α :=
  withTheReader Context (λ ctx ↦ bindings.foldl (init := ctx) λ ctx' (x, τ) ↦ ctx'.insert x { type := τ }) act

/-- Extend `Γ` with a list of already-tagged `Binding`s (each carrying its own `isScheme`) for
the scope of `act` — used where the caller has just checked a whole top-level declaration list
(`Elaborator/Declarations.lean`'s `checkDeclarations`, `Elaborator/Elaborator.lean`'s
`Module.check`) and must extend `Γ` with its `operator`/`function` bindings as schemes, unlike
`extendAll` above, which always inserts monomorphically. -/
def extendAllBindings {α} (bindings : List (String × Binding)) (act : m α) : m α :=
  withTheReader Context (λ ctx ↦ bindings.foldl (init := ctx) λ ctx' (x, b) ↦ ctx'.insert x b) act

/-- Requires that an annotation be present, erroring at `pos` with `what` otherwise. -/
def requireAnnotation (pos : SourceSpan) (what : String) : Option Typ → m Typ
  | some τ => return τ
  | none => throw (.expectedTypeAnnotation pos what)
