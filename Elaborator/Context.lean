module

public import Elaborator.Monad

@[expose] public section


open TypedTLAPlus (Typ Origin)

/-- Resolve `x` against `Γ`: `lexical` first (an expression binder at position `i` → `Origin.bound
i`), then `named` (a `Memory`-keyed name or a declaration, taking its stored `Origin`). Returns the
type, the `Origin` to bake onto the `.var` node, and whether the binding is a scheme. -/
def Context.lookup (ctx : Context) (x : String) : Option (Typ × Origin × Bool) :=
  match ctx.lexical.findIdx? (·.1 == x) with
  | some i => ctx.lexical[i]?.map λ (_, τ) ↦ (τ, .bound i, false)
  | none => ctx.named[x]?.map λ b ↦ (b.type, b.origin, b.isScheme)

/-- Insert one already-tagged `named` binding — used to build the initial `Γ` from a module's
imports (`Driver/Modules.lean`). -/
def Context.insertNamed (ctx : Context) (x : String) (b : Binding) : Context :=
  { ctx with named := ctx.named.insert x b }

variable {m : Type → Type} [Monad m] [MonadElaborator m]

/-- Push one expression-level lexical binder for the scope of `act` — a quantifier, `CHOOSE`,
set-builder, `map'`/`fn`, `EXCEPT` binder, or `multicast` filter recipient. References to `x`
inside `act` elaborate to `Origin.bound 0` at the top of the pushed scope. -/
def extend {α} (x : String) (τ : Typ) (act : m α) : m α :=
  withTheReader Context (λ c ↦ { c with lexical := (x, τ) :: c.lexical }) act

/-- Push several lexical binders at once — operator/function parameters. `bindings` is in
declaration order (`Op(a, b)` ⇒ `[(a, _), (b, _)]`), so the last parameter ends up innermost:
`a` elaborates to `Origin.bound 1`, `b` to `Origin.bound 0`. -/
def extendAll {α} (bindings : List (String × Typ)) (act : m α) : m α :=
  withTheReader Context (λ c ↦ { c with lexical := bindings.reverse ++ c.lexical }) act

/-- Add one `Memory`-keyed name (`Origin.free` — a PlusCal `variable`/`channel`/`fifo`, `self`, or
a statement-level `with`) for the scope of `act`. -/
def extendFree {α} (x : String) (τ : Typ) (act : m α) : m α :=
  withTheReader Context (λ c ↦
    { c with named := c.named.insert x { type := τ, origin := .free x } }) act

/-- `extendFree` over a list — a whole `variables`/`channels`/`fifos` block, or a process's local
state in scope for its threads. -/
def extendAllFree {α} (bindings : List (String × Typ)) (act : m α) : m α :=
  withTheReader Context (λ c ↦
    { c with named := bindings.foldl (init := c.named) λ nm (x, τ) ↦
      nm.insert x { type := τ, origin := .free x } }) act

/-- Extend `Γ` with a list of already-tagged `named` `Binding`s (each carrying its own
`isScheme`/`origin`) for the scope of `act` — a checked declaration list's `operator`/`function`
schemes and `CONSTANT`/`VARIABLE` bindings. -/
def extendAllBindings {α} (bindings : List (String × Binding)) (act : m α) : m α :=
  withTheReader Context (λ c ↦
    { c with named := bindings.foldl (init := c.named) λ nm (x, b) ↦ nm.insert x b }) act

/-- Requires that an annotation be present, erroring at `pos` with `what` otherwise. -/
def requireAnnotation (pos : SourceSpan) (what : String) : Option Typ → m Typ
  | some τ => return τ
  | none => throw (.expectedTypeAnnotation pos what)

end
