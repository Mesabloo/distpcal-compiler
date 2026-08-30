module

public import Elaborator.Errors
public import Core.TypedTLAPlus.Syntax
public import Common.Fresh

public section


/-! The effects the type checker needs: a local typing context `Γ`, a metavariable context,
error reporting, and fresh-name generation. -/

/-- One `Γ` entry in the `named` half of `Context` (below): a `Memory`-keyed name
(`Origin.free` — PlusCal `variables`/`channels`/`fifos`, `self`) or a top-level declaration
(`Origin.module`/`Origin.intrinsic` — `CONSTANT`/`VARIABLE`/operator/function/builtin). `type` is
the `Γ`-lookup result; `isScheme` marks a declaration whose `Typ.var`s are freshened into fresh
metavariables at every reference (`specializeType`, `Elaborator/Expressions.lean`'s `inferExpr`) —
only `operator`/`function` definitions and `builtinContext` entries; and `origin` is the `Origin`
baked onto every `Expression.var` node that resolves here. Expression-level lexical binders
(`\A`/`\E`/`CHOOSE`/set-builders/`map'`/`fn`, operator/function parameters) are *not* `Binding`s —
they live on `Context.lexical` as de Bruijn positions. No default for `origin` — every
construction site says which. -/
structure Binding : Type where
  type : TypedTLAPlus.Typ
  isScheme : Bool := false
  origin : TypedTLAPlus.Origin

/-- The local typing context `Γ`, split by how a name resolves under locally-nameless binding:

- `lexical` — expression-level binders, innermost first. A `.var` reference matching entry `i`
  here elaborates to `Origin.bound i`.
- `named` — everything `Memory`-keyed or top-level (`Origin.free`/`.module`/`.intrinsic`), each
  carrying its own `Binding`. A `.var` match here takes the stored `origin` verbatim.

`lexical` is consulted first, so an expression binder shadows a same-named PlusCal variable for
the scope of its body. -/
structure Context : Type where
  lexical : List (String × TypedTLAPlus.Typ) := []
  named : Std.HashMap String Binding := ∅

/--
  The metavariable context: tracks only whether each metavariable is resolved, and to what.
  `MVarId` is fixed at this project's own `TypedTLAPlus.MVarId` (`:= Nat`).

  The pending-upper-bounds bookkeeping the direction-aware solving algorithm needs on top of this
  is `Elaborator/Subtyping.lean`'s job to layer over this class, not this file's concern.
-/
class MonadMetavarContext (α : outParam Type) (m : Type → Type) where
  /-- Allocate a new, as-yet-unresolved metavariable. -/
  mkFreshMVar : m TypedTLAPlus.MVarId
  /-- Resolve a metavariable to a concrete value. A no-op if already resolved. -/
  assignMVar : TypedTLAPlus.MVarId → α → m Unit
  /-- The metavariable's resolved value, if any. -/
  assigned? : TypedTLAPlus.MVarId → m (Option α)
export MonadMetavarContext (mkFreshMVar assignMVar assigned?)

/-- Backing store for the generic `MonadMetavarContext` instance below: index `n` holds `?n`'s
resolved value, or `none` while still unresolved. -/
structure MetavarContext (α : Type) : Type where
  protected mvars : Array (Option α)

instance {α} : EmptyCollection (MetavarContext α) where
  emptyCollection := ⟨#[]⟩

instance {α m} [Monad m] [Inhabited α] [MonadStateOf (MetavarContext α) m] : MonadMetavarContext α m where
  mkFreshMVar := modifyGet λ ⟨vars⟩ ↦ (vars.size, ⟨vars.push none⟩)
  assignMVar v x := modify λ ⟨vars⟩ ↦
    match vars[v]? with
    | none | some (some _) => ⟨vars⟩
    | some none => ⟨vars.set! v (some x)⟩
  assigned? v := return (← getThe (MetavarContext α)).mvars[v]?.join

/-- The effect bundle the checker's expression/declaration/PlusCal-level rules check against. -/
class abbrev MonadElaborator (m : Type → Type) :=
  MonadReaderOf Context m,
  MonadWithReaderOf Context m,
  MonadMetavarContext TypedTLAPlus.Typ m,
  MonadDiagnostic TCWarning TCError m,
  MonadFresh m

end
