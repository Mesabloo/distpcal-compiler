module

public import Elaborator.Errors
public import Core.TypedTLAPlus.Syntax
public import Common.Fresh

public section


/-! The effects the type checker needs: a local typing context `Γ`, a metavariable context,
error reporting, and fresh-name generation. -/

/-- One `Γ` binding: its type; whether it's a *scheme* (a top-level `operator`/`function`
definition, freshened into new metavariables on every `.var` reference in `Elaborator/
Expressions.lean`'s `inferExpr`) versus an ordinary monomorphic binding (`CONSTANT`/`VARIABLE`
declarations, and every binder — parameters, quantifiers, `CHOOSE`, `EXCEPT`, PlusCal
variables/channels — used exactly as declared); and its `origin` (`Core/TypedTLAPlus/Syntax.lean`'s
`Origin`): a binder or a top-level declaration. Only declarations generalize to schemes; binders
are fixed for the scope of their one body. No default for `origin` — every construction site must
say which. -/
structure Binding : Type where
  type : TypedTLAPlus.Typ
  isScheme : Bool := false
  origin : TypedTLAPlus.Origin

/-- The local typing context `Γ` (`Γ,x:τ` grammar). -/
abbrev Context := Std.HashMap String Binding

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
