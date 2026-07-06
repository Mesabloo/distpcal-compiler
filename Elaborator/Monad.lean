import Elaborator.Errors
import Core.TypedTLAPlus.Syntax
import Common.Fresh

/-! The effects the type checker needs: a local typing context `Γ`, a metavariable context,
error reporting, and fresh-name generation. -/

/-- One `Γ` binding: its type, and whether it's a *scheme* — a top-level `operator`/`function`
definition, freshened into new metavariables on every `.var` reference (`Elaborator/
Expressions.lean`'s `inferExpr`) — versus an ordinary monomorphic binding (`CONSTANT`/`VARIABLE`
declarations, and every binder: operator/function parameters, quantifiers, `CHOOSE`, `EXCEPT`,
PlusCal variables/channels), used exactly as declared. Only a declaration has a scheme to
generalize in the first place; a binder is fixed for the scope of the one body it's bound in. -/
structure Binding : Type where
  type : TypedTLAPlus.Typ
  isScheme : Bool := false

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
  private mvars : Array (Option α)

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
  MonadExceptOf TCError m,
  MonadFresh m
