import Elaborator.Errors
import Core.TypedTLAPlus.Syntax

/-!
  The effects the type checker needs (§5.3), following `Desugarer/Monad.lean`'s
  `MonadDesugarerExpr` shape: a local typing context `Γ` (`MonadReaderOf`/`MonadWithReaderOf`,
  lookup semantics per the usual `Γ,x:τ` reading — the most recently `withReader`-inserted
  binding for a name wins, i.e. the rightmost one shadows), a metavariable context (this
  project's own `MonadMetavarContext`, adapted below from prior art's clean, already-generic
  design), and error reporting (`MonadExceptOf TCError`). `MonadFresh` is **not** included here,
  unlike the desugarer — the checker never invents fresh *names*, only fresh metavariables, which
  `MonadMetavarContext.mkFreshMVar` already covers on its own counter.
-/

/-- The local typing context `Γ` (§5.3's `Γ,x:τ` grammar). -/
abbrev Context := Std.HashMap String TypedTLAPlus.Typ

/--
  The metavariable context (§5.3's deliberate deviation from the thesis's literal `Specialize`
  rule) — ported from prior art's `Checker/Typechecker/Monad.lean` (`MonadMetavarContext`/
  `MetavarContext`), a good, genuinely reusable design worth keeping even though the checker
  built around it there is unfinished (`CLAUDE.md`). One change from prior art: `MVarId` is
  fixed at this project's own `TypedTLAPlus.MVarId` (already committed to `:= Nat`,
  `Core/TypedTLAPlus/Syntax.lean`) rather than an associated type of the class — prior art
  needed the indirection since it hadn't committed to a concrete id type yet; this project
  already has.

  Tracks only *resolved-or-not*, same as prior art. The pending-upper-bounds bookkeeping the
  direction-aware solving algorithm needs on top of this (`PLAN.md` §5.3's lower-bound/
  upper-bound/mvar-mvar cases) is `Elaborator/Convertibility.lean`'s job to layer over this
  class, not this file's concern.
-/
class MonadMetavarContext (α : outParam Type) (m : Type → Type) where
  /-- Allocate a new, as-yet-unresolved metavariable. -/
  mkFreshMVar : m TypedTLAPlus.MVarId
  /-- Resolve a metavariable to a concrete value. A no-op if already resolved. -/
  assignMVar : TypedTLAPlus.MVarId → α → m Unit
  /-- The metavariable's resolved value, if any. -/
  assigned? : TypedTLAPlus.MVarId → m (Option α)
export MonadMetavarContext (mkFreshMVar assignMVar assigned?)

/-- Backing store for the generic `MonadMetavarContext` instance below — `Array (Option α)`,
ported verbatim from prior art (see the class doc): index `n` holds `?n`'s resolved value, or
`none` while still unresolved. -/
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

/--
  The effect bundle `Elaborator/Expressions.lean`/`Elaborator/Declarations.lean`/
  `Elaborator/PlusCal.lean` actually check against — see the module doc for why each piece is
  here (and why `MonadFresh` isn't). The module cache `Ξ` (`MonadModuleCache`) is **not** part of
  this bundle, and isn't defined in this file at all: it's not a type-*checking* effect, it's a
  module-*resolution* one — expression/declaration-level checking rules never touch `Ξ` directly,
  only `Elaborator/Modules.lean`'s resolution driver does, and only *before* a module's own
  checking rules start (`Γ` is fully assembled from already-resolved dependencies by then). See
  `Elaborator/Modules.lean` for `MonadModuleCache`/`CacheEntry`.
-/
class abbrev MonadElaborator (m : Type → Type) :=
  MonadReaderOf Context m,
  MonadWithReaderOf Context m,
  MonadMetavarContext TypedTLAPlus.Typ m,
  MonadExceptOf TCError m
