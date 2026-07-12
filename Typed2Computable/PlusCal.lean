import Typed2Computable.TLAPlus
import Core.TypedPlusCal.Syntax
import Core.ComputablePlusCal.Syntax

/-!
  `TypedPlusCal.{Ref,MulticastFilter,Statement,Block,Branches,Declarations,Process,Algorithm}
  .toComputable` — translates a checked PlusCal algorithm (and its pieces) into `ComputablePlusCal`,
  delegating every leaf `TypedTLAPlus.Expression` to `Expression.toComputable`
  (`Typed2Computable/TLAPlus.lean`). `τ` fields (`Ref.type`, `Statement.with`'s `ann`,
  `Declarations`'s per-binding annotations, …) pass through unconverted, same reason as
  `Typed2Computable/TLAPlus.lean`'s own note: `ComputableTLAPlus.Typ` is a literal reuse of
  `TypedTLAPlus.Typ`, not a second copy.

  `ElaboratedPlusCal` (`Core/TypedPlusCal/Syntax.lean`, the shared generic layer both
  `TypedPlusCal` and `ComputablePlusCal` pin) doesn't derive `Bifunctor`/`Bitraversable` instances
  of its own the way `CorePlusCal`'s equivalently-shaped types do — so `Ref`/`Statement`/`Block`/
  `Branches`/`Declarations`/`Process`/`Algorithm` each get a hand-written `toComputable` below,
  mirroring `CorePlusCal.Statement.bitraverse`'s own per-constructor shape
  (`Core/CorePlusCal/Syntax.lean:134-163`) with `f := pure` (the `τ`-side function, always the
  identity here) folded away. `MulticastFilter` is the one exception: it's reused generically from
  `SurfacePlusCal`, which *does* carry a registered `Bitraversable` instance, so its `toComputable`
  is just `bitraverse pure Expression.toComputable` (same precedent as `Desugarer/TLAPlus.lean`'s
  own `bitraverse pure Expression.desugar` calls).

  Every `ElaboratedPlusCal`-family conversion below is invoked via **qualified call**
  (`TypedPlusCal.Block.toComputable B`, not `B.toComputable`) rather than dot-notation — the same
  "dot-called extension methods are qualified-call sites" issue task 4 already hit: dot-notation on
  a `TypedPlusCal.X`-typed value resolves through the abbrev to `ElaboratedPlusCal`'s own namespace,
  which has no such method. Only `TypedTLAPlus.Expression`-typed leaves stay dot-called
  (`e.toComputable`), since `Expression` is a real inductive matching its own declared name, not an
  abbrev layer.
-/

variable {m : Type → Type} [Monad m] [MonadExceptOf ComputableError m]

/-- `Ref.args`' `.inr` (index) entries delegated to `Expression.toComputable`; `.inl` (field)
entries and `name`/`type` pass through unconverted. -/
def TypedPlusCal.Ref.toComputable (r : TypedPlusCal.Ref) : m ComputablePlusCal.Ref := do
  let args ← r.args.mapM λ
    | .inl field => pure (Sum.inl field)
    | .inr e => Sum.inr <$> TypedTLAPlus.Expression.toComputable e
  pure { r with args }

/-- `SurfacePlusCal.MulticastFilter`'s own registered `Bitraversable` instance, with the `τ`-side
function fixed to `pure` (identity) — see the module doc above. -/
def TypedPlusCal.MulticastFilter.toComputable (filter : TypedPlusCal.MulticastFilter) :
    m ComputablePlusCal.MulticastFilter :=
  bitraverse pure TypedTLAPlus.Expression.toComputable filter

mutual
  /-- Mirrors `CorePlusCal.Statement.bitraverse`'s own per-constructor shape
  (`Core/CorePlusCal/Syntax.lean:134-153`), `f := pure` folded away — no position to reattach,
  unlike `TypedTLAPlus.Expression.toComputable` (`ElaboratedPlusCal.Statement` carries none, per
  the module doc above). `partial`: same reason `Statement.bitraverse` itself is — structural
  recursion isn't visibly decreasing to Lean through the mutual `Block`/`Branches` nesting. -/
  partial def TypedPlusCal.Statement.toComputable {b : Bool} :
      TypedPlusCal.Statement b → m (ComputablePlusCal.Statement b)
    | .goto label => pure (.goto label)
    | .skip => pure .skip
    | .print e => .print <$> e.toComputable
    | .assign upds => .assign <$> upds.mapM λ (r, e) ↦
        Prod.mk <$> TypedPlusCal.Ref.toComputable r <*> e.toComputable
    | .if cond B₁ B₂ => (.if · · ·) <$> cond.toComputable
        <*> TypedPlusCal.Block.toComputable B₁ <*> TypedPlusCal.Block.toComputable B₂
    | .await e => .await <$> e.toComputable
    | .with var ann eq val B => (.with var ann eq · ·) <$> val.toComputable
        <*> TypedPlusCal.Block.toComputable B
    | .assert e => .assert <$> e.toComputable
    | .either branches => .either <$> TypedPlusCal.Branches.toComputable branches
    | .while cond B => (.while · ·) <$> cond.toComputable <*> TypedPlusCal.Block.toComputable B
    | .receive c r coe => (.receive · · coe) <$> TypedPlusCal.Ref.toComputable c
        <*> TypedPlusCal.Ref.toComputable r
    | .send c e => (.send · ·) <$> TypedPlusCal.Ref.toComputable c <*> e.toComputable
    | .multicast c filter => .multicast c <$> TypedPlusCal.MulticastFilter.toComputable filter

  /-- Mirrors `CorePlusCal.Block.bitraverse`. -/
  partial def TypedPlusCal.Block.toComputable {b : Bool} :
      TypedPlusCal.Block b → m (ComputablePlusCal.Block b)
    | .mk begin «end» => (.mk · ·) <$> begin.mapM TypedPlusCal.Statement.toComputable
        <*> TypedPlusCal.Statement.toComputable «end»

  /-- Mirrors `CorePlusCal.Branches.bitraverse`. -/
  partial def TypedPlusCal.Branches.toComputable {b : Bool} :
      TypedPlusCal.Branches b → m (ComputablePlusCal.Branches b)
    | .either B => .either <$> TypedPlusCal.Block.toComputable B
    | .or B rest => (.or · ·) <$> TypedPlusCal.Block.toComputable B
        <*> TypedPlusCal.Branches.toComputable rest
end

/-- Mirrors `CorePlusCal.Declarations.bitraverse` — every field carries leaf expressions, so
nothing passes through via `{d with ...}` the way `Process`/`Algorithm` below can. -/
def TypedPlusCal.Declarations.toComputable (d : TypedPlusCal.Declarations) :
    m ComputablePlusCal.Declarations := do
  let «variables» ← d.variables.mapM λ (name, τ, isParam, init) ↦ do
    let init' ← init.mapM λ (isEq, e) ↦ (isEq, ·) <$> e.toComputable
    pure (name, τ, isParam, init')
  let channels ← d.channels.mapM λ (name, τ, es) ↦
    (name, τ, ·) <$> es.mapM TypedTLAPlus.Expression.toComputable
  let fifos ← d.fifos.mapM λ (name, τ, es) ↦
    (name, τ, ·) <$> es.mapM TypedTLAPlus.Expression.toComputable
  pure { «variables», channels, fifos }

/-- Mirrors `CorePlusCal.Process.bitraverse`; `isFair`/`name`/`«=|∈»` pass through unconverted via
`{p with ...}`. -/
def TypedPlusCal.Process.toComputable (p : TypedPlusCal.Process) : m ComputablePlusCal.Process := do
  let mailbox ← p.mailbox.mapM λ (name, es) ↦
    (name, ·) <$> es.mapM TypedTLAPlus.Expression.toComputable
  let id ← p.id.toComputable
  let localState ← TypedPlusCal.Declarations.toComputable p.localState
  let threads ← p.threads.mapM λ thread ↦ thread.mapM λ (label, B) ↦
    (label, ·) <$> TypedPlusCal.Block.toComputable B
  pure { p with mailbox, id, localState, threads }

/-- Mirrors `CorePlusCal.Algorithm.bitraverse`; `isFair`/`name` pass through unconverted via
`{algo with ...}`. -/
def TypedPlusCal.Algorithm.toComputable (algo : TypedPlusCal.Algorithm) :
    m ComputablePlusCal.Algorithm := do
  let globalState ← TypedPlusCal.Declarations.toComputable algo.globalState
  let processes ← algo.processes.mapM TypedPlusCal.Process.toComputable
  pure { algo with globalState, processes }
