module

public import Typed2Computable.TLAPlus
public import Core.TypedPlusCal.Syntax
public import Core.ComputablePlusCal.Syntax

public section

/-!
  `TypedPlusCal.{Ref,Multicast,Statement,Block,Branches,Declarations,Process,Algorithm}
  .toComputable` — translates a checked PlusCal algorithm (and its pieces) into `ComputablePlusCal`,
  delegating every leaf `TypedTLAPlus.Expression` to `Expression.toComputable`
  (`Typed2Computable/TLAPlus.lean`). `τ` fields (`Ref.baseType`, `Statement.with`'s `ann`,
  `Declarations`'s per-binding annotations, …) pass through unconverted, same reason as
  `Typed2Computable/TLAPlus.lean`'s own note: `ComputableTLAPlus.Typ` is a literal reuse of
  `TypedTLAPlus.Typ`, not a second copy.

  Position-carrying nodes (`Statement`, `Process`, `Algorithm`) are re-registered at their source
  node's own span via `match_source`/`@@`, the same convention `CorePlusCal.Statement.bitraverse`
  and `Elaborator/PlusCal.lean` follow. `Ref`/`Block`/`Branches`/`Declarations` are not
  position-carrying anywhere in this codebase, and nothing reads a span off one.

  `ElaboratedPlusCal` (`Core/TypedPlusCal/Syntax.lean`, the shared generic layer both
  `TypedPlusCal` and `ComputablePlusCal` pin) doesn't derive `Bifunctor`/`Bitraversable` instances
  of its own the way `CorePlusCal`'s equivalently-shaped types do — so `Ref`/`Statement`/`Block`/
  `Branches`/`Declarations`/`Process`/`Algorithm` each get a hand-written `toComputable` below,
  mirroring `CorePlusCal.Statement.bitraverse`'s own per-constructor shape with `f := pure` (the
  `τ`-side function, always the identity here) folded away. `Multicast` is the one exception: it's
  reused generically from `CorePlusCal`, which *does* carry a registered `Bitraversable` instance,
  so its `toComputable` is just `bitraverse pure Expression.toComputable`.

  Every `ElaboratedPlusCal`-family conversion below is invoked via **qualified call**
  (`TypedPlusCal.Block.toComputable B`, not `B.toComputable`) rather than dot-notation:
  dot-notation on a `TypedPlusCal.X`-typed value resolves through the abbrev to
  `ElaboratedPlusCal`'s own namespace, which has no such method. Only `TypedTLAPlus.Expression`-
  typed leaves stay dot-called (`e.toComputable`), since `Expression` is a real inductive matching
  its own declared name, not an abbrev layer.
-/

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty ComputableError m]

/-- `Ref.args`' `.inr` (index) entries delegated to `Expression.toComputable`; `.inl` (field)
entries and `name`/`baseType` pass through unconverted. -/
def TypedPlusCal.Ref.toComputable (r : TypedPlusCal.Ref) : m ComputablePlusCal.Ref := do
  let args ← r.args.mapM λ
    | .inl field => pure (Sum.inl field)
    | .inr e => Sum.inr <$> TypedTLAPlus.Expression.toComputable e
  pure { r with args }

/-- `CorePlusCal.Multicast`'s own registered `Bitraversable` instance, with the `τ`-side
function fixed to `pure` (identity) — see the module doc above. -/
def TypedPlusCal.Multicast.toComputable (filter : TypedPlusCal.Multicast) :
    m ComputablePlusCal.Multicast :=
  bitraverse pure TypedTLAPlus.Expression.toComputable filter

mutual
  /-- Mirrors `CorePlusCal.Statement.bitraverse`'s own per-constructor shape, `f := pure` folded
  away, and reattaches the source
  statement's own span to the translated one exactly the way `Statement.bitraverse` and
  `TypedTLAPlus.Expression.toComputable` do — a `ComputablePlusCal.Statement` whose position is
  never registered is a position `posOf` cannot answer for, and it answers with an unrelated
  node's span rather than failing (`Common/Position.lean`). `partial`: same reason
  `Statement.bitraverse` itself is — structural recursion isn't visibly decreasing to Lean
  through the mutual `Block`/`Branches` nesting. -/
  partial def TypedPlusCal.Statement.toComputable {b : Bool} (s : TypedPlusCal.Statement b) :
      m (ComputablePlusCal.Statement b) := match_source s with
    | .goto label, pos => pure (.goto label @@ pos)
    | .skip, pos => pure (.skip @@ pos)
    | .print e, pos => (.print · @@ pos) <$> e.toComputable
    | .assign upds, pos => (.assign · @@ pos) <$> upds.mapM λ (r, e) ↦
        Prod.mk <$> TypedPlusCal.Ref.toComputable r <*> e.toComputable
    | .if cond B₁ B₂, pos => (.if · · · @@ pos) <$> cond.toComputable
        <*> TypedPlusCal.Block.toComputable B₁ <*> TypedPlusCal.Block.toComputable B₂
    | .await e, pos => (.await · @@ pos) <$> e.toComputable
    | .with var ann eq val B, pos => (.with var ann eq · · @@ pos) <$> val.toComputable
        <*> TypedPlusCal.Block.toComputable B
    | .assert e, pos => (.assert · @@ pos) <$> e.toComputable
    | .either branches, pos => (.either · @@ pos) <$> TypedPlusCal.Branches.toComputable branches
    | .while cond B, pos => (.while · · @@ pos) <$> cond.toComputable <*> TypedPlusCal.Block.toComputable B
    | .receive c r coe, pos => (.receive · · coe @@ pos) <$> TypedPlusCal.Ref.toComputable c
        <*> TypedPlusCal.Ref.toComputable r
    | .send c e, pos => (.send · · @@ pos) <$> TypedPlusCal.Ref.toComputable c <*> e.toComputable
    | .multicast c filter, pos => (.multicast c · @@ pos) <$> TypedPlusCal.Multicast.toComputable filter

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
  pure ({ p with mailbox, id, localState, threads } @@ posOf p)

/-- Mirrors `CorePlusCal.Algorithm.bitraverse`; `isFair`/`name` pass through unconverted via
`{algo with ...}`. -/
def TypedPlusCal.Algorithm.toComputable (algo : TypedPlusCal.Algorithm) :
    m ComputablePlusCal.Algorithm := do
  let globalState ← TypedPlusCal.Declarations.toComputable algo.globalState
  let processes ← algo.processes.mapM TypedPlusCal.Process.toComputable
  pure ({ algo with globalState, processes } @@ posOf algo)

end
