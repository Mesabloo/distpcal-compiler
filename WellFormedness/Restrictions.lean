import WellFormedness.Errors
import WellFormedness.Monad
import WellFormedness.Reachability
import Elaborator.Declarations
import Core.TypedPlusCal.Syntax
import Core.TypedTLAPlus.Builtins

/-!
  The expression walker (`PLAN.md` §5.2a's checks 1, 2(c), 3): one unified recursive walk over
  every `TypedTLAPlus.Expression` reachable from the algorithm — every statement's own embedded
  expression(s), every `Ref.args` index expression, and (transitively) every operator/function
  body reachable by a call the algorithm makes, directly or indirectly. Threading one walker
  rather than three separate ones avoids re-deriving "which expression positions exist in a
  statement" three times, and gets check 3's transitive half for free: recursing into a called
  declaration's body re-applies *every* check to it, not just the temporal/action one.

  The recursion/resolution/memoization machinery itself — `ResolvedDecl`, `Decl.resolve`,
  `resolveInModule`, `TypedTLAPlus.Expression.walkReachable` — lives in
  `WellFormedness/Reachability.lean`, shared with `Typed2Computable`'s own later use of the same
  walk. This file supplies the actual checks (below) as `walkReachable`'s `visit` callback, run
  once per node in the same pre-order the walk visits nodes in, before recursing into children —
  same visiting order the original fused version used.

  - **Check 1**: any subexpression node whose type is Channel-shaped (`Typ.isChannelLike`,
    shared with `Declarations.lean`) is an error. Only nodes that actually carry a type
    (`var`/`set`/`seq`/`tuple`/`record`/`recordSet`) are inspected — most `Expression`
    constructors don't store their own overall type at all (`Core/TypedTLAPlus/Syntax.lean`'s
    own doc comment: recoverable from context, which `Γ` supplied during checking but is
    discarded by the time this pass runs). This is complete anyway: TLA⁺ has no channel-literal
    syntax, so the only way a `Channel(τ)` value can ever appear in an expression tree at all is
    by referencing an already-channel-typed name (`.var`) — never by constructing one inline.
    `receive`'s destination `r` is *not* exempted, nor is `assign`'s LHS: a `Ref` never produces
    an `Expression` node (checked via `inferRef` in `Elaborator/PlusCal.lean`, a wholly separate
    type), so the walker can't see these positions by walking expressions alone — `TypedPlusCal.
    Ref` carries its own resolved `type` (`Core/TypedPlusCal/Syntax.lean`) precisely so
    `TypedPlusCal.Statement.checkRestrictions`'s `checkNonChannelRef` can check it directly,
    without needing `Γ`. Only `send`'s/`receive`'s channel argument `c` is legitimately
    Channel-shaped and exempted from this — its `Ref.args` (index expressions) still aren't.
  - **Check 2(c)**: a `.var name _ origin` where `origin = .module m` and `m`'s declaration
    list has `name` as a `Decl.variables` entry.
  - **Check 3, direct**: `.opCall (.var op _ _) _` where `op` is one of the eight temporal/
    action spellings (`[]`/`<>`/`ENABLED`/`UNCHANGED`/`'`/`^+`/`^*`/`^#` — the plan text says
    "six" but lists eight; going with the literal list, `PLAN.md` §9.24 on `^+`/`^*`/`^#`
    specifically). Also bans `Expression.stutter` (`[A]_e`) and `fforall`/`eexists` (`\AA`/
    `\EE`) outright — dedicated action/temporal constructors, not `opCall`-based, confirmed
    with the project owner to ban too even though the plan's literal enumeration only lists the
    `opCall` spellings (`fforall`/`eexists` cost nothing: currently unparseable, commented out
    in `Parser_/TLAPlus.lean`). `.forall`/`.exists`/`.choose` with `dom = none` → unbounded
    quantifier, the new half of check 3.
  - **Check 3, transitive**: whenever a `.var`/`.opCall (.var _ _ _)` resolves (via `origin`) to
    a `Decl.operator`/`Decl.function`, recurse into *that* declaration's own body with the same
    full walker — a `StateT (Std.HashSet (String × String))` layer (module × name pairs already
    fully walked) both guards against looping on a self-recursive `function` (`operator`s never
    self-recurse, per `Elaborator/Declarations.lean`'s own doc comment, so only `function`
    bodies can actually cycle) *and* memoizes: an operator/function referenced more than once
    anywhere in the algorithm has its body walked exactly once, not once per reference (a plain
    argument threaded only *down* one recursive chain, as an earlier version of this file did,
    doesn't share insertions across sibling calls — e.g. `f(x) + f(y)` would re-walk `f`'s body
    twice; genuine shared state does). `path : List String` is the breadcrumb (innermost first)
    for check 3's message — stays a plain argument, not state, since it's purely per-message and
    every check here throws (stopping the whole pass) rather than continuing, so it never needs
    to be visible across sibling branches the way `visited` does.
-/

/-- Checks 1/2(c)/3 over `e` and everything reachable from it, transitively — a thin per-node
`visit`, run once per node by `WellFormedness/Reachability.lean`'s shared
`TypedTLAPlus.Expression.walkReachable`, which owns the actual recursion/resolution/memoization.
`visit` itself never recurses (the walk does that); each arm below only inspects the current
node, using `resolveInModule` directly for check 2(c) — a leaf check, independent of the walk's
own memoized resolution (check 2(c) must fire on *every* reference to a global variable, not just
the first, unlike check 3-transitive's into-the-body recursion, which the walk already memoizes
for its own purposes). -/
def TypedTLAPlus.Expression.checkRestrictions {m' : Type → Type} [Monad m']
    [MonadExceptOf WellFormednessError m'] [MonadForeignLookup m']
    [MonadStateOf ReachabilityClosure m']
    (currentModule : String) (ownDecls : List Decl) (path : List String)
    (e : TypedPlusCal.Expression) : m' Unit :=
  let visit (path : List String) (e : TypedPlusCal.Expression) : m' Unit :=
    match_source e with
    | .var name τ origin, pos => do
      if τ.isChannelLike then throw (.channelInExpression pos τ)
      match origin with
      | .binder | .intrinsic => pure ()
      | .module m => do
        match ← resolveInModule currentModule ownDecls m name with
        | some (.variable _) => throw (.globalTLAPlusVariable pos name m)
        | _ => pure ()
    | .opCall f _, pos => do
      match f with
      | .var op _ _ => if TypedTLAPlus.reservedTemporalActionNames.contains op then throw (.bareTemporalOrAction pos op path)
      | _ => pure ()
    | .forall _ _ dom _, pos => if dom.isNone then throw (.unboundedQuantifier pos path) else pure ()
    | .exists _ _ dom _, pos => if dom.isNone then throw (.unboundedQuantifier pos path) else pure ()
    | .fforall .., pos => throw (.bareTemporalOrAction pos "\\AA" path)
    | .eexists .., pos => throw (.bareTemporalOrAction pos "\\EE" path)
    | .choose _ _ dom _, pos => if dom.isNone then throw (.unboundedQuantifier pos path) else pure ()
    | .set _ τ, pos => if τ.isChannelLike then throw (.channelInExpression pos τ) else pure ()
    | .record fs, pos => fs.forM λ (τ, _, _) ↦ if τ.isChannelLike then throw (.channelInExpression pos τ) else pure ()
    | .recordSet fs, pos => fs.forM λ (τ, _, _) ↦ if τ.isChannelLike then throw (.channelInExpression pos τ) else pure ()
    | .tuple es, pos => es.forM λ (τ, _) ↦ if τ.isChannelLike then throw (.channelInExpression pos τ) else pure ()
    | .seq _ τ, pos => if τ.isChannelLike then throw (.channelInExpression pos τ) else pure ()
    | .stutter .., pos => throw (.bareTemporalOrAction pos "[.]_." path)
    | _, _ => pure ()
  TypedTLAPlus.Expression.walkReachable visit currentModule ownDecls path e

/-- Walks every expression/`Ref.args` reachable from `s`. -/
partial def TypedPlusCal.Statement.checkRestrictions {b} {m' : Type → Type} [Monad m']
    [MonadExceptOf WellFormednessError m'] [MonadForeignLookup m']
    [MonadStateOf ReachabilityClosure m']
    (currentModule : String) (ownDecls : List Decl) (s : TypedPlusCal.Statement b) : m' Unit :=
  let checkExpr (e : TypedPlusCal.Expression) : m' Unit :=
    TypedTLAPlus.Expression.checkRestrictions currentModule ownDecls [] e
  -- `send`'s/`receive`'s channel argument `c` is a legitimate channel reference — only its
  -- index expressions (`Ref.args`) are subject to check 1, not its own type.
  let checkRef (r : TypedPlusCal.Ref) : m' Unit := r.args.forM checkExpr
  -- Every other `Ref` position (`assign`'s LHS, `receive`'s destination `r`) is *not* exempt:
  -- referencing an already-declared channel there is exactly check 1's concern, just via a
  -- `Ref` (which never produces an `Expression` node) instead of a `.var`.
  let checkNonChannelRef (pos : SourceSpan) (r : TypedPlusCal.Ref) : m' Unit := do
    if r.type.isChannelLike then throw (.channelInExpression pos r.type)
    checkRef r
  match_source s with
  | .goto _, _ | .skip, _ => pure ()
  | .print e, _ => checkExpr e
  | .assign asss, pos => asss.forM λ (r, e) ↦ do checkNonChannelRef pos r; checkExpr e
  | .if cond B₁ B₂, _ => do
    checkExpr cond
    TypedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkRestrictions currentModule ownDecls) B₁
    TypedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkRestrictions currentModule ownDecls) B₂
  | .await e, _ => checkExpr e
  | .with _ _ _ val B, _ => do
    checkExpr val
    TypedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkRestrictions currentModule ownDecls) B
  | .assert e, _ => checkExpr e
  | .either branches, _ =>
    TypedPlusCal.Branches.forStatements (TypedPlusCal.Statement.checkRestrictions currentModule ownDecls) branches
  | .while cond B, _ => do
    checkExpr cond
    TypedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkRestrictions currentModule ownDecls) B
  | .receive c r _, pos => do checkRef c; checkNonChannelRef pos r
  | .send c e, _ => do checkRef c; checkExpr e
  | .multicast _ filter, _ => do
    filter.binds.forM λ (_, _, _, e) ↦ checkExpr e
    checkExpr filter.val

/-- Checks 1/2(c)/3 over a whole algorithm. `currentModule`/`ownDecls` come from the enclosing
`TypedModule` (`WellFormedness/WellFormedness.lean`) — this pass alone doesn't have them, since
it only ever receives the embedded `pcalAlgorithm`, not the whole module. The `visited`-set
memoization (see the module doc above) is scoped to just this one call — a private `StateT`
layer, run from `{}` and discarded once this returns, invisible to callers: whether an operator
was already walked while checking a *previous* module has no bearing on checking this one. -/
def TypedPlusCal.Algorithm.checkRestrictions {m' : Type → Type} [Monad m']
    [MonadExceptOf WellFormednessError m'] [MonadForeignLookup m']
    (currentModule : String) (ownDecls : List Decl) (algo : TypedPlusCal.Algorithm) : m' Unit :=
  let go : StateT ReachabilityClosure m' Unit := do
    for p in algo.processes do
      for thread in p.threads do
        for (_, blk) in thread do
          TypedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkRestrictions currentModule ownDecls) blk
  go.run' {}
