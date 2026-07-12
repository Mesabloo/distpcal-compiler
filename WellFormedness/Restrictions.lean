module

public import WellFormedness.Errors
public import WellFormedness.Monad
public import WellFormedness.Reachability
public import Elaborator.Declarations
public import Core.TypedPlusCal.Syntax
public import Core.TypedTLAPlus.Builtins

public section

/-!
  The expression walker: one unified recursive walk over every `TypedTLAPlus.Expression`
  reachable from the algorithm — every statement's own embedded expression(s), every `Ref.args`
  index expression, and (transitively) every operator/function body reachable by a call the
  algorithm makes, directly or indirectly. Threading one walker rather than three avoids
  re-deriving "which expression positions exist in a statement" three times, and gets the
  transitive check for free: recursing into a called declaration's body re-applies every check
  to it, not just the temporal/action one.

  The recursion/resolution/memoization machinery — `ResolvedDecl`, `Decl.resolve`,
  `resolveInModule`, `Expression.walkReachable`, and the statement-level traversal
  (`Statement`/`Algorithm.walkReachable`) — lives in `WellFormedness/Reachability.lean`, shared
  with `Typed2Computable`'s later use of the same walk. This file supplies the actual checks
  below as two callbacks, `visitStatement`/`visitExpr`, run once per node in the same pre-order
  the walk visits nodes, before recursing into children.

  - **Channel-shapedness**: any subexpression node whose type is Channel-shaped
    (`Typ.isChannelLike`, shared with `Declarations.lean`) is an error. Only nodes that carry
    their own type (`var`/`set`/`seq`/`tuple`/`record`/`recordSet`) are inspected — most
    `Expression` constructors don't store their own overall type (recoverable from context,
    which `Γ` supplied during checking but is discarded by the time this pass runs). This is
    complete anyway: TLA⁺ has no channel-literal syntax, so the only way a `Channel(τ)` value
    can appear in an expression tree is by referencing an already-channel-typed name (`.var`) —
    never by constructing one inline. `receive`'s destination `r` and `assign`'s LHS are *not*
    exempted: a `Ref` never produces an `Expression` node (checked via `inferRef` in
    `Elaborator/PlusCal.lean`, a separate type), so the walker can't see these positions by
    walking expressions alone — `TypedPlusCal.Ref` carries its own resolved `type`
    (`Core/TypedPlusCal/Syntax.lean`) precisely so `TypedPlusCal.Statement.checkRefRestrictions`
    can check it directly, without `Γ`. Only `send`'s/`receive`'s channel argument `c` is
    legitimately Channel-shaped and exempted — its `Ref.args` (index expressions) still aren't.
  - **Global-variable reference**: a `.var name _ origin` where `origin = .module m` and `m`'s
    declaration list has `name` as a `Decl.variables` entry.
  - **Temporal/action operators, direct**: `.opCall (.var op _ _) _` where `op` is one of the
    reserved temporal/action spellings (`[]`/`<>`/`ENABLED`/`UNCHANGED`/`'`/`^+`/`^*`/`^#`). Also
    bans `Expression.stutter` (`[A]_e`) and `fforall`/`eexists` (`\AA`/`\EE`) outright — dedicated
    action/temporal constructors, not `opCall`-based (`fforall`/`eexists` cost nothing:
    unparseable today, commented out in `Parser_/TLAPlus.lean`). `.forall`/`.exists`/`.choose`
    with `dom = none` is an unbounded quantifier.
  - **Temporal/action operators, transitive**: whenever a `.var`/`.opCall (.var _ _ _)` resolves
    (via `origin`) to a `Decl.operator`/`Decl.function`, recurses into that declaration's own
    body with the same full walker — a `StateT (Std.HashSet (String × String))` layer (module ×
    name pairs already fully walked) both guards against looping on a self-recursive `function`
    (`operator`s never self-recurse, per `Elaborator/Declarations.lean`, so only `function`
    bodies can cycle) and memoizes: an operator/function referenced more than once has its body
    walked exactly once, not once per reference. `path : List String` is the breadcrumb
    (innermost first) for the error message — stays a plain argument, not state, since every
    check here throws (stopping the whole pass) rather than continuing.
-/

/-- The per-node checks alone, no recursion of its own — `TypedPlusCal.Statement.walkReachable`'s
shared traversal (`WellFormedness/Reachability.lean`) calls this once per node, as its
`visitExpr`, forwarding into `Expression.walkReachable` for the actual
recursion/resolution/memoization. Uses `resolveInModule` directly for the global-variable check
— it must fire on every reference to a global variable, not just the first, unlike the transitive
into-the-body recursion, which the walk already memoizes for its own purposes. -/
def TypedTLAPlus.Expression.checkNode {m' : Type → Type} [Monad m']
    [MonadDiagnostic Empty WellFormednessError m'] [MonadForeignLookup m']
    (currentModule : String) (ownDecls : List Decl) (path : List String)
    (e : TypedPlusCal.Expression) : m' Unit :=
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

/-- The channel-shapedness check over `s`'s own non-expression positions — `assign`'s LHS `Ref`s
and `receive`'s destination `Ref` `r`, neither of which is an `Expression` node the shared walk's
`visitExpr` would see (`Ref` carries its own resolved `baseType` so `Ref.resultType` can recompute
the reference's result type directly, without `Γ` — see `Core/TypedPlusCal/Syntax.lean`).
`send`'s/`receive`'s channel argument `c` is legitimately Channel-shaped and exempted — only its
index expressions (`Ref.args`, walked by `TypedPlusCal.Statement.walkReachable` itself) are
checked. Supplied as `walkReachable`'s `visitStatement`; the expression-position checks are
`Expression.checkNode`, supplied as its `visitExpr`. -/
def TypedPlusCal.Statement.checkRefRestrictions {b} {m' : Type → Type} [Monad m']
    [MonadDiagnostic Empty WellFormednessError m'] (s : TypedPlusCal.Statement b) : m' Unit :=
  match_source s with
  | .assign asss, pos => asss.forM λ (r, _) ↦
      let τ := TypedPlusCal.Ref.resultType r
      if τ.isChannelLike then throw (.channelInExpression pos τ) else pure ()
  | .receive _ r _, pos =>
      let τ := TypedPlusCal.Ref.resultType r
      if τ.isChannelLike then throw (.channelInExpression pos τ) else pure ()
  | _, _ => pure ()

/-- Runs all the above checks over a whole algorithm, via the shared
`TypedPlusCal.Algorithm.walkReachable` (`WellFormedness/Reachability.lean`), supplying
`Statement.checkRefRestrictions`/`Expression.checkNode` as its two callbacks. `currentModule`/
`ownDecls` come from the enclosing `TypedModule` (`WellFormedness/WellFormedness.lean`) — this
pass alone doesn't have them, since it only receives the embedded `pcalAlgorithm`. The
`ReachabilityClosure` memoization is scoped to this one call — a private `StateT` layer, run from
`{}` and discarded (`.run'`) once this returns: whether an operator was already walked while
checking a previous module has no bearing on checking this one. -/
def TypedPlusCal.Algorithm.checkRestrictions {m' : Type → Type} [Monad m']
    [MonadDiagnostic Empty WellFormednessError m'] [MonadForeignLookup m']
    (currentModule : String) (ownDecls : List Decl) (algo : TypedPlusCal.Algorithm) : m' Unit :=
  let go : StateT ReachabilityClosure m' Unit :=
    TypedPlusCal.Algorithm.walkReachable TypedPlusCal.Statement.checkRefRestrictions
      (TypedTLAPlus.Expression.checkNode currentModule ownDecls) currentModule ownDecls algo
  go.run' {}

end
