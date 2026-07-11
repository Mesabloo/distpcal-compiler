import WellFormedness.Errors
import WellFormedness.Monad
import Elaborator.Declarations
import Core.TypedPlusCal.Syntax

/-!
  The expression walker (`PLAN.md` §5.2a's checks 1, 2(c), 3): one unified recursive walk over
  every `TypedTLAPlus.Expression` reachable from the algorithm — every statement's own embedded
  expression(s), every `Ref.args` index expression, and (transitively) every operator/function
  body reachable by a call the algorithm makes, directly or indirectly. Threading one walker
  rather than three separate ones avoids re-deriving "which expression positions exist in a
  statement" three times, and gets check 3's transitive half for free: recursing into a called
  declaration's body re-applies *every* check to it, not just the temporal/action one.

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

/-- What a name resolves to inside one module's declaration list — only as much detail as the
checks below need: is it a `VARIABLE` (check 2(c)), or an `operator`/`function` with a body to
keep walking (check 3 transitive)? `constants`/`assume` (and "not found", which shouldn't happen
by construction — a name only carries `origin := .module m` because `m` already type-checked
it) all fall through to `none`, i.e. "nothing further to check here." -/
private inductive ResolvedDecl : Type
  | «variable»
  | operatorOrFunction (body : TypedPlusCal.Expression)

private def Decl.resolve (name : String) : Decl → Option ResolvedDecl
  | .constants _ => none
  | .variables xs => if xs.any (·.1 == name) then some .variable else none
  | .assume _ => none
  | .operator _ f _ body => if f == name then some (.operatorOrFunction body) else none
  | .function _ f _ body => if f == name then some (.operatorOrFunction body) else none

/-- Resolves `name` against `m`'s own declaration list — `current`'s own `declarations₁ ++
declarations₂` (already in hand, no lookup) if `m` is the module currently being checked, else
`lookupForeign m`'s (`WellFormedness/Monad.lean`). `none` if `m` can't be found at all (should be
unreachable — see `ResolvedDecl`'s own doc comment) or `name` isn't in its list (a `constants`/
`assume` entry, or genuinely absent). -/
private def resolveInModule {m' : Type → Type} [Monad m'] [MonadForeignLookup m']
    (currentModule : String) (ownDecls : List Decl) (targetModule name : String) : m' (Option ResolvedDecl) := do
  let decls ← if targetModule == currentModule then pure ownDecls
    else match ← lookupForeign targetModule with
      | some tm => pure (tm.declarations₁ ++ tm.declarations₂)
      | none => pure []
  return decls.findSome? (Decl.resolve name)

/-- The eight reserved temporal/action operator spellings check 3 bans, by canonical name
(`Desugarer/TLAPlus.lean`'s `PrefixOperator.canonicalName`/`PostfixOperator.canonicalName`). -/
private def reservedTemporalActionNames : List String :=
  ["[]", "<>", "ENABLED", "UNCHANGED", "'", "^+", "^*", "^#"]

mutual
  /-- Checks 1/2(c)/3 over `e` and everything reachable from it, transitively. -/
  partial def TypedTLAPlus.Expression.checkRestrictions {m' : Type → Type} [Monad m']
      [MonadExceptOf WellFormednessError m'] [MonadForeignLookup m']
      [MonadStateOf (Std.HashSet (String × String)) m']
      (currentModule : String) (ownDecls : List Decl) (path : List String)
      (e : TypedPlusCal.Expression) : m' Unit :=
    let recurse := TypedTLAPlus.Expression.checkRestrictions currentModule ownDecls path
    match_source e with
    | .var name τ origin, pos => do
      if τ.isChannelLike then throw (.channelInExpression pos τ)
      match origin with
      | .binder | .intrinsic => pure ()
      | .module m => do
        match ← resolveInModule currentModule ownDecls m name with
        | some .variable => throw (.globalTLAPlusVariable pos name m)
        | some (.operatorOrFunction body) => do
          let visited ← getThe (Std.HashSet (String × String))
          unless visited.contains (m, name) do
            modifyThe (Std.HashSet (String × String)) (·.insert (m, name))
            TypedTLAPlus.Expression.checkRestrictions m ownDecls (path ++ [name]) body
        | none => pure ()
    | .opCall f args, pos => do
      match f with
      | .var op _ _ => if reservedTemporalActionNames.contains op then throw (.bareTemporalOrAction pos op path)
      | _ => pure ()
      recurse f
      args.forM recurse
    | .forall _ _ dom body, pos => do
      if dom.isNone then throw (.unboundedQuantifier pos path)
      dom.forM recurse
      recurse body
    | .exists _ _ dom body, pos => do
      if dom.isNone then throw (.unboundedQuantifier pos path)
      dom.forM recurse
      recurse body
    | .fforall .., pos => throw (.bareTemporalOrAction pos "\\AA" path)
    | .eexists .., pos => throw (.bareTemporalOrAction pos "\\EE" path)
    | .choose _ _ dom body, pos => do
      if dom.isNone then throw (.unboundedQuantifier pos path)
      dom.forM recurse
      recurse body
    | .set es τ, pos => do
      if τ.isChannelLike then throw (.channelInExpression pos τ)
      es.forM recurse
    | .collect _ _ dom body, _ => do recurse dom; recurse body
    | .map' body _ _ dom, _ => do recurse body; recurse dom
    | .fnCall f idx, _ => do recurse f; recurse idx
    | .fn _ _ dom body, _ => do recurse dom; recurse body
    | .fnSet dom cod, _ => do recurse dom; recurse cod
    | .record fs, pos =>
      fs.forM λ (τ, _, e) ↦ do
        if τ.isChannelLike then throw (.channelInExpression pos τ)
        recurse e
    | .recordSet fs, pos =>
      fs.forM λ (τ, _, e) ↦ do
        if τ.isChannelLike then throw (.channelInExpression pos τ)
        recurse e
    | .except e upds, _ => do
      recurse e
      upds.forM λ (path', newVal) ↦ do
        path'.forM λ
          | .inl _ => pure ()
          | .inr idx => recurse idx
        recurse newVal
    | .recordAccess e _, _ => recurse e
    | .tuple es, pos =>
      es.forM λ (τ, e) ↦ do
        if τ.isChannelLike then throw (.channelInExpression pos τ)
        recurse e
    | .seq es τ, pos => do
      if τ.isChannelLike then throw (.channelInExpression pos τ)
      es.forM recurse
    | .if c t f, _ => do recurse c; recurse t; recurse f
    | .case branches other, _ => do
      branches.forM λ (p, e) ↦ do recurse p; recurse e
      other.forM recurse
    | .nat _, _ | .str _, _ | .true, _ | .false, _ => pure ()
    | .stutter .., pos => throw (.bareTemporalOrAction pos "[.]_." path)
    -- Unreachable in practice (every `mvar` is substituted away before the checker's output is
    -- ever handed to a caller) — recurse defensively rather than special-case an impossible input.
    | .mvar _ e, _ => recurse e
end

/-- Walks every expression/`Ref.args` reachable from `s`. -/
partial def TypedPlusCal.Statement.checkRestrictions {b} {m' : Type → Type} [Monad m']
    [MonadExceptOf WellFormednessError m'] [MonadForeignLookup m']
    [MonadStateOf (Std.HashSet (String × String)) m']
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
  let go : StateT (Std.HashSet (String × String)) m' Unit := do
    for p in algo.processes do
      for thread in p.threads do
        for (_, blk) in thread do
          TypedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkRestrictions currentModule ownDecls) blk
  go.run' {}
