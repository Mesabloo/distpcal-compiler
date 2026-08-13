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

variable {m : Type → Type} [Monad m] [MonadDiagnostic WellFormednessWarning WellFormednessError m]

/-- The channel-shapedness check itself, at one type and one position — every node-level check
below is this applied to whichever type that node carries. -/
private def checkNotChannel (pos : SourceSpan) (τ : TypedTLAPlus.Typ) : m Unit :=
  if τ.isChannelLike then throw (.channelInExpression pos τ) else pure ()

/-- The per-node checks alone, no recursion of its own — `TypedPlusCal.Statement.walkReachable`'s
shared traversal (`WellFormedness/Reachability.lean`) calls this once per node, as its
`visitExpr`, forwarding into `Expression.walkReachable` for the actual
recursion/resolution/memoization. Uses `resolveInModule` directly for the global-variable check
— it must fire on every reference to a global variable, not just the first, unlike the transitive
into-the-body recursion, which the walk already memoizes for its own purposes. -/
def TypedTLAPlus.Expression.checkNode [MonadForeignLookup m]
    (currentModule : String) (ownDecls : List Decl) (path : List String)
    (e : TypedPlusCal.Expression) : m Unit :=
  match_source e with
  | .var name τ origin, pos => do
    checkNotChannel pos τ
    match origin with
    | .binder | .intrinsic => pure ()
    | .module declModule => do
      match ← resolveInModule currentModule ownDecls declModule name with
      | some (.variable _) => throw (.globalTLAPlusVariable pos name declModule)
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
  | .set _ τ, pos => checkNotChannel pos τ
  | .record fs, pos => fs.forM λ (τ, _, _) ↦ checkNotChannel pos τ
  | .recordSet fs, pos => fs.forM λ (τ, _, _) ↦ checkNotChannel pos τ
  | .tuple es, pos => es.forM λ (τ, _) ↦ checkNotChannel pos τ
  | .seq _ τ, pos => checkNotChannel pos τ
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
def TypedPlusCal.Statement.checkRefRestrictions {b} (s : TypedPlusCal.Statement b) : m Unit :=
  match_source s with
  | .assign asss, pos => asss.forM λ (r, _) ↦ checkNotChannel pos (TypedPlusCal.Ref.resultType r)
  | .receive _ r _, pos => checkNotChannel pos (TypedPlusCal.Ref.resultType r)
  | _, _ => pure ()

/-! ## One receiving channel per process

  `Guarded2Network` (§5.5) compiles every `receive` in a process into reads off **one** shared
  `inbox` sequence, fed by a `.rx` thread per channel. That is only faithful while a process
  receives from a single channel: with two, both `.rx` threads append into the same `inbox`, the
  channel a message came from is no longer recoverable at the consumption site, and
  `x := Head(inbox)` can hand a `receive(c₂, x)` a message that arrived on `c₁`. The pass's own
  per-thread dedup compounds it — `.rx` threads are deduplicated by channel *name*, so
  `receive(agt[self], …)` and `receive(agt[other], …)` in one thread produce a single `.rx` thread
  draining only the first.

  The paper (`reference/jlamp.pdf` §4.1) assumes this away by construction: its `rxₚ` drains
  `mailboxₚ`, the one channel a process listens on. Checked here rather than assumed, so the
  refinement proof's precondition is one the front end actually enforces.

  The reference channel is the process's declared `@mailbox`, and a process containing a `receive`
  must declare one: the channel a process listens on is what the compiled `inbox` stands for, so it
  is written down rather than read off whichever `receive` the walk reaches first. The mirror case
  is not an error — a `@mailbox` on a process with no `receive` is a warning, and the field is
  dropped, which is why this check returns the process rather than `Unit`. Between them the field
  becomes total on receiving processes: afterwards `p.mailbox` is `.some c` exactly when the process
  receives, and `c` is the channel it receives on.

  **A process *set* additionally has to index its channel by `self`.** `process (a \in Agents)`
  declares many instances at once, and one channel per *process text* is not one channel per
  *instance*: `receive(coord, m)` would give every instance the same FIFO, so the messages one
  instance drains into its own `inbox` are messages another instance was equally entitled to. The
  refinement invariant cannot even be stated there — the source FIFO would have to equal several
  instances' inboxes concatenated, with nothing fixing the order. `chan[self]` resolves to a
  different `ChanKey` per instance, which is what makes each instance's `inbox` account for exactly
  its own channel. A `=`-shaped process is a single instance and needs no such index.
-/

/-- Path-segment equality for a channel `Ref`'s `args`. Field segments compare as names, index
segments as whole expressions (`TypedTLAPlus.Expression` derives `BEq`) — syntactic equality, which
is what the pass's own name-based `.rx` dedup can see. Two indices that are equal only semantically
(`agt[self]` vs `agt[Id(self)]`) are reported as different channels; conservative in the safe
direction. -/
private def sameArg : (String ⊕ TypedPlusCal.Expression) → (String ⊕ TypedPlusCal.Expression) → Bool
  | .inl f₁, .inl f₂ => f₁ == f₂
  | .inr e₁, .inr e₂ => e₁ == e₂
  | _, _ => false

/-- The channel a process listens on, in the shape both a `@mailbox` annotation (`String × List
Expression`, index expressions only) and a `receive`'s channel `Ref` (`String × List (String ⊕
Expression)`, field or index segments) can be put into. -/
private abbrev ChannelRef := String × List (String ⊕ TypedPlusCal.Expression)

private def refChannel (c : TypedPlusCal.Ref) : ChannelRef := (c.name, c.args)

/-- Whether a channel reference is indexed by `self` somewhere in its path. `"self"` is the name
`Elaborator/PlusCal.lean` binds a process instance's own identity to, and a reference to it is an
ordinary `.var` by the time this pass runs. -/
private def indexedBySelf (c : ChannelRef) : Bool :=
  c.2.any λ | .inr (.var "self" _ _) => true | _ => false

private def mailboxChannel : String × List TypedPlusCal.Expression → ChannelRef
  | (name, es) => (name, es.map .inr)

/-- One process's receives, checked against `expected` — the process's declared `@mailbox`, or
`none` when it declared none, which a `receive` then rejects. The `StateT Bool` records whether a
`receive` was seen at all, which is what the caller needs to tell a used `@mailbox` from an unused
one; `expected` is a plain argument, since nothing installs one mid-walk any more. -/
private def checkOneReceive (process : String) (isProcessSet : Bool) (expected : Option ChannelRef)
    (s : TypedPlusCal.Statement false) (pos : SourceSpan) : StateT Bool m Unit :=
  match s with
  | .receive c _ _ => do
    let found := refChannel c
    if isProcessSet && !indexedBySelf found then
      throw (.mailboxNotIndexedBySelf pos process found.1)
    match expected with
    | none => throw (.receiveWithoutMailbox pos process found.1)
    | some expected =>
      set true
      if expected.1 == found.1 && List.isEqv expected.2 found.2 sameArg then pure ()
      else throw (.receiveChannelMismatch pos process expected.1 found.1
        (indicesDiffer := expected.1 == found.1))
  | _ => pure ()

/-- Every `receive` reachable in `p` — including those nested inside `if`/`while`/`either`/`with`
(`Statement.forEachNode`) — names `p`'s declared `@mailbox`, indexed by `self` when `p` is a process
set (`«=|∈» = false` is the `∈` case: `Parser_/PlusCal.lean` sets `true` for `=`).

Returns `p`, with its `mailbox` cleared when it declared one and no `receive` used it — the one
non-fatal outcome here, warned about and then normalized away rather than rejected. Position for
that warning is `p.id`'s own, the same one `WellFormedness/Declarations.lean`'s
`checkNoLocalChannels` points at: the annotation itself carries none of its own, and a bare
`@mailbox: ch;` has no index expression to borrow one from. -/
def TypedPlusCal.Process.checkReceiveChannels (p : TypedPlusCal.Process) : m TypedPlusCal.Process := do
  let expected := p.mailbox.map mailboxChannel
  let visit : ∀ {b}, TypedPlusCal.Statement b → StateT Bool m Unit :=
    λ {b} s ↦ match_source s with
      | s@(.receive ..), pos => checkOneReceive p.name (!p.«=|∈») expected s pos
      | _, _ => pure ()
  let go : StateT Bool m Unit :=
    ElaboratedPlusCal.Process.forStatements (λ {_} s ↦ ElaboratedPlusCal.Statement.forEachNode visit s) p
  let (_, received) ← go.run false
  match p.mailbox with
  | some (channel, _) =>
    if received then return p
    else do
      warn (.unusedMailbox (posOf p.id) p.name channel)
      return { p with mailbox := none }
  | none => return p

/-- `Process.checkReceiveChannels` over every process of `algo`, threading each rewritten process
back into the algorithm. Kept out of `Algorithm.checkRestrictions`'s shared walk: that walk's
`visitStatement` callback sees a statement with no record of which process it came from, and this
check is process-scoped by nature. -/
def TypedPlusCal.Algorithm.checkReceiveChannels (algo : TypedPlusCal.Algorithm) :
    m TypedPlusCal.Algorithm := do
  return { algo with processes := ← algo.processes.mapM TypedPlusCal.Process.checkReceiveChannels }

/-- Runs all the above checks over a whole algorithm, via the shared
`TypedPlusCal.Algorithm.walkReachable` (`WellFormedness/Reachability.lean`), supplying
`Statement.checkRefRestrictions`/`Expression.checkNode` as its two callbacks. `currentModule`/
`ownDecls` come from the enclosing `TypedModule` (`WellFormedness/WellFormedness.lean`) — this
pass alone doesn't have them, since it only receives the embedded `pcalAlgorithm`. The
`ReachabilityClosure` memoization is scoped to this one call — a private `StateT` layer, run from
`{}` and discarded (`.run'`) once this returns: whether an operator was already walked while
checking a previous module has no bearing on checking this one. -/
def TypedPlusCal.Algorithm.checkRestrictions [MonadForeignLookup m]
    (currentModule : String) (ownDecls : List Decl) (algo : TypedPlusCal.Algorithm) : m Unit :=
  let go : StateT ReachabilityClosure m Unit :=
    TypedPlusCal.Algorithm.walkReachable TypedPlusCal.Statement.checkRefRestrictions
      (TypedTLAPlus.Expression.checkNode currentModule ownDecls) currentModule ownDecls algo
  go.run' {}

end
