module

public import Guarded2Network.Errors
public import Core.NetworkPlusCal.Syntax
public import Core.ComputableTLAPlus.Coercion
public import Core.ComputableTLAPlus.Subst
public import Common.Fresh

public section

/-!
  `Guarded2Network` compiles a `receive` away entirely, replacing it with a real second kind of
  thread (`NetworkPlusCal.Thread.rx`) that loops draining a fresh process-local `inbox` sequence
  variable, and rewrites every later `await`/`with` guard that referenced the received value to
  read `inbox` instead — the guard's truth no longer depends on an abstract "did a message
  arrive" primitive, only on ordinary sequence operations (`Head`/`Tail`/`Len`) over `inbox`.

  - **Monad-polymorphic**: generic `{m} [Monad m] [MonadFresh m] [MonadDiagnostic Empty G2NError
    m]` — `MonadDiagnostic`, not a bare `MonadExceptOf`, so the concrete instantiation pairs
    directly with `Fugue.lean`'s `runPassDiag` (the same `DiagT`-based calling convention every
    other diagnostics-producing pass uses, `Elaborator.lean`'s `runChecker`/`Desugarer/
    TLAPlus.lean`'s `runDesugarer`). `Empty` for the warning channel, since this pass has no
    warnings to report yet (`Common/Errors.lean`'s `CompilerDiagnostic Empty String` instance
    exists exactly for this case).
  - **Every fresh name — the process-local `inbox` variable and each `.rx` thread's own block
    label — comes from `freshName` (`Common/Fresh.lean`)**, giving the same
    `$`-based hygiene as every other pass's fresh binder: a name a real user could have written
    can never collide with one of these. `inbox` is fresh once per process, shared by every
    thread of that process; each new `.rx` thread gets its own fresh label. That label is what the
    semantics schedules the receiving loop by, and what its own terminal `goto` targets
    (`reference/jlamp.pdf` §4.1); it must therefore stay distinct from every `AtomicBlock.label` in
    the process, which `freshName` guarantees.
  - **A `receive`'s stored `Coercion` (`Core/TypedTLAPlus/Coercion.lean`) is discharged via
    `Coercion.applyComputable` directly against the built `Head(inbox)` expression**, not left
    unapplied.
  - **Only `G2NError.internalInvariantViolated` guards a `receive`'s channel resolution** — and
    only "channel not found" is actually reachable: `GuardedPlusCal.Declarations.channels`/
    `.fifos` already store a channel's checked *element* type directly (`Elaborator/
    PlusCal.lean`'s `checkChannelDecl` unwraps `Channel(τ)`/`dom → Channel(τ)` down to `τ` before
    it reaches `Declarations`), so there's no wrapped `Typ` left to mismatch on by the time this
    pass runs.
  - **Guard-expression substitution reuses `ComputableTLAPlus.Expression.substRef`**
    (`Core/ComputableTLAPlus/Subst.lean`, already written for `Computable2Guarded/FlatReord.lean`'s
    own `𝒞_reord` case): bare `r` substitutes the name directly; a compound `r` substitutes the
    whole base variable with a one-entry `EXCEPT`. **Fold direction matters**: each new `(Ref,
    Expr)` pair is appended to the end of `newInstrs` as its receive is processed, and a later
    guard's substitution is a **`foldr`** over that list — a later-appended "advance `inbox` past
    what this receive consumed" pair applies *before* an earlier-appended one (since `foldr`
    processes right-to-left), which is what makes a second receive's freshly-substituted
    `Head(inbox)` get caught and advanced to `Head(Tail(inbox))` by the first receive's
    still-pending advance. Switching to `foldl` silently breaks this.
  - **Positions are carried across, not dropped**: every `NetworkPlusCal.Statement` this pass
    builds is registered (`@@`) at the `GuardedPlusCal.Statement` it replaces, and the
    consumption assignments a `receive` compiles into take that `receive`'s own span. Positions
    live in `Common/Position.lean`'s side map rather than in a field on the node, so this costs
    the AST nothing — but a node left unregistered is one `posOf` answers for with an unrelated
    node's span, which is why every construction site here has an `@@`.

  ```
  receive(c, x[0]);
  await x[0] + y = 0;
  receive(c, y);
  await x[0] + y = 0;
  ```
  compiles to (guards, symbolically, before any assignment runs):
  ```
  await Len(inbox) > 0;
  await [x EXCEPT ![0] = Head(inbox)][0] + y = 0;
  await Len(inbox) > 1;
  await [x EXCEPT ![0] = Head(inbox)][0] + Head(Tail(inbox)) = 0;
  ```
  and the branch's action block gains, as its own new prefix (ordinary sequential assignments — no
  substitution needed here, since each one's `Head(inbox)` is read *after* the previous one's own
  `inbox := Tail(inbox)` has already run):
  ```
  x[0] := Head(inbox); inbox := Tail(inbox); y := Head(inbox); inbox := Tail(inbox);
  ```
-/

/-- One process's channel/fifo element-type table — a channel name resolves to its already-checked
element type directly (see the module doc above for why no wrapped `Channel(_)`/`dom →
Channel(_)` shape ever needs matching here), built by merging global and process-local
`channels`/`fifos` declarations. Looked up by a `receive`'s channel `Ref`'s base name, ignoring any
index arguments — a channel's element type doesn't depend on which array slot is referenced. -/
abbrev Guarded2NetworkChans := List (String × ComputableTLAPlus.Typ)

private def declsChans (decls : ComputableGuardedPlusCal.Declarations) : Guarded2NetworkChans :=
  (decls.channels ++ decls.fifos).map λ (x, τ, _) ↦ (x, τ)

namespace Guarded2Network

/-! The three sequence expressions this pass builds over `inbox`. Public, and namespaced rather
than file-private, because the refinement proof has to state what they *mean* — `Guarded2Network/
Lemmas/Seq.lean`'s `SeqBuiltins` gives each one its evaluation law, and a law about a private
definition cannot be written at all. -/

/-- `Head(e)`. -/
def head (τ : ComputableTLAPlus.Typ) (e : ComputablePlusCal.Expression) : ComputablePlusCal.Expression :=
  .opCall (.var "Head" (.operator [.seq τ] τ) (.module "Sequences")) [e]

/-- `Tail(e)`. -/
def tail (τ : ComputableTLAPlus.Typ) (e : ComputablePlusCal.Expression) : ComputablePlusCal.Expression :=
  .opCall (.var "Tail" (.operator [.seq τ] (.seq τ)) (.module "Sequences")) [e]

/-- `Len(e) > n`, `n` a literal `Nat`. -/
def lenGt (τ : ComputableTLAPlus.Typ) (e : ComputablePlusCal.Expression) (n : Nat) : ComputablePlusCal.Expression :=
  .opCall (.var ">" (.operator [.int, .int] .bool) (.module "Naturals"))
    [.opCall (.var "Len" (.operator [.seq τ] .int) (.module "Sequences")) [e], .nat (toString n)]

end Guarded2Network

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty G2NError m]

/-- `processPrecondition`'s per-statement accumulator, threaded through `stepStatement` via a
local `StateT` layer (same "function-scoped `StateT`, `.run` at the end" shape
`WellFormedness/Restrictions.lean`'s `checkRestrictions` uses for its own memoization state)
rather than imperative `let mut` bindings. -/
private structure ReceiveState where
  i : Nat := 0
  /-- Each entry carries the span of the `receive` it was generated from, so the consumption
  assignment built from it in `processPrecondition` can be registered against real source text
  rather than a placeholder. -/
  newInstrs : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan) := []
  rxs : List (ComputableGuardedPlusCal.Ref × ComputableTLAPlus.Typ) := []

/-- Substitutes every `receive` processed so far (`newInstrs`) into a later guard `e` — see the
module doc's `foldr`/fold-direction explanation. The per-entry span plays no part in
substitution and is dropped here. -/
private def substGuard (newInstrs : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression × SourceSpan))
    (e : ComputablePlusCal.Expression) : ComputablePlusCal.Expression :=
  newInstrs.foldr (init := e) λ (r, rhs, _) e' ↦ ComputableTLAPlus.Expression.substRef r rhs e'

/-- One statement of `processPrecondition`'s walk — `ReceiveState.i`'s value before this step's
own increment is the count of receives already consumed prior to this one. -/
private def stepStatement (chans : Guarded2NetworkChans) (inboxName : String)
    (s : ComputableGuardedPlusCal.Statement true false) :
    StateT ReceiveState m (ComputableNetworkPlusCal.Statement true false) :=
  match_source s with
  | .with x ann bound e, pos => return .with x ann bound (substGuard (← get).newInstrs e) @@ pos
  | .await e, pos => return .await (substGuard (← get).newInstrs e) @@ pos
  | .receive c r coe, pos => do
    let st ← get
    match chans.lookup c.name with
    | none =>
      throw (.internalInvariantViolated pos
        s!"receive's channel '{c.name}' does not resolve to any declared channel or fifo")
    | some τ =>
      let inboxVar : ComputablePlusCal.Expression := .var inboxName (.seq τ) .binder @@ pos
      let inboxRef : ComputableGuardedPlusCal.Ref := { name := inboxName, args := [], baseType := .seq τ }
      set { st with
        i := st.i + 1
        newInstrs := st.newInstrs
          ++ [(r, coe.applyComputable (Guarded2Network.head τ inboxVar), pos), (inboxRef, Guarded2Network.tail τ inboxVar, pos)]
        rxs := st.rxs.concat (c, τ) }
      pure <| .await (Guarded2Network.lenGt τ inboxVar st.i) @@ pos

/-- Walk one branch's precondition block (`none` for a branch with no guards), threading
substitution of every already-processed `receive` into later `await`/`with` guards — see the
module doc's `foldr`/fold-direction explanation. Returns the rewritten precondition block; the
physical consumption assignments (`ref := coe(Head(inbox)); inbox := Tail(inbox)` per `receive`,
in order) as plain action statements to prepend to the branch's action block; and the list of
`(channel, element type)` pairs this branch received from, in order (`Thread.toNetwork` below
decides, per distinct channel, whether a new `.rx` thread is needed). -/
private def processPrecondition (chans : Guarded2NetworkChans) (inboxName : String) :
    Option (GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement true) false) →
      m (Option (GuardedPlusCal.Block (ComputableNetworkPlusCal.Statement true) false) ×
         List (ComputableNetworkPlusCal.Statement false false) ×
         List (ComputableGuardedPlusCal.Ref × ComputableTLAPlus.Typ))
  | none => pure (none, [], [])
  | some B => do
    let (results, st) ← ((B.begin.concat B.last).mapM (stepStatement chans inboxName)).run {}
    return (some { begin := results.dropLast, last := results.getLast! },
      st.newInstrs.map λ (r, e, pos) ↦ .assign r e @@ pos, st.rxs)

/-- Every action-class constructor `GuardedPlusCal.Statement`/`NetworkPlusCal.Statement` share
verbatim (all but `receive`, already compiled away above, and `with`, guard-class only) — `Ref`/
`Multicast` are the same types under both pinnings (`Core/NetworkPlusCal/Syntax.lean` reuses
`GuardedPlusCal.Ref`/`.Multicast` directly), so this is a plain re-tagging, not a
translation. -/
private def convertActionStmt {b} (s : ComputableGuardedPlusCal.Statement false b) :
    ComputableNetworkPlusCal.Statement false b :=
  match_source s with
  | .skip, pos => .skip @@ pos
  | .print e, pos => .print e @@ pos
  | .assert e, pos => .assert e @@ pos
  | .send c e, pos => .send c e @@ pos
  | .multicast c filter, pos => .multicast c filter @@ pos
  | .assign r e, pos => .assign r e @@ pos
  | .goto l, pos => .goto l @@ pos

private def convertActionBlock (B : GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement false) true) :
    GuardedPlusCal.Block (ComputableNetworkPlusCal.Statement false) true :=
  B.map (λ ⦃_⦄ ↦ convertActionStmt)

variable [MonadFresh m]

/-- `Thread.toNetwork`'s per-thread accumulator — `newLocals`/`rxThreads` are threaded state
across every block/branch of the thread; `blocks` itself needs no state slot, since it's just
`stepBlock`'s ordinary `mapM` result. -/
private structure ThreadState where
  newLocals : List (String × ComputableTLAPlus.Typ × Bool × Option (Bool × ComputablePlusCal.Expression)) := []
  rxThreads : List ComputableNetworkPlusCal.Thread := []

/-- One branch of one block — walks its precondition (`processPrecondition`), prepends the
resulting consumption assignments to its action block, and (the first time this call's thread
encounters a not-yet-seen channel) registers the shared `inbox` local and a new `.rx` thread for
that channel. -/
private def stepBranch (chans : Guarded2NetworkChans) (inboxName : String)
    (branch : ComputableGuardedPlusCal.AtomicBranch) : StateT ThreadState m ComputableNetworkPlusCal.AtomicBranch := do
  let (precond, newInstrStmts, rxs) ← (processPrecondition chans inboxName branch.precondition : m _)
  let action := convertActionBlock branch.action

  if let (chan, τ) :: _ := rxs then
    let st ← get
    let newLocals :=
      if st.newLocals.isEmpty then st.newLocals.concat (inboxName, .seq τ, false, some (true, .seq [] τ))
      else st.newLocals
    let rxThreads ←
      if st.rxThreads.any (λ | .rx c' .. => c'.name == chan.name | .code _ => false) then
        pure st.rxThreads
      else do
        let rxLabel ← (freshName "rx" : m String)
        pure (st.rxThreads.concat (.rx chan rxLabel τ inboxName))
    set ({ newLocals := newLocals, rxThreads := rxThreads } : ThreadState)

  return { precondition := precond, action := { action with begin := newInstrStmts ++ action.begin } }

private def stepBlock (chans : Guarded2NetworkChans) (inboxName : String)
    (block : ComputableGuardedPlusCal.AtomicBlock) : StateT ThreadState m ComputableNetworkPlusCal.AtomicBlock := do
  return { label := block.label, branches := ← block.branches.mapM (stepBranch chans inboxName) }

/-- One process's channel table (already merged with that process's own local `channels`/`fifos`
by `Process.toNetwork`) and its single shared `inbox` name (fresh once per process, shared by
every thread of the process) drive the whole compilation: every `AtomicBranch`'s precondition is
walked (`processPrecondition`), its action block gets the resulting consumption assignments
prepended, and a new `.rx` thread is added the first time this call encounters a not-yet-seen
channel. -/
def ComputableGuardedPlusCal.Thread.toNetwork (chans : Guarded2NetworkChans) (inboxName : String)
    (T : ComputableGuardedPlusCal.Thread) :
    m (List (String × ComputableTLAPlus.Typ × Bool × Option (Bool × ComputablePlusCal.Expression)) ×
       List ComputableNetworkPlusCal.Thread × ComputableNetworkPlusCal.Thread) := do
  let (blocks, st) ← (T.mapM (stepBlock chans inboxName)).run {}
  return (st.newLocals, st.rxThreads, .code blocks)

/-- First occurrence per name wins — a process's several original threads may each independently
propose the same single `(inboxName, ...)` local (every one of them shares that same fresh name,
`Thread.toNetwork`'s own doc above), which would otherwise duplicate the declaration once per
receiving thread. -/
private def dedupLocalsByName (entries : List (String × ComputableTLAPlus.Typ × Bool × Option (Bool × ComputablePlusCal.Expression))) :
    List (String × ComputableTLAPlus.Typ × Bool × Option (Bool × ComputablePlusCal.Expression)) :=
  entries.foldl (λ acc e ↦ if acc.any (·.1 == e.1) then acc else acc.concat e) []

def ComputableGuardedPlusCal.Process.toNetwork (globalChans : Guarded2NetworkChans)
    (p : ComputableGuardedPlusCal.Process) : m ComputableNetworkPlusCal.Process := do
  let inboxName ← freshName "inbox"
  let chans := globalChans ++ declsChans p.localState
  let results ← p.threads.mapM (ComputableGuardedPlusCal.Thread.toNetwork chans inboxName)
  let newLocals := dedupLocalsByName (results.flatMap (·.1))
  let rxThreads := results.flatMap (·.2.1)
  let codeThreads := results.map (·.2.2)
  return {
    mailbox := p.mailbox, isFair := p.isFair, name := p.name, «=|∈» := p.«=|∈», id := p.id
    localState := { p.localState with «variables» := p.localState.variables ++ newLocals }
    threads := rxThreads ++ codeThreads
  } @@ posOf p

def ComputableGuardedPlusCal.Algorithm.toNetwork (algo : ComputableGuardedPlusCal.Algorithm) :
    m ComputableNetworkPlusCal.Algorithm := do
  let globalChans := declsChans algo.globalState
  return {
    isFair := algo.isFair, name := algo.name, globalState := algo.globalState
    processes := ← algo.processes.mapM (ComputableGuardedPlusCal.Process.toNetwork globalChans)
  } @@ posOf algo

end
