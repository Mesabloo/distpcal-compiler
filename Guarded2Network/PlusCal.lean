module

public import Guarded2Network.Errors
public import Core.NetworkPlusCal.Syntax
public import Core.ComputableTLAPlus.Coercion
public import Core.ComputableTLAPlus.Subst
public import Common.Fresh

public section

/-!
  `Guarded2Network` (§5.5): compiles a `receive` away entirely, replacing it with a real second
  kind of thread (`NetworkPlusCal.Thread.rx`) that loops draining a fresh process-local `inbox`
  sequence variable, and rewrites every later `await`/`with` guard that referenced the received
  value to read `inbox` instead — the guard's own truth no longer depends on an abstract "did a
  message arrive" primitive, only on ordinary sequence operations (`Head`/`Tail`/`Len`) over
  `inbox`. Design reference: `~/Documents/distpcal-compiler/Guarded2Network/PlusCal.lean` (139
  lines, reused as design, not code, per this project's convention) — differences from that prior
  art, beyond the fresh `GuardedPlusCal`/`NetworkPlusCal` ASTs (`Core/NetworkPlusCal/Syntax.lean`'s
  own module doc) themselves:

  - **Monad-polymorphic** (`INSTRUCTIONS.md`'s cross-cutting convention), not hardcoded against
    prior art's own concrete `Id`: generic `{m} [Monad m] [MonadFresh m] [MonadDiagnostic Empty
    G2NError m]` — `MonadDiagnostic`, not a bare `MonadExceptOf`, so the concrete instantiation
    pairs directly with `Fugue.lean`'s `runPassDiag` (the same `DiagT`-based calling convention
    every other diagnostics-producing pass already uses, `Elaborator.lean`'s `runChecker`/
    `Desugarer/TLAPlus.lean`'s `runDesugarer`). `Empty` (not a new bespoke warning type) for the
    warning channel — this pass has no warnings to report yet (`Common/Errors.lean`'s
    `CompilerDiagnostic Empty String` instance exists exactly for this case).
  - **Every fresh name — the process-local `inbox` variable and each `.rx` thread's own throwaway
    loop-local `var` — comes from `freshName` (`Common/Fresh.lean`), not prior art's string
    concatenation (`inbox ++ procName`) or bare counter-suffixed literal (`s!"rx_{i}"`)**. Same
    `$`-based hygiene argument as every other pass's fresh binder (`Common/Fresh.lean`'s own doc
    comment) — a name a real user could have written can never collide with one of these. `inbox`
    is fresh once per process (shared by every thread of that process, exactly like prior art's own
    `inbox ++ procName` was one name per process); each new `.rx` thread gets its own fresh `var`
    (prior art's `rxs'` triple's synthesized name existed for the same purpose, just less
    hygienically).
  - **A `receive`'s stored `Coercion` (`Core/TypedTLAPlus/Coercion.lean`, item 0) is discharged via
    `Coercion.applyComputable` directly against the built `Head(inbox)` expression**, not left
    unapplied — prior art's `receive` carried no coercion field at all, so this has no direct
    precedent there.
  - **Prior art's two `panic!` sites** ("channel has wrong type" / "channel not found") **become
    `G2NError.internalInvariantViolated`**. In fact only "not found" is reachable at all in this
    project's fresh design: `GuardedPlusCal.Declarations.channels`/`.fifos` already store a
    channel's checked *element* type directly (`Elaborator/PlusCal.lean`'s `checkChannelDecl`
    already unwraps `Channel(τ)`/`dom → Channel(τ)` down to `τ` before it ever reaches
    `Declarations`), so there is no wrapped `Typ` left to mismatch on by the time this pass runs —
    unlike prior art's own channel table, which stored the *unwrapped* Γ-binding type and so still
    had a "wrong shape" case to guard against.
  - **Guard-expression substitution reuses `ComputableTLAPlus.Expression.substRef`**
    (`Core/ComputableTLAPlus/Subst.lean`, already written for `Computable2Guarded/FlatReord.lean`'s
    own `𝒞_reord` case) in place of prior art's local `Ref.substOf` + manual `.replace` fold — same
    substitution primitive (bare `r` substitutes the name directly; a compound `r` substitutes the
    whole base variable with a one-entry `EXCEPT`), just already available rather than
    reimplemented. The **fold direction still matters and is unchanged from prior art**: each new
    `(Ref, Expr)` pair is appended to the end of `newInstrs` as its receive is processed, and a
    later guard's substitution is a **`foldr`** over that list — this makes a later-appended
    "advance `inbox` past what this receive consumed" pair get applied *before* an earlier-appended
    one during the fold (since `foldr` processes right-to-left), which is exactly what makes a
    second receive's freshly-substituted `Head(inbox)` get caught and advanced to `Head(Tail(inbox))`
    by the first receive's still-pending advance. Switching to `foldl` silently breaks this.
  - **No `Located`/position tracking anywhere**: this project's fresh `GuardedPlusCal.Statement`/
    `NetworkPlusCal.Statement` carry no position at all (`Core/NetworkPlusCal/Syntax.lean`'s module
    doc), so none of prior art's `posOf`/`@@`/`match_source` machinery has anything to port.

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
*element* type directly (see the module doc above for why no wrapped `Channel(_)`/`dom →
Channel(_)` shape ever needs matching here), built by merging global and process-local
`channels`/`fifos` declarations. Looked up by a `receive`'s channel `Ref`'s own base name, ignoring
any index arguments — a channel's element type doesn't depend on which array slot is referenced,
same as prior art's own by-name lookup. -/
abbrev Guarded2NetworkChans := List (String × ComputableTLAPlus.Typ)

private def declsChans (decls : ComputableGuardedPlusCal.Declarations) : Guarded2NetworkChans :=
  (decls.channels ++ decls.fifos).map λ (x, τ, _) ↦ (x, τ)

private def head (τ : ComputableTLAPlus.Typ) (e : ComputablePlusCal.Expression) : ComputablePlusCal.Expression :=
  .opCall (.var "Head" (.operator [.seq τ] τ) (.module "Sequences")) [e]

private def tail (τ : ComputableTLAPlus.Typ) (e : ComputablePlusCal.Expression) : ComputablePlusCal.Expression :=
  .opCall (.var "Tail" (.operator [.seq τ] (.seq τ)) (.module "Sequences")) [e]

/-- `Len(e) > n`, `n` a literal `Nat`. -/
private def lenGt (τ : ComputableTLAPlus.Typ) (e : ComputablePlusCal.Expression) (n : Nat) : ComputablePlusCal.Expression :=
  .opCall (.var ">" (.operator [.int, .int] .bool) (.module "Naturals"))
    [.opCall (.var "Len" (.operator [.seq τ] .int) (.module "Sequences")) [e], .nat (toString n)]

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty G2NError m]

/-- Walk one branch's precondition block (`none` for a branch with no guards at all), threading
substitution of every already-processed `receive` into later `await`/`with` guards — see the
module doc above for the `foldr`/fold-direction explanation. Returns the rewritten precondition
block; the physical consumption assignments (`ref := coe(Head(inbox)); inbox := Tail(inbox)` per
`receive`, in order) as plain action statements, meant to be prepended to the branch's action
block; and the list of `(channel, element type)` pairs this branch actually received from, in
order (`Thread.toNetwork` below decides, per distinct channel, whether a new `.rx` thread is
needed). -/
private def processPrecondition (chans : Guarded2NetworkChans) (inboxName : String) :
    Option (GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement true) false) →
      m (Option (GuardedPlusCal.Block (ComputableNetworkPlusCal.Statement true) false) ×
         List (ComputableNetworkPlusCal.Statement false false) ×
         List (ComputableGuardedPlusCal.Ref × ComputableTLAPlus.Typ))
  | none => pure (none, [], [])
  | some B => do
    let mut i : Nat := 0
    let mut newInstrs : List (ComputableGuardedPlusCal.Ref × ComputablePlusCal.Expression) := []
    let mut rxs : List (ComputableGuardedPlusCal.Ref × ComputableTLAPlus.Typ) := []
    let mut results : List (ComputableNetworkPlusCal.Statement true false) := []

    let substGuard (e : ComputablePlusCal.Expression) : ComputablePlusCal.Expression :=
      newInstrs.foldr (init := e) λ (r, rhs) e' ↦ ComputableTLAPlus.Expression.substRef r rhs e'

    for S in B.begin.concat B.last do
      let S' : ComputableNetworkPlusCal.Statement true false ← match S with
        | .with x ann bound e => pure <| .with x ann bound (substGuard e)
        | .await e => pure <| .await (substGuard e)
        | .receive c r coe =>
          match chans.lookup c.name with
          | none =>
            throw (.internalInvariantViolated SourceSpan.placeholder
              s!"receive's channel '{c.name}' does not resolve to any declared channel or fifo")
          | some τ =>
            let inboxVar : ComputablePlusCal.Expression := .var inboxName (.seq τ) .binder
            let inboxRef : ComputableGuardedPlusCal.Ref := { name := inboxName, args := [], baseType := .seq τ }
            newInstrs := newInstrs ++ [(r, coe.applyComputable (head τ inboxVar)), (inboxRef, tail τ inboxVar)]
            i := i + 1
            rxs := rxs.concat (c, τ)
            pure <| .await (lenGt τ inboxVar (i - 1))
      results := results.concat S'

    return (some { begin := results.dropLast, last := results.getLast! },
      newInstrs.map λ (r, e) ↦ .assign r e, rxs)

/-- Every action-class constructor `GuardedPlusCal.Statement`/`NetworkPlusCal.Statement` share
verbatim (all but `receive`, already compiled away above, and `with`, guard-class only) — `Ref`/
`MulticastFilter` are the exact same types under both pinnings (`Core/NetworkPlusCal/Syntax.lean`
reuses `GuardedPlusCal.Ref`/`.MulticastFilter` directly), so this is a plain re-tagging, not a
translation. -/
private def convertActionStmt {b} : ComputableGuardedPlusCal.Statement false b → ComputableNetworkPlusCal.Statement false b
  | .skip => .skip
  | .print e => .print e
  | .assert e => .assert e
  | .send c e => .send c e
  | .multicast c filter => .multicast c filter
  | .assign r e => .assign r e
  | .goto l => .goto l

private def convertActionBlock (B : GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement false) true) :
    GuardedPlusCal.Block (ComputableNetworkPlusCal.Statement false) true :=
  B.map (λ ⦃_⦄ ↦ convertActionStmt)

variable [MonadFresh m]

/-- One process's channel table (already merged with that process's own local `channels`/`fifos`
by `Process.toNetwork`) and its single shared `inbox` name (fresh once per process, shared by
every one of the process's threads — same sharing prior art's own `inbox ++ procName` had, just
hygienic) drive the whole compilation: every `AtomicBranch`'s precondition is walked
(`processPrecondition`), its action block gets the resulting consumption assignments prepended,
and a new `.rx` thread is added the first time this call encounters a not-yet-seen channel. -/
def ComputableGuardedPlusCal.Thread.toNetwork (chans : Guarded2NetworkChans) (inboxName : String)
    (T : ComputableGuardedPlusCal.Thread) :
    m (List (String × ComputableTLAPlus.Typ × Bool × Option (Bool × ComputablePlusCal.Expression)) ×
       List ComputableNetworkPlusCal.Thread × ComputableNetworkPlusCal.Thread) := do
  let mut newLocals : List (String × ComputableTLAPlus.Typ × Bool × Option (Bool × ComputablePlusCal.Expression)) := []
  let mut rxThreads : List ComputableNetworkPlusCal.Thread := []
  let mut blocks : List ComputableNetworkPlusCal.AtomicBlock := []

  for block in T do
    let mut branches' : List ComputableNetworkPlusCal.AtomicBranch := []

    for branch in block.branches do
      let (precond, newInstrStmts, rxs) ← processPrecondition chans inboxName branch.precondition
      let action := convertActionBlock branch.action

      if let (chan, τ) :: _ := rxs then
        if newLocals.isEmpty then
          newLocals := newLocals.concat (inboxName, .seq τ, false, some (true, .seq [] τ))
        unless rxThreads.any (λ | .rx c' .. => c'.name == chan.name | .code _ => false) do
          let rxVar ← freshName "rx"
          rxThreads := rxThreads.concat (.rx chan rxVar τ inboxName)

      branches' := branches'.concat { precondition := precond, action := { action with begin := newInstrStmts ++ action.begin } }

    blocks := blocks.concat { label := block.label, branches := branches' }

  return (newLocals, rxThreads, .code blocks)

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
  }

def ComputableGuardedPlusCal.Algorithm.toNetwork (algo : ComputableGuardedPlusCal.Algorithm) :
    m ComputableNetworkPlusCal.Algorithm := do
  let globalChans := declsChans algo.globalState
  return {
    isFair := algo.isFair, name := algo.name, globalState := algo.globalState
    processes := ← algo.processes.mapM (ComputableGuardedPlusCal.Process.toNetwork globalChans)
  }

end
