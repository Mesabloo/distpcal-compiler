module

public import Network2Go.Definition
public import Network2Go.Locks

public section

/-!
  Compiling Network PlusCal processes into Go, on top of the TLA⁺ half
  (`Network2Go.{Typ,Expression,Definition}`) and the lock assignment (`Network2Go.Locks`).

  **The shape.** An atomic block does not become a Go block. Each of its branches becomes a
  top-level function returning `bool` — "did I fire" — and the block itself becomes a scheduler
  function looping over them, picking one at random per iteration and stopping once one returns
  `true`. Control then leaves through `goto`, which spawns a goroutine running the *next* block's
  scheduler rather than calling it: a chain of blocks is unbounded, and Go's goroutine stacks are
  small and growable, so a tail call would eventually overflow one.

  The loop is a busy-wait, and knowingly so: a failed iteration still
  pays for its lock acquisitions and its guard evaluation. Condition variables would avoid that
  and are much harder to state a correctness property about. Go's runtime also preempts on
  channel operations, which is exactly what `Acquire`/`Release` are, so the loop does not spin
  freely in practice.

  **Every function takes every lock**, whether it acquires it or not, because a `goto` may hand
  control to a block with a different footprint and the lock has to reach it.
  Which locks a piece of code *acquires* is decided per **branch**, not per block:
  two branches of one block touching disjoint variables should not serialize against each other.

  **Locks are storage, not just mutual exclusion.** A process-local variable exists only inside
  the struct its lock carries; a branch projects the variables out after `Acquire` and reassembles
  them before `Release`, and `INIT_LOCKS` in the process function is the only place an initial
  value is ever written. This is why `Network2Go.Locks` does not prune thread-confined locks.

  Four choices are this compiler's own:

  - **Names.** A readable scheduler name like `SndPi`, or a process function called `Pong`, collides
    with what a user-written definition of the same name compiles to — and `PingPongs.tla` really
    does have a process `Ping` beside a `CONSTANT Ping`. The synthesized names go through
    `Naming`'s `blockName`/`branchName`/`threadName`/`processName` instead.
  - **Assignment through a reference.** Compiling `r ≔ e` index by index would assume a TLA⁺
    function is a Go map. Here it is a `LazyFunction`, and a
    sequence is 1-indexed, so `x[i] := e` compiles the way `[x EXCEPT ![i] = e]` does — through
    `compileExcept`, which already knows all three cases (function, sequence, tuple).
  - **`LOCK`/`UNLOCK`** are `locks.Acquire`/`locks.Release` calls, not raw channel operations, so
    that `Lock[τ] = chan τ` stays inside the runtime library.
  - **`multicast`** compiles to a single `comm.Multicast` call. The iteration lives in the runtime
    library rather than in emitted code: the
    specification fixes no order on the sends, so there is nothing for a generated loop to say
    that the library cannot. The payload becomes a function literal from the recipient, which is
    why `ProcEnv` carries the channels' element types — Go infers a literal's parameter types
    from nothing, and demands its result type outright.
-/

namespace Network2Go

open ComputableTLAPlus (Typ)
open NetworkPlusCal (Statement AtomicBranch AtomicBlock Thread Process Algorithm)
open GuardedPlusCal (Block)

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty N2GError m] [MonadFresh m]

/-! ## Go fragments used throughout -/

/-- Go's unit type, `struct {}` — the element type of every `done` channel here. -/
def unitTyp : Go.Typ := .struct []

/-- `struct {}{}`, the sole value of `unitTyp`. -/
def unitVal : ComputableGo.Expression := .structLit unitTyp []

/-- `chan struct {}`. -/
def doneTyp : Go.Typ := .chan unitTyp

/-- Go's own `bool`, as opposed to the runtime's `tlaplus.Bool`. A branch's `guard` and a
scheduler's `shouldContinue` are Go booleans: they drive `if` and `for`, which the runtime type
cannot. -/
def goBoolTyp : Go.Typ := .named "bool" []

/-- `locks.f(e₁, …)`. -/
def locksCall (name : String) (args : List ComputableGo.Expression) : ComputableGo.Expression :=
  .call (locksVar name) args

/-! ## Per-process environment -/

/--
  Everything the compilation of one process's blocks needs to agree on: the names its generated
  functions bind, and the lock assignment they all share.

  `self` is *not* freshly named. A compiled expression mentioning `self` goes through
  `binderName`, so the parameter has to answer to exactly that; the elaborator binds `self` rather
  than declaring it, so no process-local variable can collide with it. `net` and `done` are
  fresh, since nothing in a compiled expression refers to them and a process variable named `net`
  is perfectly legal.
-/
structure ProcEnv where
  /-- The process's source-level name, which every synthesized function name is qualified by. -/
  proc : String
  locks : ProcessLocks
  /-- Declared process-local variables and their types, in declaration order. -/
  varTyps : List (String × Typ)
  /-- Every channel of the whole specification and the type it carries — the `Network` struct is
  algorithm-wide, so a process may `send`/`multicast` on one another process declared. Needed
  where a channel's element type cannot be read off the statement: `multicast`'s payload compiles
  to a function literal, and Go requires a literal to state its result type. -/
  chanTyps : List (String × Typ)
  net : String
  self : String
  done : String

/-- The `struct {x τ, …}` a lock carries: one field per variable it guards, in declaration order.

The field order is fixed by `Lock.vars` rather than sorted, unlike a compiled record type. Nothing
structural depends on it here — this type is written out at every site that mentions the lock, and
all of them get it from this function. -/
def lockStructTyp (env : ProcEnv) (l : Lock) : m Go.Typ := do
  let fields ← l.vars.mapM λ x ↦ do
    let some τ := env.varTyps.lookup x
      | throw (.internalInvariantViolated SourceSpan.placeholder
          s!"lock '{l.name}' guards '{x}', which is not a declared variable of process \
             '{env.proc}'")
    return (binderName x, ← compileTyp τ)
  return .struct fields

/-- The Go type of one lock: `locks.Lock[struct {x τ, …}]`. -/
def lockTyp (env : ProcEnv) (l : Lock) : m Go.Typ :=
  return locksTyp "Lock" [← lockStructTyp env l]

/-- The lock parameters every generated function takes, in locking order. -/
def lockParams (env : ProcEnv) : m (List (String × Go.Typ)) :=
  env.locks.locks.mapM λ l ↦ return (l.name, ← lockTyp env l)

/-- The lock arguments, matching `lockParams` position for position. -/
def lockArgs (env : ProcEnv) : List ComputableGo.Expression :=
  env.locks.locks.map λ l ↦ .var l.name

/-- The parameter list shared by branch, block-scheduler and thread functions:
`(ℓ₁, …, ℓₖ, net, self, done)`. -/
def commonParams (env : ProcEnv) : m (List (String × Go.Typ)) :=
  return (← lockParams env)
    ++ [(env.net, .named networkTypName []), (env.self, commTyp "Address"), (env.done, doneTyp)]

/-- The matching argument list. -/
def commonArgs (env : ProcEnv) : List ComputableGo.Expression :=
  lockArgs env ++ [.var env.net, .var env.self, .var env.done]

/-- `_ = f(args…)` — a call whose result is deliberately dropped. Every generated function returns
`struct {}` or `bool`, and Go rejects a bare call only for the sake of the value, so the blank
assignment is what makes `go { … }` around one legal. -/
def dropCall (f : String) (args : List ComputableGo.Expression) : ComputableGo.Statement :=
  .assign [.wildcard] [.call (.var f) args]

/-! ## Statements -/

/-- A branch's guards. `await` conjoins onto `guard`; `with x = e` introduces a real Go
variable, since later guards and the branch body both read it.

A `with` is evaluated even when `guard` is already `false` — Go has no lazy declaration — so an
expression that would panic on an undefined value can panic in a branch that was never going to
fire. The thesis's scheme has the same property; making it lazy would mean nesting the rest of
the branch inside the `if`, one level per `with`. -/
def compileGuard (guardVar : String) :
    ComputableNetworkPlusCal.Statement true false → m (List ComputableGo.Statement)
  | .await e => do
    return [.assign [.var guardVar]
      [.binary .and (.var guardVar) (goBool (← compileExprTop e))]]
  | s@(.with x ann isEq e) => do
    if !isEq then
      throw (.unsupported (posOf s) "with x ∈ S"
        "picking a value of S that satisfies the branch's remaining guards is a search, not a \
         computation — the thesis rejects the construct rather than deferring it")
    return [.var (binderName x) (← compileTyp ann), .assign [.var (binderName x)] [← compileExprTop e]]

/-- `net.C[e₁].Send(e₂)`, or `net.C.Send(e₂)` for a channel declared without an index. The channel
is a field of the `Network` struct named after it, so `send` needs no channel table — the
reference carries everything. -/
private def compileSend (env : ProcEnv) (pos : SourceSpan) (c : ComputableNetworkPlusCal.Ref)
    (e : ComputablePlusCal.Expression) : m ComputableGo.Statement := do
  let base : ComputableGo.Expression := .field (.var env.net) (fieldName c.name)
  let target : ComputableGo.Expression ← match c.args with
    | [] => pure base
    | [.inr i] => pure (.index base (← compileExprTop i))
    | [.inl f] =>
      throw (.internalInvariantViolated pos
        s!"send targets the field '{f}' of a channel, which type checking should have rejected")
    | _ =>
      throw (.unsupported pos s!"send on the channel '{c.name}'"
        "a channel indexed by more than one bracket group has no Network field shape to compile \
         against")
  return .expr (.call (.field target "Send") [← compileExprTop e])

/-- A branch's action statements. These run only once every guard has passed, so they
are emitted inside the branch's `if guard { … }`. -/
def compileAction (env : ProcEnv) {b} :
    ComputableNetworkPlusCal.Statement false b → m (List ComputableGo.Statement)
  | .skip => return []
  -- `tlaplus.Print`, not `Go.Statement.print`: that node prints through Go's builtin `println`,
  -- which accepts only basic types, and every TLA⁺ value is a defined type or a struct.
  | .print e => return [.expr (tlaplusCall "Print" [← compileExprTop e])]
  | s@(.assert e) => do
    -- Not `panic` on the negation directly: the runtime's `Bool` has to become a Go `bool` first.
    return [.if (.unary .not (goBool (← compileExprTop e)))
      [.panic (.str s!"Assertion violated at {posOf s}")] []]
  | s@(.assign r e) => do
    -- A bare `x := e` is a Go assignment; a path `x[i].f := e` rebuilds `x` the way `EXCEPT`
    -- does, since a TLA⁺ function is a lazy map rather than something Go can assign into.
    let lhs : ComputableGo.Ref := .var (binderName r.name)
    if r.args.isEmpty then
      return [.assign [lhs] [← compileExprTop e]]
    else
      return [.assign [lhs]
        [← compileExceptTop (posOf s) r.baseType (.var (binderName r.name)) r.args e]]
  | s@(.send c e) => return [← compileSend env (posOf s) c e]
  | s@(.multicast c filter) => do
    let some elemTy := env.chanTyps.lookup c
      | throw (.internalInvariantViolated (posOf s)
          s!"multicast targets '{c}', which is not a declared channel")
    -- The recipient's type is the channel's declared domain, and `Network`'s field for an indexed
    -- channel is a `map[comm.Address]`, so a tuple domain (a channel declared over more than one
    -- index group) has no field shape to index — the same limit `compileSend` runs into.
    let .address := filter.ann
      | throw (.unsupported (posOf s) s!"multicast on the channel '{c}'"
          "a channel indexed by more than one bracket group has no Network field shape to compile \
           against")
    return [.expr (.call (commVar "Multicast")
      [ .field (.var env.net) (fieldName c)
      , ← compileExprTop filter.set
      , .funcLit [(binderName filter.recipient, ← compileTyp filter.ann)] [← compileTyp elemTy]
          [.return [← compileExprTop filter.val [filter.recipient]]] ])]
  | .goto l =>
    -- `Done` is the sentinel `WellFormedness/Labelling.lean` reserves; it labels no block.
    pure <| if l == "Done" then
      [.send (.var env.done) unitVal]
    else
      [.go [dropCall (blockName env.proc l) (commonArgs env)]]

/-! ## Locks around a branch -/

/-- `st := Acquire(ℓ)` followed by one `var x τ; x = st.x` per variable the lock guards, so that
the branch body can name its variables directly. Returns the statements and the `st` name, which the
matching release needs. -/
private def acquireLock (env : ProcEnv) (l : Lock) : m (List ComputableGo.Statement × String) := do
  let st := goIdent (← freshName "st")
  let mut stmts : List ComputableGo.Statement :=
    [.var st (← lockStructTyp env l), .assign [.var st] [locksCall "Acquire" [.var l.name]]]
  for x in l.vars do
    let some τ := env.varTyps.lookup x
      | throw (.internalInvariantViolated SourceSpan.placeholder
          s!"lock '{l.name}' guards '{x}', which is not a declared variable")
    stmts := stmts ++
      [.var (binderName x) (← compileTyp τ),
       .assign [.var (binderName x)] [.field (.var st) (binderName x)]]
  return (stmts, st)

/-- `Release(ℓ, struct {…}{x, …})` — the struct rebuilt from the locals the branch has been
mutating. The lock carries the value, so releasing without writing back would discard the
branch's whole effect. -/
private def releaseLock (env : ProcEnv) (l : Lock) : m ComputableGo.Statement := do
  let fields ← l.vars.mapM λ x ↦ return (binderName x, (.var (binderName x) : ComputableGo.Expression))
  return .expr (locksCall "Release" [.var l.name, .structLit (← lockStructTyp env l) fields])

/-! ## Branches, blocks, threads, processes -/

/-- One branch of an atomic block, as its own `bool`-returning function.

The order is fixed by what depends on what: `guard` first, then the locks (a guard reads locked
variables), then the guards, then the body under `if guard`, then the releases, then `return
guard`. The releases sit outside the `if` because the locks were acquired outside it too. -/
def compileBranch (env : ProcEnv) (label : String) (i : Nat) (br : ComputableNetworkPlusCal.AtomicBranch) :
    m ComputableGo.Function := do
  let guardVar := goIdent (← freshName "guard")
  let acquired := env.locks.acquiredBy (branchShared br)
  let held := acquired.filterMap λ j ↦ env.locks.locks[j]?
  let mut body : List ComputableGo.Statement :=
    [.var guardVar goBoolTyp, .assign [.var guardVar] [.true]]
  let mut sts : List (Lock × String) := []
  for l in held do
    let (stmts, st) ← acquireLock env l
    body := body ++ stmts
    sts := sts ++ [(l, st)]
  for s in br.precondition.elim [] (λ B ↦ B.begin ++ [B.last]) do
    body := body ++ (← compileGuard guardVar s)
  let mut action : List ComputableGo.Statement := []
  for s in br.action.begin do
    action := action ++ (← compileAction env s)
  action := action ++ (← compileAction env br.action.last)
  body := body ++ [.if (.var guardVar) action []]
  for (l, _) in sts do
    body := body ++ [← releaseLock env l]
  return { name := branchName env.proc label i
           typeParams := [], params := ← commonParams env
           returnType := [goBoolTyp]
           body := body ++ [.return [.var guardVar]] }

/-- An atomic block: its branch functions, plus the scheduler that picks between them.

`shouldContinue = !branch(…)` is the whole protocol — a branch returns whether it fired, and the
loop stops exactly when one did. With a single branch the `switch` is redundant (`Rand(0, 1)` is
always `0`); the thesis emits it anyway and so does this, leaving the peephole to a later pass
rather than special-casing the shape here.

The `ToInt` around the switch head is load-bearing rather than cosmetic. `Rand` is typed over the
runtime's `Int`, which under the default arbitrary-precision build is a struct — an `Int`-valued
switch head could not match the integer-literal cases, and Go would reject the function. -/
def compileBlock (env : ProcEnv) (B : ComputableNetworkPlusCal.AtomicBlock) :
    m (List ComputableGo.Declaration) := do
  if B.branches.isEmpty then
    throw (.internalInvariantViolated SourceSpan.placeholder
      s!"atomic block '{B.label}' has no branches, which desugaring should have made impossible")
  let branches ← B.branches.zipIdx.mapM λ (br, i) ↦ compileBranch env B.label (i + 1) br
  let continueVar := goIdent (← freshName "loop")
  let cases := branches.zipIdx.map λ (F, i) ↦
    ({ head := .nat (toString i)
       body := [.assign [.var continueVar] [.unary .not (.call (.var F.name) (commonArgs env))]] } :
      ComputableGo.SwitchClause)
  let scheduler : ComputableGo.Function :=
    { name := blockName env.proc B.label
      typeParams := [], params := ← commonParams env
      returnType := [unitTyp]
      body :=
        [ .var continueVar goBoolTyp, .assign [.var continueVar] [.true],
          .for (.var continueVar)
            [.switch (tlaplusCall "ToInt"
                       [tlaplusCall "Rand"
                         [tlaplusCall "MkInt" [.nat "0"],
                          tlaplusCall "MkInt" [.nat (toString branches.length)]]])
                     cases []],
          .return [unitVal] ] }
  return (branches ++ [scheduler]).map .function

/-- A code thread: every block it contains, plus the function that starts the chain by calling the
first one. Everything after that first block happens through `goto`'s goroutines, so
this really is all a thread needs.

A thread with no blocks compiles to a function that does nothing. That is not a degenerate case to
reject: `@rx`-annotated threads are written `{}` in the source, and `Guarded2Network` turns them
into `Thread.rx` — but an ordinary empty thread is legal too, and denotes a process component that
terminates immediately. -/
def compileCodeThread (env : ProcEnv) (k : Nat) (blocks : List ComputableNetworkPlusCal.AtomicBlock) :
    m (List ComputableGo.Declaration) := do
  let blockDecls ← blocks.flatMapM (compileBlock env)
  let start := blocks.head?.elim [] λ B ↦ [dropCall (blockName env.proc B.label) (commonArgs env)]
  let thread : ComputableGo.Function :=
    { name := threadName env.proc k
      typeParams := [], params := ← commonParams env
      returnType := [unitTyp]
      body := start ++ [.return [unitVal]] }
  return blockDecls ++ [.function thread]

/-- A receiving thread: loop on `mailbox.Recv()`, and on each message that arrives,
acquire the lock holding `inbox` just long enough to append.

Locking only around the append is the point. `Recv` blocks — possibly forever, if no peer ever
sends — and a thread that held `inbox`'s lock across that call would freeze every block trying to
consume a message, including ones with nothing to consume. `ok` going false means the medium is
gone, which is how the loop terminates instead of blocking against a channel nobody will write to.

This thread takes `mailbox` in place of `done`: it never finishes on its own, so it has nothing to
signal. -/
def compileRxThread (env : ProcEnv) (k : Nat) (τ : Typ) (inbox : String) :
    m ComputableGo.Declaration := do
  let okVar := goIdent (← freshName "ok")
  let rxVar := goIdent (← freshName "rx")
  let stVar := goIdent (← freshName "st")
  let mailbox := goIdent (← freshName "mailbox")
  let goτ ← compileTyp τ
  let some j := env.locks.ofVar.lookup inbox
    | throw (.internalInvariantViolated SourceSpan.placeholder
        s!"the inbox '{inbox}' of process '{env.proc}' is guarded by no lock, but a receiving \
           thread writes it concurrently with the threads that drain it")
  let some l := env.locks.locks[j]?
    | throw (.internalInvariantViolated SourceSpan.placeholder s!"lock index {j} is out of range")
  let append : List ComputableGo.Statement :=
    [ .var stVar (← lockStructTyp env l), .assign [.var stVar] [locksCall "Acquire" [.var l.name]],
      .assign [.field (.var stVar) (binderName inbox)]
        [tlaplusCall "Append" [.field (.var stVar) (binderName inbox), .var rxVar]],
      ← releaseLockOf env l stVar ]
  return .function
    { name := rxThreadName env.proc k
      typeParams := []
      params := (← lockParams env)
        ++ [(env.net, .named networkTypName []), (mailbox, commTyp "Receiver" [goτ]),
            (env.self, commTyp "Address")]
      returnType := [unitTyp]
      body :=
        [ .var okVar goBoolTyp, .assign [.var okVar] [.true],
          .for (.var okVar)
            [ .var rxVar goτ,
              -- An ordinary two-valued assignment, not `Statement.receive`: `Recv` is a method on
              -- the `Receiver` interface, so what the medium is — a channel, a socket, a queue —
              -- stays the implementation's business.
              .assign [.var rxVar, .var okVar] [.call (.field (.var mailbox) "Recv") []],
              .if (.var okVar) append [] ],
          .return [unitVal] ] }
  where
    /-- `Release(ℓ, st)` — the receiving thread mutates the struct in place rather than projecting
    its fields out, so it writes the whole thing back unchanged apart from `inbox`. -/
    releaseLockOf (_env : ProcEnv) (l : Lock) (st : String) : m ComputableGo.Statement :=
      return .expr (locksCall "Release" [.var l.name, .var st])

/--
  Which non-`@parameter` variables need a Go local, in declaration order.

  Not all of them, and the answer is not "the ones in some lock" either. Lock inference narrows
  every footprint to the process's declared variables (`Network2Go/Locks.lean`), so a variable no
  branch touches lands in no lock, and a lock *is* a variable's storage — such a variable is
  emitted nowhere at all, and emitting a local for it anyway would be an unused local, which Go
  rejects.

  But a variable in no lock can still be *read*: by a later initializer (`variables x = 1, y = x
  + 1`, where only `y` is ever touched) or by a later `@parameter`'s bound (`variables limit = 10,
  @parameter start ∈ 1..limit`, where the assertion is `limit`'s only reader). Hence the backward
  pass — a variable is needed when it belongs to a lock, or when something later that *is* emitted
  names it. A `@parameter`'s bound always counts, since its assertion is always emitted; a
  dropped initializer's free variables do not.

  Scope makes one pass enough: an initializer may name only variables declared before it
  (`Elaborator/PlusCal.lean`'s `checkVariables` extends Γ per entry), so every read reaches
  backward and a right-to-left walk sees it before the declaration it refers to.
-/
private def localsNeeded (env : ProcEnv)
    (inits : List (String × Bool × Option (Bool × ComputablePlusCal.Expression))) : List String :=
  let locked := env.locks.locks.flatMap (·.vars)
  let step (acc : List String × List String)
      (entry : String × Bool × Option (Bool × ComputablePlusCal.Expression)) :
      List String × List String :=
    let (needed, reads) := acc
    let (x, isParam, init) := entry
    let initVars := init.elim [] λ (_, e) ↦ exprFreeVars [] e
    if isParam then (needed, reads ++ initVars)
    else if locked.contains x || reads.contains x then (x :: needed, reads ++ initVars)
    else (needed, reads)
  (inits.reverse.foldl step ([], [])).1

/--
  A process's initialization prologue: the declaration walk, then the initial lock values
  (`INIT_LOCKS`).

  **The walk is in declaration order, and interleaves two different things.** A `@parameter`
  emits no local — its value comes from the caller, as a parameter of the process function, so
  `binderName x` already names it — but its declared bound becomes an assertion. Every other
  variable emits a Go local: `Pick(S)` for an `∈` initializer, the compiled expression for `=`,
  and nothing for an uninitialized one, which leaves it at Go's zero value (the runtime types are
  built to accept theirs — `tlaplus.Int`'s reads as `0` rather than dereferencing a nil pointer).

  Interleaving rather than asserting everything up front is what lets a bound name an earlier
  local. Nothing forces the other order: a parameter is live from function entry, a local is
  computed from parameters and earlier locals, and an assertion computes nothing, so declaration
  order is both what PlusCal's sequential initializers already mean and the order that fires each
  assertion as early as it can — before an initializer that could panic on the very value the
  assertion is there to reject.

  **Locals come before locks because a lock is where the variable lives.** A process-local exists
  only inside its lock's struct, so an initializer naming an earlier sibling would otherwise
  compile to a Go identifier that does not exist; with the locals emitted first, each lock's
  struct is built by naming them.
-/
def initLocks (env : ProcEnv)
    (inits : List (String × Bool × Option (Bool × ComputablePlusCal.Expression))) :
    m (List ComputableGo.Statement) := do
  let needed := localsNeeded env inits
  let mut stmts : List ComputableGo.Statement := []
  for (x, isParam, init) in inits do
    let some τ := env.varTyps.lookup x
      | throw (.internalInvariantViolated SourceSpan.placeholder
          s!"'{x}' has an initializer in process '{env.proc}' but is not one of its declared \
             variables")
    if isParam then
      match init with
      | some (false, s) =>
        stmts := stmts ++
          [.if (.unary .not
                 (tlaplusCall "SetIn" [← ordDict τ, ← compileExprTop s, .var (binderName x)]))
             [.panic (.str s!"process {env.proc}: {x} is outside the set it was declared in")] []]
      | _ =>
        throw (.internalInvariantViolated SourceSpan.placeholder
          s!"'@parameter' variable '{x}' of process '{env.proc}' has no '∈' initializer, which \
             desugaring should have made impossible")
    else if needed.contains x then
      stmts := stmts ++ [.var (binderName x) (← compileTyp τ)]
      match init with
      | some (true, e) => stmts := stmts ++ [.assign [.var (binderName x)] [← compileExprTop e]]
      | some (false, s) =>
        stmts := stmts ++ [.assign [.var (binderName x)] [tlaplusCall "Pick" [← compileExprTop s]]]
      | none => pure ()
  for l in env.locks.locks do
    let τ ← match ← lockTyp env l with
      | .named _ [τ] => pure τ
      | τ => throw (.internalInvariantViolated SourceSpan.placeholder
               s!"lock type {repr τ} is not Lock[_]")
    let fields := l.vars.map λ x ↦
      (binderName x, (.var (binderName x) : ComputableGo.Expression))
    stmts := stmts ++
      [.var l.name (← lockTyp env l),
       .assign [.var l.name] [locksCall "MkLock" [.structLit τ fields]]]
  return stmts

/--
  A whole process: its threads' functions, and the function that starts them.

  The process function returns `done` immediately rather than blocking, so its caller decides when
  to wait. Each *code* thread signals the buffered `done'` when it reaches `goto Done`; a final
  goroutine reads `done'` once per code thread and only then signals the unbuffered `done`.
  Receiving threads never signal: they run until the medium vanishes, which is not the process
  finishing.

  `mailbox` is a parameter, not something the generated code constructs. The compiler emits no
  `main` and takes no position on how processes find each other — whoever assembles the system
  supplies a `Receiver` backed by a socket, a queue, or a Go channel.
-/
def compileProcess (chanTyps : List (String × Typ)) (p : ComputableNetworkPlusCal.Process) :
    m (List ComputableGo.Declaration) := do
  let locks ← inferLocks p
  let env : ProcEnv :=
    { proc := p.name, locks, chanTyps
      varTyps := p.localState.variables.map λ (x, τ, _, _) ↦ (x, τ)
      net := goIdent (← freshName "net")
      self := binderName "self"
      done := goIdent (← freshName "done") }
  let inits := p.localState.variables.map λ (x, _, isParam, init) ↦ (x, isParam, init)

  let mut decls : List ComputableGo.Declaration := []
  let mut starts : List ComputableGo.Statement := []
  let mut codeThreads := 0
  let donePrime := goIdent (← freshName "donep")
  let doneVar := goIdent (← freshName "done")
  let mailbox := goIdent (← freshName "mailbox")
  let mut mailboxτ : Option Go.Typ := none

  for (t, k) in p.threads.zipIdx do
    match t with
    | .code blocks =>
      decls := decls ++ (← compileCodeThread env k blocks)
      codeThreads := codeThreads + 1
      starts := starts ++
        [.go [dropCall (threadName env.proc k)
          (lockArgs env ++ [.var env.net, .var env.self, .var donePrime])]]
    | .rx _ _ τ inbox =>
      decls := decls ++ [← compileRxThread env k τ inbox]
      mailboxτ := some (← compileTyp τ)
      starts := starts ++
        [.go [dropCall (rxThreadName env.proc k)
          (lockArgs env ++ [.var env.net, .var mailbox, .var env.self])]]

  let aggregator : ComputableGo.Statement :=
    .go ((List.replicate codeThreads (.receive (.var donePrime) .wildcard none : ComputableGo.Statement))
      ++ [.send (.var doneVar) unitVal])
  -- `@parameter` variables are parameters of the process function, in declaration order and after
  -- everything the compiler supplies itself. This is API surface: whoever writes `main` passes
  -- them, so the compiler-supplied prefix stays in a fixed position rather than shifting with the
  -- number of parameters a process happens to declare.
  let paramVars ← (p.localState.variables.filter (·.2.2.1)).mapM λ (x, τ, _, _) ↦
    return (binderName x, ← compileTyp τ)
  let params : List (String × Go.Typ) :=
    [(env.net, .named networkTypName [])]
      ++ mailboxτ.elim [] (λ τ ↦ [(mailbox, commTyp "Receiver" [τ])])
      ++ [(env.self, commTyp "Address")]
      ++ paramVars
  let proc : ComputableGo.Function :=
    { name := processName p.name
      typeParams := [], params
      returnType := [doneTyp]
      body := (← initLocks env inits)
        ++ [ .make donePrime unitTyp (some (.nat (toString codeThreads))),
             .make doneVar unitTyp none ]
        ++ starts ++ [aggregator, .return [.var doneVar]] }
  return decls ++ [.function proc]

/-- Every channel and FIFO of the whole specification, algorithm-level and process-local alike, as
`(name, element type, index-domain expressions)`. Both the `Network` struct below and `ProcEnv`'s
own channel table are built from this one list — the struct is algorithm-wide, so a process may
name a channel another process declared. -/
def channelTyps (algo : ComputableNetworkPlusCal.Algorithm) :
    List (String × Typ × List ComputablePlusCal.Expression) :=
  (algo.globalState :: algo.processes.map (·.localState)).flatMap λ d ↦ d.channels ++ d.fifos

/-- The `Network` struct type: one field per channel of the whole specification, holding
the *sending* end only — a process reads from its own mailbox, which it is handed directly, and
never from the network at large.

A channel declared with an index domain (`pong[Pongs]`) becomes a `map[Address]Sender[τ]`, which
is what makes `net.c[e].Send(…)` resolve; one declared without becomes a plain `Sender[τ]`. -/
def networkTyp (algo : ComputableNetworkPlusCal.Algorithm) : m ComputableGo.Declaration := do
  let chans := channelTyps algo
  let fields ← chans.mapM λ (c, τ, idx) ↦ do
    let sender := commTyp "Sender" [← compileTyp τ]
    return (fieldName c, if idx.isEmpty then sender else .map (commTyp "Address") sender)
  return .typ networkTypName (.struct (fields.mergeSort λ (x, _) (y, _) ↦ x ≤ y))

end Network2Go

open Network2Go in
/-- A whole algorithm: the `Network` type, then every process.

Order is for readability only — Go resolves package-level declarations regardless of the order
they appear in.

Sits outside `namespace Network2Go` so that `algo.toGo` resolves by dot notation, matching
`Guarded2Network/PlusCal.lean`'s `guarded.toNetwork` — `Driver/Pipeline.lean` calls each pass that
way. -/
def ComputableNetworkPlusCal.Algorithm.toGo {m : Type → Type} [Monad m]
    [MonadDiagnostic Empty N2GError m] [MonadFresh m] (algo : ComputableNetworkPlusCal.Algorithm) :
    m (List ComputableGo.Declaration) := do
  let chanTyps := (channelTyps algo).map λ (c, τ, _) ↦ (c, τ)
  return (← networkTyp algo) :: (← algo.processes.flatMapM (compileProcess chanTyps))

end
