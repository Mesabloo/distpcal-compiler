module

public import Network2Go.Naming
public import Core.NetworkPlusCal.Syntax
public import Common.Fresh

public section

/-!
  Lock inference (thesis §7.1.2, Definition 7.1.3) — deciding which process-local variables share
  a lock, in what order the locks are acquired, and which of them can be dropped.

  This module is pure analysis: it answers in variable names and lock groupings, and emits no Go.
  `Network2Go/PlusCal.lean` reads the answer and writes the `Lock[struct{…}]` parameters,
  `MkLock` initializers and `Acquire`/`Release` calls from it. Keeping the two apart is what lets
  the inference be checked against the thesis's own worked examples without a Go backend in the
  way.

  **Why locks at all.** A process's threads run as goroutines over shared process-local state, and
  an atomic block must observe that state as one indivisible step. Go offers no atomicity, so
  §7.1 recovers it with locks — and then the whole question is how *few* locks suffice, since one
  global lock per process would serialize threads that never touch the same variable.

  **The scheme, from [HFP06] by way of §7.1.2.** `shared` is the set of process-local variables a
  piece of code reads or writes. A variable `x` *dominates* `y` (`x ⪰ y`) when every footprint
  containing `y` also contains `x`; then `y` can be guarded by `x`'s lock at no cost in
  concurrency, because everything that had to lock `y` was going to lock `x` anyway. Merging along
  strict domination (Definition 7.1.3) collapses the one-lock-per-variable assignment down without
  ever forcing two independent pieces of code to serialize — [HFP06, Lemma 2], which is the
  property that makes this worth doing rather than just locking everything.

  Three things are decided here that the thesis leaves open, and one that it declines to do:

  - **Footprints are per branch**, where Definition 7.1.2 states them per atomic block. The branch
    is what executes atomically; the block only chooses among branches, and §7.2.3.1 acquires per
    branch for that reason (Remark 7.2.4). See `processFootprints` for why the block-level reading
    serializes exactly the branches that remark wants concurrent.
  - **`self` is never locked.** §7.1.2 excludes it explicitly as read-only. Nothing special is
    needed for that here: `self` is bound by `Elaborator/PlusCal.lean`'s `checkProcess` rather
    than declared in `localState.variables`, and only declared variables are considered, so it
    drops out of every footprint on its own.
  - **A receiving thread has a footprint of its own, over its `inbox`.** `Thread.rx` has no label,
    no branches and no statements, but it does write the `inbox` sequence, concurrently with the
    code threads that drain it — and the whole reason `Guarded2Network` introduced `inbox` is that
    two threads share it. Leaving it out does not break correctness (the receiving thread still
    acquires whatever lock holds `inbox`) but it merges away the concurrency: in Ping-Pong's
    `Ping`, without it every footprint containing `inbox` also contains `tmp1`, so `tmp1 ≻ inbox`
    and the two share a lock — and the receiving thread then blocks a `send` that touches only
    `tmp1`. It is also what makes §7.3's `inbox_Pong ≻ tmp2` strict rather than mutual.
  - **Thread-confinement pruning is *not* implemented**, and the reason is stronger than the
    "for simplicity" §7.1.2 gives. A lock touched from only one thread does guard nothing —
    Network PlusCal runs at most one block of a given thread at a time, so its blocks are already
    mutually exclusive — but in this compilation scheme a lock is not only a mutex, it is the
    variable's *storage*: §7.2.3.1's branch functions read their variables out of the struct a
    lock carries, and `INIT_LOCKS` is the only place a variable's initial value is ever written.
    Dropping a lock therefore leaves its variables with nowhere to live. Pruning would need
    thread-confined variables to become goroutine-local state instead, which the compilation
    shape rules out: each atomic block is its own top-level function, so it cannot mutate a
    local of the thread function that started the chain. Worth revisiting only together with
    that, and it was implemented and reverted here once already.

  Verified by hand against Examples 7.1.1, 7.1.4 and 7.1.5, against §7.3's Ping-Pong compilation,
  and against Two-Phase Commit.
-/

namespace Network2Go

open ComputableTLAPlus (Typ)
open NetworkPlusCal (Statement AtomicBranch AtomicBlock Thread Process)
open GuardedPlusCal (Block)

/-! ## Variable sets

  Ordered lists rather than `HashSet`s. Order is not incidental here — it becomes the locking
  order, and through that the order of `Acquire` calls in generated code — so the analysis has to
  be deterministic down to the sequence, not just the set. -/

/-- Append `x` unless it is already present, keeping first-occurrence order. -/
private def insertVar (xs : List String) (x : String) : List String :=
  if xs.contains x then xs else xs ++ [x]

/-- `xs ∪ ys`, keeping `xs`'s order and appending what `ys` adds in its own order. -/
private def unionVars (xs ys : List String) : List String := ys.foldl insertVar xs

/-! ## Free variables -/

/--
  The free variables of a TLA⁺ expression, in first-occurrence order, ignoring anything in
  `bound`.

  Only `Origin.binder` references count. A process-local variable is introduced by
  `Elaborator/Context.lean`'s `extend`/`extendAll`, which tag every binding they make `.binder`,
  so a `.module` reference is a module-level definition and a `.intrinsic` one a builtin — neither
  is process state, and neither can be locked. This is the same discriminator
  `Network2Go/Definition.lean`'s `mentionsSelf` keys on, for the same reason: it is exact, so no
  scope walk is needed to tell the two apart.

  Quantifier and function-literal binders shadow, and are removed from their body's result only —
  a domain expression is evaluated outside its own binder (`[x ∈ D ↦ e]` may not mention `x` in
  `D`), so `bound` grows for `e` and not for `D`.
-/
partial def exprFreeVars (bound : List String) : ComputablePlusCal.Expression → List String
  | .var x _ .binder => if bound.contains x then [] else [x]
  | .var .. | .nat _ | .str _ | .true | .false => []
  | .opCall f args => args.foldl (λ acc e ↦ unionVars acc (exprFreeVars bound e)) (exprFreeVars bound f)
  | .forall x _ dom e | .exists x _ dom e | .choose x _ dom e | .collect x _ dom e =>
    unionVars (exprFreeVars bound dom) (exprFreeVars (insertVar bound x) e)
  | .map' e x _ _ dom => unionVars (exprFreeVars bound dom) (exprFreeVars (insertVar bound x) e)
  | .fn x _ _ dom e => unionVars (exprFreeVars bound dom) (exprFreeVars (insertVar bound x) e)
  | .set es _ | .seq es _ => es.foldl (λ acc e ↦ unionVars acc (exprFreeVars bound e)) []
  | .fnCall f _ i => unionVars (exprFreeVars bound f) (exprFreeVars bound i)
  | .record fs => fs.foldl (λ acc (_, _, e) ↦ unionVars acc (exprFreeVars bound e)) []
  | .tuple es => es.foldl (λ acc (_, e) ↦ unionVars acc (exprFreeVars bound e)) []
  | .recordAccess r _ => exprFreeVars bound r
  | .except f _ upds =>
    upds.foldl (init := exprFreeVars bound f) λ acc (path, rhs) ↦
      path.foldl (init := unionVars acc (exprFreeVars bound rhs)) λ acc' seg ↦
        match seg with
        | .inl _ => acc'
        | .inr i => unionVars acc' (exprFreeVars bound i)
  | .if c t f _ =>
    unionVars (unionVars (exprFreeVars bound c) (exprFreeVars bound t)) (exprFreeVars bound f)
  | .case arms other _ =>
    let acc := arms.foldl (init := []) λ acc (p, b) ↦
      unionVars (unionVars acc (exprFreeVars bound p)) (exprFreeVars bound b)
    other.elim acc (unionVars acc <| exprFreeVars bound ·)

/-- The variables a reference *reads*: those occurring in its bracket-index expressions. The base
name itself is not read — `x[i] := e` writes `x` and reads `i`, and a field segment reads
nothing. -/
private def refReads (bound : List String) (r : ComputableNetworkPlusCal.Ref) : List String :=
  r.args.foldl (init := []) λ acc seg ↦
    match seg with
    | .inl _ => acc
    | .inr e => unionVars acc (exprFreeVars bound e)

/-! ## Footprints -/

/-- `shared`'s accumulator as it walks a branch left to right: what has been touched so far, and
which names a `with` has bound since. Separate fields because a `with`-bound name must be
subtracted from *later* statements only — it is a temporary, and §7.1.2 removes it from the
footprint, but a process variable of the same name read *before* the `with` was still read. -/
private structure Footprint where
  shared : List String
  bound : List String

/-- One statement's contribution. `send`'s channel is not a footprint entry: a channel is not
process state, so only its index expressions and payload are read. `multicast`'s filter binds its
own names, scoped left to right and over the value. -/
private def stepStatement {b b'} (f : Footprint) :
    ComputableNetworkPlusCal.Statement b b' → Footprint
  | .skip | .goto _ => f
  | .await e | .print e | .assert e => { f with shared := unionVars f.shared (exprFreeVars f.bound e) }
  | .with name _ _ e =>
    { shared := unionVars f.shared (exprFreeVars f.bound e), bound := insertVar f.bound name }
  | .send c e =>
    { f with shared := unionVars (unionVars f.shared (refReads f.bound c)) (exprFreeVars f.bound e) }
  | .assign r e =>
    { f with shared :=
        unionVars (unionVars (insertVar f.shared r.name) (refReads f.bound r)) (exprFreeVars f.bound e) }
  | .multicast _ filter =>
    let inner := filter.binds.foldl (init := f) λ acc (name, _, _, e) ↦
      { shared := unionVars acc.shared (exprFreeVars acc.bound e), bound := insertVar acc.bound name }
    { f with shared := unionVars inner.shared (exprFreeVars inner.bound filter.val) }

/-- Every statement of a block, in order. -/
private def stepBlock {α : Bool → Type} {b}
    (step : ⦃c : Bool⦄ → Footprint → α c → Footprint) (f : Footprint) (B : Block α b) : Footprint :=
  step (B.begin.foldl (step (c := false)) f) B.last

/-- One branch's footprint. The precondition runs first and its `with` bindings stay in scope for
the action, which is why one `Footprint` is threaded through both rather than two being merged. -/
def branchShared (br : ComputableNetworkPlusCal.AtomicBranch) : List String :=
  let f : Footprint := { shared := [], bound := [] }
  let f := br.precondition.elim f (stepBlock (λ ⦃_⦄ ↦ stepStatement) f)
  (stepBlock (λ ⦃_⦄ ↦ stepStatement) f br.action).shared

/-- `shared(B)` for a whole atomic block: the union over its branches. A branch is one way the
block can fire, and the block's lock set has to cover every way. -/
def blockShared (B : ComputableNetworkPlusCal.AtomicBlock) : List String :=
  B.branches.foldl (λ acc br ↦ unionVars acc (branchShared br)) []

/--
  Every footprint of a process — one per **branch**, plus one per receiving thread — narrowed to
  the process's *declared* variables.

  **Per branch, not per block, and Definition 7.1.2 is stated over blocks.** The unit that
  executes atomically is the branch; a block only chooses among its branches, and §7.2.3.1
  acquires locks per branch for exactly that reason (Remark 7.2.4). Taking the block's footprint —
  the union over its branches — makes two branches that touch disjoint variables look like joint
  users of both, so those variables dominate each other, merge into one lock, and each branch then
  acquires a lock bundling the other's variables. That serializes precisely the pair Remark 7.2.4
  wants to keep concurrent. Branch footprints are the finer relation and merge strictly less;
  correctness is unaffected, since any assignment giving each variable exactly one lock is sound
  and every branch still acquires every lock covering what it touches.

  A `Thread.rx` contributes one footprint over its `inbox` although it has neither label nor
  branches — see the module doc for why leaving it out would be wrong.

  Narrowing here rather than inside `exprFreeVars` is what keeps `self`, quantifier binders and
  operator parameters out without naming any of them: none of the three is declared.
-/
def processFootprints (p : ComputableNetworkPlusCal.Process) : List (List String) :=
  let declared := p.localState.variables.map (·.1)
  let keep (xs : List String) := xs.filter declared.contains
  p.threads.flatMap λ t ↦
    match t with
    | .code blocks => blocks.flatMap λ B ↦ B.branches.map λ br ↦ keep (branchShared br)
    | .rx chan _ _ inbox => [keep (unionVars [inbox] (refReads [] chan))]

/-! ## Lock selection -/

/-- One inferred lock: a Go-side name and the variables it guards.

`vars` is in the process's declaration order, which fixes the field order of the `struct` the lock
holds — generated code projects those fields out after `Acquire` and reassembles them before
`Release`, so the order has to be stable across every site that names the lock. -/
structure Lock where
  name : String
  vars : List String
  deriving Repr, Inhabited

/-- A process's whole lock assignment: the locks in *locking order*, and which lock (if any) each
process-local variable is guarded by.

A variable missing from `ofVar` is one no lock protects — either nothing touches it, or its lock
was pruned as thread-confined. Reading or writing it needs no `Acquire` at all.

The set a given piece of code acquires is derived on demand through `acquiredBy` rather than
tabulated per block, because §7.2.3's Remark 7.2.4 acquires **per branch**, not per block: a block
whose two branches touch disjoint variables should let a concurrent block touching one of them run
while the other branch holds only its own. Blocks are still the unit the *inference* runs over —
`shared(B)` in Definition 7.1.2 is a block-level set — so the two granularities genuinely differ
and neither replaces the other.

Every generated function takes *all* the locks as parameters regardless (§7.2.3.1, Remark 7.2.1),
since a `goto` may hand control to a block with a different footprint. -/
structure ProcessLocks where
  locks : List Lock
  ofVar : List (String × Nat)
  deriving Repr, Inhabited

/-- The locks a piece of code touching `shared` must hold, as indices into `locks`, ascending.

Ascending is the whole point: acquiring in one fixed order everywhere is what rules out a
lock-ordering deadlock between two blocks that need the same pair. Callers acquire in list order
and may release in any. -/
def ProcessLocks.acquiredBy (ls : ProcessLocks) (shared : List String) : List Nat :=
  ls.locks.zipIdx.filterMap λ (l, i) ↦
    if shared.any l.vars.contains then some i else none

/-- `x ⪰ y` (Definition 7.1.2): every block whose footprint contains `y` also contains `x`. -/
private def dominates (fps : List (List String)) (x y : String) : Bool :=
  fps.all λ fp ↦ !fp.contains y || fp.contains x

/-- Definition 7.1.3, steps 1–2. Lock identities are represented by the variable that originally
owned them — `ℓ_x` is just `x` — so a merge is a rewrite of one identity to another and the final
distinct identities are the locks.

The thesis leaves both the iteration order and the choice among several dominators free ("in
whatever order", "we pick the first"). Both are fixed to declaration order here: the result is
insensitive to the choice in the sense that matters (any of them yields a valid assignment), but a
compiler that emitted a different lock grouping for the same input on different runs would be
untestable.

Mutual domination is why the merge rewrites *every* variable currently holding `ℓ_x` rather than
`x` alone. Two variables used in exactly the same blocks each strictly dominate the other; the
second iteration then finds nothing left pointing at the lock it would have redirected, and the
assignment is stable instead of oscillating. -/
private def selectLocks (fps : List (List String)) (vars : List String) : List (String × String) :=
  vars.foldl (init := vars.map λ x ↦ (x, x)) λ assign x ↦
    let lx := (assign.lookup x).getD x
    match vars.find? λ y ↦ y != x && dominates fps y x with
    | none => assign
    | some y =>
      let ly := (assign.lookup y).getD y
      assign.map λ (z, lz) ↦ (z, if lz == lx then ly else lz)

/--
  Definition 7.1.3 plus the pruning pass §7.1.2 leaves out, over footprints that have already been
  computed. `vars` is every lockable variable in declaration order.

  Split out from `inferLocks` because this half is exactly what the thesis's Examples 7.1.4 and
  7.1.5 state — they give footprints directly and say nothing about the code that produced them —
  so keeping it callable on a bare footprint list is what lets those be checked as written.
-/
def assignLocks {m : Type → Type} [Monad m] [MonadFresh m]
    (fps : List (List String)) (vars : List String) : m ProcessLocks := do
  let assign := selectLocks fps vars
  -- Distinct lock identities, ordered by the first variable that carries them: the locking order.
  let ids := vars.foldl (init := []) λ acc x ↦ insertVar acc ((assign.lookup x).getD x)
  let locks ← ids.mapM λ id ↦ do
    return { name := goIdent (← freshName "lock")
             vars := vars.filter λ x ↦ (assign.lookup x).getD x == id : Lock }
  let ofVar := locks.zipIdx.flatMap λ (l, i) ↦ l.vars.map (·, i)
  return { locks, ofVar }

/--
  The whole inference for one process: compute every block's footprint, then assign locks.

  A variable no block touches gets no lock at all — it is process-local state nothing races on.
-/
def inferLocks {m : Type → Type} [Monad m] [MonadFresh m]
    (p : ComputableNetworkPlusCal.Process) : m ProcessLocks :=
  let fps := processFootprints p
  -- Declaration order, restricted to what is actually touched somewhere.
  assignLocks fps ((p.localState.variables.map (·.1)).filter λ x ↦ fps.any (·.contains x))

end Network2Go

end
