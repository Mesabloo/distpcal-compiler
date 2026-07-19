module

public import WellFormedness.Monad
import Elaborator.Declarations
import Core.TypedPlusCal.Syntax

public section

/-!
  The shared reachability walk: given a starting `TypedTLAPlus.Expression`, resolves every
  `.var name _ (.module m)` against `m`'s declaration list and, for anything with a body
  (`operator`/`function`), recurses into that body too, transitively, memoized so a declaration
  referenced from multiple places is walked once. Every visited `(module, name)` pair, with what
  it resolved to, accumulates into a `ReachabilityClosure` returned to the caller.

  Split out from `WellFormedness/Restrictions.lean` so `Typed2Computable` can reuse the same
  resolution/recursion/memoization machinery to collect "every constant/variable/operator/
  function reachable from the algorithm," without inheriting `Restrictions.lean`'s own
  error-throwing checks. `walkReachable`'s `visit` parameter is the seam: `Restrictions.lean`
  supplies its checks through it; a caller that only wants the closure supplies a no-op. Checks
  run once per node via `visit`, in the same pre-order the walk visits nodes (`visit`, then
  recurse into children).

  `TypedPlusCal.Statement.walkReachable`/`.Algorithm.walkReachable` below extend the same sharing
  to the statement-level traversal — which expression positions exist in a statement, and how
  they nest through `Block`/`Branches`. Two callbacks: `visitStatement` (a statement's own
  non-expression positions — `Restrictions.lean`'s Ref channel-likeness checks on `assign`'s
  LHS/`receive`'s destination) and `visitExpr` (forwarded into `Expression.walkReachable`).
  `Typed2Computable` supplies no-ops for both, wanting only the `ReachabilityClosure`;
  `Restrictions.lean` supplies its real checks for both, and wraps its own `StateT
  ReachabilityClosure` at its own call site — `Algorithm.walkReachable` leaves `.run` vs `.run'`
  to the caller, same as `Expression`/`Statement.walkReachable`.
-/

/-- What a name resolves to inside one module's declaration list, alongside the raw `Decl` itself
(needed by callers that do more than classify it — `Typed2Computable` re-emits referenced
constants/variables and translates referenced operator/function bodies). `assume` entries never
resolve — falls through to `none` in `Decl.resolve` below, same as "not found". -/
inductive ResolvedDecl : Type
  | «constant» (decl : Decl)
  | «variable» (decl : Decl)
  | operatorOrFunction (decl : Decl) (body : TypedPlusCal.Expression)

/-- Resolves `name` against one declaration `d` — `some` iff `d` is the `constants`/`variables`
entry that declares `name`, or the `operator`/`function` definition named `name`. -/
def Decl.resolve (name : String) : Decl → Option ResolvedDecl
  | d@(.constants xs) => if xs.any (·.1 == name) then some (.constant d) else none
  | d@(.variables xs) => if xs.any (·.1 == name) then some (.variable d) else none
  | .assume _ => none
  | d@(.operator _ f _ body) => if f == name then some (.operatorOrFunction d body) else none
  | d@(.function _ f _ body) => if f == name then some (.operatorOrFunction d body) else none

/-- Resolves `name` against `targetModule`'s own declaration list — `currentModule`'s own
`ownDecls` (already in hand, no lookup) if `targetModule` is the module currently being walked,
else `lookupForeign targetModule`'s (`WellFormedness/Monad.lean`). `none` if `targetModule` can't
be found at all (should be unreachable — a name only carries `origin := .module m` because `m`
already type-checked it) or `name` isn't in its list (an `ASSUME` entry, or genuinely absent). -/
def resolveInModule {m' : Type → Type} [Monad m'] [MonadForeignLookup m']
    (currentModule : String) (ownDecls : List Decl) (targetModule name : String) : m' (Option ResolvedDecl) := do
  let decls ← if targetModule == currentModule then pure ownDecls
    else match ← lookupForeign targetModule with
      | some tm => pure (tm.declarations₁ ++ tm.declarations₂)
      | none => pure []
  return decls.findSome? (Decl.resolve name)

/-- Every `(module, name)` pair the walk has resolved so far, alongside what it resolved to. -/
abbrev ReachabilityClosure := Std.HashMap (String × String) ResolvedDecl

/-- The shared walk. Visits `e` and everything structurally reachable from it — every `opCall`'s
function/arguments, every quantifier's domain/body, etc. — calling `visit path` once per node
before recursing into its children (`path`, innermost first, grows only when the walk recurses
into a resolved declaration's body — the breadcrumb `Restrictions.lean`'s error messages report
"reached via" through).

Whenever a node is `.var name _ (.module m)`, resolves `(m, name)` and, the first time this pair
is seen (`ReachabilityClosure`-memoized, guarding against looping on a self-recursive `function`
— `operator`s never self-recurse, per `Elaborator/Declarations.lean` — so only `function` bodies
can cycle), records the resolution and, if it resolved to an `operator`/`function`, recurses into
its body too (`path` extended by `name`). A `constant`/`variable` resolution is recorded but never
recursed into. Resolutions after the first for an already-visited pair are no-ops for recursion —
`visit` still runs on every node regardless, since some checks are per-reference, not
per-declaration. -/
partial def TypedTLAPlus.Expression.walkReachable {m' : Type → Type} [Monad m']
    [MonadForeignLookup m'] [MonadStateOf ReachabilityClosure m']
    (visit : List String → TypedPlusCal.Expression → m' Unit)
    (currentModule : String) (ownDecls : List Decl) (path : List String)
    (e : TypedPlusCal.Expression) : m' Unit := do
  visit path e
  let recurse := TypedTLAPlus.Expression.walkReachable visit currentModule ownDecls path
  match e with
  | .var name _ origin =>
    match origin with
    | .binder | .intrinsic => pure ()
    | .module m => do
      match ← resolveInModule currentModule ownDecls m name with
      | some resolved => do
        let visited ← getThe ReachabilityClosure
        unless visited.contains (m, name) do
          modifyThe ReachabilityClosure (·.insert (m, name) resolved)
          match resolved with
          | .operatorOrFunction _ body =>
            TypedTLAPlus.Expression.walkReachable visit m ownDecls (path ++ [name]) body
          | _ => pure ()
      | none => pure ()
  | .opCall f args => do recurse f; args.forM recurse
  | .forall _ _ dom body => do dom.forM recurse; recurse body
  | .exists _ _ dom body => do dom.forM recurse; recurse body
  | .fforall .. => pure ()
  | .eexists .. => pure ()
  | .choose _ _ dom body => do dom.forM recurse; recurse body
  | .set es _ => es.forM recurse
  | .collect _ _ dom body => do recurse dom; recurse body
  | .map' body _ _ _ dom => do recurse body; recurse dom
  | .fnCall f _ idx => do recurse f; recurse idx
  | .fn _ _ _ dom body => do recurse dom; recurse body
  | .fnSet dom cod => do recurse dom; recurse cod
  | .record fs => fs.forM λ (_, _, e) ↦ recurse e
  | .recordSet fs => fs.forM λ (_, _, e) ↦ recurse e
  | .except e _ upds => do
    recurse e
    upds.forM λ (path', newVal) ↦ do
      path'.forM λ
        | .inl _ => pure ()
        | .inr idx => recurse idx
      recurse newVal
  | .recordAccess e _ => recurse e
  | .tuple es => es.forM λ (_, e) ↦ recurse e
  | .seq es _ => es.forM recurse
  | .if c t f _ => do recurse c; recurse t; recurse f
  | .case branches other _ => do
    branches.forM λ (p, e) ↦ do recurse p; recurse e
    other.forM recurse
  | .nat _ | .str _ | .true | .false => pure ()
  | .stutter .. => pure ()
  -- Unreachable in practice (every `mvar` is substituted away before the checker's output is
  -- ever handed to a caller) — recurse defensively rather than special-case an impossible input.
  | .mvar _ e => recurse e

/-- Visits every statement in `s`'s tree — `visitStatement` once per statement, before recursing
into substructure — and threads every expression position (`print`'s `e`, `assign`'s per-pair
`e`, every `Ref.args`, …) through `Expression.walkReachable` via `visitExpr`, always with a fresh
`[]` path (`path` only grows inside one expression's own walk, when it recurses into a resolved
declaration's body).

`send`'s/`receive`'s channel-argument `Ref` (`c`) and any non-channel `Ref` position (`assign`'s
LHS, `receive`'s destination `r`) are treated identically here — walking `args`, nothing else;
`Restrictions.lean`'s asymmetric channel-likeness check between the two lives entirely in its own
`visitStatement`, which sees the raw `Statement` and can tell them apart.

`partial`: recursion isn't visibly decreasing to Lean through the mutual `Block`/`Branches`
nesting. -/
partial def TypedPlusCal.Statement.walkReachable {b : Bool} {m' : Type → Type} [Monad m']
    [MonadForeignLookup m'] [MonadStateOf ReachabilityClosure m']
    (visitStatement : ∀ {b}, TypedPlusCal.Statement b → m' Unit)
    (visitExpr : List String → TypedPlusCal.Expression → m' Unit)
    (currentModule : String) (ownDecls : List Decl)
    (s : TypedPlusCal.Statement b) : m' Unit := do
  visitStatement s
  let walkExpr (e : TypedPlusCal.Expression) : m' Unit :=
    TypedTLAPlus.Expression.walkReachable visitExpr currentModule ownDecls [] e
  let walkRefArgs (r : TypedPlusCal.Ref) : m' Unit := r.args.forM λ
    | .inl _ => pure ()
    | .inr e => walkExpr e
  let recurse : ∀ {b}, TypedPlusCal.Statement b → m' Unit :=
    TypedPlusCal.Statement.walkReachable visitStatement visitExpr currentModule ownDecls
  match s with
  | .goto _ | .skip => pure ()
  | .print e => walkExpr e
  | .assign asss => asss.forM λ (r, e) ↦ do walkRefArgs r; walkExpr e
  | .if cond B₁ B₂ => do
    walkExpr cond
    ElaboratedPlusCal.Block.forStatements recurse B₁
    ElaboratedPlusCal.Block.forStatements recurse B₂
  | .await e => walkExpr e
  | .with _ _ _ val B => do
    walkExpr val
    ElaboratedPlusCal.Block.forStatements recurse B
  | .assert e => walkExpr e
  | .either branches => ElaboratedPlusCal.Branches.forStatements recurse branches
  | .while cond B => do
    walkExpr cond
    ElaboratedPlusCal.Block.forStatements recurse B
  | .receive c r _ => do walkRefArgs c; walkRefArgs r
  | .send c e => do walkRefArgs c; walkExpr e
  | .multicast _ filter => do
    filter.binds.forM λ (_, _, _, e) ↦ walkExpr e
    walkExpr filter.val

/-- Walks every expression embedded in `d` — every `variables` entry's initializer, every
`channels`/`fifos` entry's index-type expressions. `Declarations` has no further substructure to
recurse into. Widened to cover this after `Typed2Computable` was found silently dropping a
`CONSTANTS`/`VARIABLES` entry referenced only from a process's own `id`/`Declarations` and never
from a statement body — the same root cause left a banned construct hiding in such positions
unchecked by `Restrictions.lean` too. -/
def TypedPlusCal.Declarations.walkReachable {m' : Type → Type} [Monad m']
    [MonadForeignLookup m'] [MonadStateOf ReachabilityClosure m']
    (visitExpr : List String → TypedPlusCal.Expression → m' Unit)
    (currentModule : String) (ownDecls : List Decl)
    (d : TypedPlusCal.Declarations) : m' Unit :=
  let walkExpr (e : TypedPlusCal.Expression) : m' Unit :=
    TypedTLAPlus.Expression.walkReachable visitExpr currentModule ownDecls [] e
  do
    d.variables.forM λ (_, _, _, init) ↦ init.forM λ (_, e) ↦ walkExpr e
    d.channels.forM λ (_, _, es) ↦ es.forM walkExpr
    d.fifos.forM λ (_, _, es) ↦ es.forM walkExpr

/-- Walks every expression reachable from `algo` — every statement (via `Statement
.walkReachable`), every process's own `id`/`mailbox` index expressions, and both `globalState`'s
and every process's own `localState`'s embedded expressions (`Declarations.walkReachable` above).
Doesn't wrap its own `ReachabilityClosure` `StateT` layer: callers choose `.run` (keep the closure
— `Typed2Computable`'s use) or `.run'` (discard — `Restrictions.lean`'s use), same choice
`Expression`/`Statement.walkReachable` leave open. -/
def TypedPlusCal.Algorithm.walkReachable {m' : Type → Type} [Monad m']
    [MonadForeignLookup m'] [MonadStateOf ReachabilityClosure m']
    (visitStatement : ∀ {b}, TypedPlusCal.Statement b → m' Unit)
    (visitExpr : List String → TypedPlusCal.Expression → m' Unit)
    (currentModule : String) (ownDecls : List Decl)
    (algo : TypedPlusCal.Algorithm) : m' Unit := do
  let walkExpr (e : TypedPlusCal.Expression) : m' Unit :=
    TypedTLAPlus.Expression.walkReachable visitExpr currentModule ownDecls [] e
  TypedPlusCal.Declarations.walkReachable visitExpr currentModule ownDecls algo.globalState
  for p in algo.processes do
    walkExpr p.id
    p.mailbox.forM λ (_, es) ↦ es.forM walkExpr
    TypedPlusCal.Declarations.walkReachable visitExpr currentModule ownDecls p.localState
    for thread in p.threads do
      for (_, blk) in thread do
        ElaboratedPlusCal.Block.forStatements
          (TypedPlusCal.Statement.walkReachable visitStatement visitExpr currentModule ownDecls) blk

end
