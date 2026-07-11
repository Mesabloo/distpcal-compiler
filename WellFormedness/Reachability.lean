import WellFormedness.Monad
import Elaborator.Declarations
import Core.TypedPlusCal.Syntax

/-!
  The shared reachability walk: given a starting `TypedTLAPlus.Expression`, resolves every
  `.var name _ (.module m)` against `m`'s declaration list and — for anything with a body
  (`operator`/`function`) — recurses into that body too, transitively, memoized so a declaration
  referenced from multiple places is only walked once. Every visited `(module, name)` pair,
  alongside what it resolved to, accumulates into a `ReachabilityClosure` the caller gets back,
  rather than being discarded once some check finishes with it.

  Originally fused directly into `WellFormedness/Restrictions.lean`'s own checks (channel-type,
  reserved-name, unbounded-quantifier). Split out here so `Typed2Computable`
  (`.claude/tasklist.md` task 8) can reuse the exact same resolution/recursion/memoization
  machinery to collect "every constant/variable/operator/function reachable from the algorithm,"
  without inheriting `Restrictions.lean`'s own `WellFormednessError`-throwing checks —
  `walkReachable`'s `visit` parameter is the seam: `Restrictions.lean` supplies its checks
  through it, a caller that only wants the closure supplies a no-op.

  `Restrictions.lean`'s checks still run once per node via `visit`, in the same pre-order the
  walk itself visits nodes in (`visit`, then recurse into children) — same visiting order as
  the original fused version, so moving the checks out from under the recursion doesn't change
  what fires or in what order.
-/

/-- What a name resolves to inside one module's declaration list, alongside the raw `Decl`
itself (needed by any caller that wants to do more with it than just classify it —
`Typed2Computable`'s own use, which re-emits referenced constants/variables and translates
referenced operator/function bodies). `assume` entries never resolve (an `ASSUME` isn't a named,
referenceable entity) — falls through to `none` in `Decl.resolve` below, same as "not found". -/
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

/-- The shared walk itself. Visits `e` and everything structurally reachable from it — every
`opCall`'s function/arguments, every quantifier's domain/body, etc. — calling `visit path` once
per node before recursing into its children (`path`, innermost first, only grows when the walk
recurses into a *resolved declaration's* body, not for ordinary substructure recursion — the
breadcrumb `Restrictions.lean`'s error messages report "reached via" through).

Whenever a node is `.var name _ (.module m)`, resolves `(m, name)` and — the first time this
particular pair is seen (`ReachabilityClosure`-memoized, guarding against looping on a
self-recursive `function`; `operator`s never self-recurse, per `Elaborator/Declarations.lean`'s
own doc comment, so only `function` bodies can actually cycle) — records the resolution in the
closure and, if it resolved to an `operator`/`function`, recurses into its body too (with `path`
extended by `name`). A `constant`/`variable` resolution is recorded but never recursed into (no
body to walk). Resolutions after the first for an already-visited pair are silent no-ops as far
as the walk's own recursion is concerned — `visit` still runs on every node regardless, since
some checks (`Restrictions.lean`'s check 2(c)) are per-reference, not per-declaration. -/
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
  | .map' body _ _ dom => do recurse body; recurse dom
  | .fnCall f idx => do recurse f; recurse idx
  | .fn _ _ dom body => do recurse dom; recurse body
  | .fnSet dom cod => do recurse dom; recurse cod
  | .record fs => fs.forM λ (_, _, e) ↦ recurse e
  | .recordSet fs => fs.forM λ (_, _, e) ↦ recurse e
  | .except e upds => do
    recurse e
    upds.forM λ (path', newVal) ↦ do
      path'.forM λ
        | .inl _ => pure ()
        | .inr idx => recurse idx
      recurse newVal
  | .recordAccess e _ => recurse e
  | .tuple es => es.forM λ (_, e) ↦ recurse e
  | .seq es _ => es.forM recurse
  | .if c t f => do recurse c; recurse t; recurse f
  | .case branches other => do
    branches.forM λ (p, e) ↦ do recurse p; recurse e
    other.forM recurse
  | .nat _ | .str _ | .true | .false => pure ()
  | .stutter .. => pure ()
  -- Unreachable in practice (every `mvar` is substituted away before the checker's output is
  -- ever handed to a caller) — recurse defensively rather than special-case an impossible input.
  | .mvar _ e => recurse e
