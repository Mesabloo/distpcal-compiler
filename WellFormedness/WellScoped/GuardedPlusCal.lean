module

public import Core.GuardedPlusCal.Syntax

public section

/-!
  `GuardedPlusCal.Algorithm.WellScoped`, a **Prop** — `Guarded2Network`'s refinement proof
  precondition (§9, phase 10 item 5), assumed as a hypothesis wherever that proof needs it, not
  derived from `Elaborator`/`Computable2Guarded`'s own behavior (out of scope for this file, and
  for phase 10 generally — this phase is about `Guarded2Network`, not the passes before it).

  Same "no duplicate / no shadow" discipline as `WellFormedness.WellScoped.CorePlusCal`'s Prop,
  adapted to `GuardedPlusCal`'s post-`Computable2Guarded` shape: every `if`/`while`/`either`/
  nested-`with` has already been rewritten into `AtomicBranch`'s flat precondition/action split,
  so there's no nested `Block` to recurse into the way `CorePlusCal.Statement.WellScopedIn`'s
  `.with` case does. The only name-introducing construct left is a precondition's own `.with`,
  and — unlike `CorePlusCal`'s nested `with`, whose body-scope closes at `}` — a flattened
  precondition's later statements (guard *and* action) really do see an earlier `.with`'s
  binding, so its freshness has to be threaded sequentially down the flat guard list rather than
  checked once against one shared `inScope` (`CorePlusCal.Block.WellScopedIn`'s `∀ s ∈ B.begin,
  …` pattern would be wrong here — it'd let two sibling `.with`s reuse the same name).
  `receive`/`send`/`assign`/`multicast`'s targets aren't required to resolve against any
  particular scope class here, matching `CorePlusCal.WellScoped`'s own choice not to re-derive
  "every reference resolves" (redundant with `Computable2Guarded`'s success, whose input already
  passed `TypedPlusCal.Algorithm.checkWellScoped`) — this Prop is only about fresh/shadow-free
  binder positions, not full reference resolution.
-/

/-- Every name a `Declarations` value binds — the `GuardedPlusCal` counterpart of
`CorePlusCal.Declarations.names`. -/
def GuardedPlusCal.Declarations.names {Typ Expr} (d : GuardedPlusCal.Declarations Typ Expr) : List String :=
  (d.variables.map (·.1)) ++ (d.channels.map (·.1)) ++ (d.fifos.map (·.1))

/-- Whether a precondition's own flat guard list introduces no duplicate/shadowed name, given
`inScope` already holds — `with`'s binder must be fresh against `inScope` *and* every earlier
`with` in the same list; `await`/`receive` bind nothing. The `Prop` counterpart of what
`GuardedPlusCal.Thread.toNetwork` (`Guarded2Network/PlusCal.lean`) relies on implicitly when it
threads a `receive`'s destination straight into later guards without renaming. -/
def GuardedPlusCal.PreconditionWellScopedIn {Typ Expr} (inScope : List String) :
    List (GuardedPlusCal.Statement Typ Expr true false) → Prop
  | [] => True
  | .with name _ _ _ :: rest => name ∉ inScope ∧ GuardedPlusCal.PreconditionWellScopedIn (name :: inScope) rest
  | .await _ :: rest | .receive _ _ _ :: rest => GuardedPlusCal.PreconditionWellScopedIn inScope rest

/-- `Br`'s own precondition (if any) is well-scoped against `inScope` — the action block binds
nothing, so there's nothing further to check there (same reasoning as `CorePlusCal.WellScoped`
not inspecting `.assign`/`.send`/etc.'s expressions). -/
def GuardedPlusCal.AtomicBranch.WellScopedIn {Typ Expr} (inScope : List String)
    (Br : GuardedPlusCal.AtomicBranch Typ Expr) : Prop :=
  match Br.precondition with
  | none => True
  | some B => GuardedPlusCal.PreconditionWellScopedIn inScope (B.begin ++ [B.last])

/-- `p` has no duplicate name in any scope, and no name shadows an enclosing scope's — the
`GuardedPlusCal` counterpart of `CorePlusCal.WellScoped`'s per-process conjunct. -/
structure GuardedPlusCal.Process.WellScoped {Typ Expr} (p : GuardedPlusCal.Process Typ Expr)
    (globalNames : List String) : Prop where
  locals_nodup : p.localState.names.Nodup
  locals_no_shadow : ∀ n ∈ p.localState.names, n ∉ globalNames
  branches_ws : ∀ thread ∈ p.threads, ∀ blk ∈ thread, ∀ Br ∈ blk.branches,
    GuardedPlusCal.AtomicBranch.WellScopedIn (globalNames ++ p.localState.names) Br

/-- The `GuardedPlusCal` counterpart of `CorePlusCal.WellScoped` — `Guarded2Network`'s
refinement proof precondition. -/
structure GuardedPlusCal.Algorithm.WellScoped {Typ Expr} (algo : GuardedPlusCal.Algorithm Typ Expr) : Prop where
  global_nodup : algo.globalState.names.Nodup
  procs_ws : ∀ p ∈ algo.processes, GuardedPlusCal.Process.WellScoped p algo.globalState.names

end
