module

public import Core.GuardedPlusCal.Syntax
public import Core.ComputableTLAPlus.FreeVars

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

/-- A larger forbidden set only makes freshness harder to satisfy, never easier — well-scoped
against `inScope` is well-scoped against any subset of it. Lets a caller holding the
whole-algorithm `Algorithm.WellScoped` fact (`inScope = globalNames ++ p.localState.names`)
specialize down to whatever smaller `inScope` a specific lemma invocation actually needs. -/
theorem GuardedPlusCal.wellscoped_mono_of_subset {Typ Expr} {stmts : List (GuardedPlusCal.Statement Typ Expr true false)} :
    ∀ {inScope inScope' : List String}, inScope' ⊆ inScope →
    GuardedPlusCal.PreconditionWellScopedIn inScope stmts →
    GuardedPlusCal.PreconditionWellScopedIn inScope' stmts := by
  induction stmts with
  | nil => intro _ _ _ _; trivial
  | cons s rest ih =>
    cases s with
    | «with» name _ _ _ =>
      intro inScope inScope' h
      rintro ⟨fresh, ws⟩
      refine ⟨λ mem ↦ fresh (h mem), ih (inScope := name :: inScope) (inScope' := name :: inScope') ?_ ws⟩
      intro x hx
      cases hx with
      | head => exact List.mem_cons_self
      | tail _ hx => exact List.mem_cons_of_mem _ (h hx)
    | await _ => intro _ _ h ws; exact ih h ws
    | receive _ _ _ => intro _ _ h ws; exact ih h ws

/-- The bound name of a precondition statement, `none` for `await`/`receive` (which bind
nothing). -/
def GuardedPlusCal.Statement.boundName? {Typ Expr b'} :
    GuardedPlusCal.Statement Typ Expr true b' → Option String
  | .with name _ _ _ => some name
  | .await _ => none
  | .receive _ _ _ => none

/-- The other direction from `Expression.not_mem_of_fresh`, packaged over a whole flat guard
list: every name a `with` in `stmts` binds avoids `e`'s free variables — the capture-avoidance
side condition `Guarded2Network/PlusCal.lean`'s `substGuard` needs when it substitutes `e` (an
earlier `receive`'s consumption expression) into a later guard. -/
theorem GuardedPlusCal.fresh_of_wellscoped_of_not_mem {inScope : List String}
    {e : ComputableTLAPlus.Expression ComputableTLAPlus.Typ} (sub : ∀ z ∈ e.freeVars, z ∈ inScope)
    {stmts : List (ComputableGuardedPlusCal.Statement true false)} :
    GuardedPlusCal.PreconditionWellScopedIn inScope stmts →
    ∀ s ∈ stmts, ∀ name, s.boundName? = some name → name ∉ e.freeVars := by
  induction stmts generalizing inScope with
  | nil => intro _ s hs; cases hs
  | cons s rest ih =>
    cases s with
    | «with» name _ _ _ =>
      rintro ⟨fresh, ws⟩ s' hmem name' heq
      cases hmem with
      | head =>
        simp only [GuardedPlusCal.Statement.boundName?, Option.some.injEq] at heq
        exact heq ▸ ComputableTLAPlus.Expression.not_mem_of_fresh fresh sub
      | tail _ hmem' =>
        exact ih (λ z hz ↦ List.mem_cons_of_mem name (sub z hz)) ws s' hmem' name' heq
    | await _ =>
      intro ws s' hmem name' heq
      cases hmem with
      | head => simp [GuardedPlusCal.Statement.boundName?] at heq
      | tail _ hmem' => exact ih sub ws s' hmem' name' heq
    | receive _ _ _ =>
      intro ws s' hmem name' heq
      cases hmem with
      | head => simp [GuardedPlusCal.Statement.boundName?] at heq
      | tail _ hmem' => exact ih sub ws s' hmem' name' heq

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
