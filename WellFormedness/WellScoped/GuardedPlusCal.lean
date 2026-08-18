module

public import Core.GuardedPlusCal.Syntax
public import Core.ComputableTLAPlus.FreeVars

public section

/-!
  `GuardedPlusCal.Algorithm.WellScoped`, a **Prop** — `Guarded2Network`'s refinement proof
  precondition, assumed as a hypothesis wherever that proof needs it rather than derived from
  `Elaborator`/`Computable2Guarded`'s own behavior.

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
  passed `TypedPlusCal.Algorithm.checkWellScoped`) — nothing here derives full reference
  resolution.

  Beyond binder positions it also carries the **two receive restrictions**
  (`GuardedPlusCal.PreconditionReceives`): one channel per process, and no `receive` target
  indexing its own channel. `WellFormedness/Restrictions.lean` checks both executably over
  `TypedPlusCal`; they are restated here as `Prop`s because `Guarded2Network`'s refinement proof
  needs them and has no other source for them: the executable checks exist so that the proof can
  assume them. That is why the structures below are concrete over
  `ComputableGuardedPlusCal` rather than generic in `Typ`/`Expr`: `Ref.freeVars` is.
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

/-- The two receive restrictions `WellFormedness/Restrictions.lean` checks executably over
`TypedPlusCal` (`checkOneReceive`, `checkRefRestrictions`), restated as a `Prop` over one
precondition's flat guard list — the form `Guarded2Network`'s refinement proof consumes.

Neither is stylistic: with two channels the consumption site `x := Head(inbox)`
cannot tell which channel a message arrived on, and a `receive` whose target name indexes its own
channel moves the `ChanKey` the refinement invariant pins out from under it. The executable checks
exist so that this proof can assume them; this is the assumption they justify.

Concrete rather than generic in `Typ`/`Expr`, because `Ref.freeVars` is. -/
structure GuardedPlusCal.PreconditionReceives (c₀ : ComputableGuardedPlusCal.Ref)
    (stmts : List (ComputableGuardedPlusCal.Statement true false)) : Prop where
  /-- Every `receive` here names the same channel — the process's one mailbox. -/
  one_channel : ∀ c r coe, GuardedPlusCal.Statement.receive c r coe ∈ stmts → c = c₀
  /-- No `receive`'s target is a name its own channel is indexed by. -/
  target_not_in_channel : ∀ (c r : ComputableGuardedPlusCal.Ref) coe,
    GuardedPlusCal.Statement.receive c r coe ∈ stmts → r.name ∉ GuardedPlusCal.Ref.freeVars c

/-- `Br`'s own precondition (if any) is well-scoped against `inScope` and receives only from `c₀` —
the action block binds nothing, so there's nothing further to check there (same reasoning as
`CorePlusCal.WellScoped` not inspecting `.assign`/`.send`/etc.'s expressions). -/
def GuardedPlusCal.AtomicBranch.WellScopedIn (inScope : List String)
    (c₀ : ComputableGuardedPlusCal.Ref) (Br : ComputableGuardedPlusCal.AtomicBranch) : Prop :=
  match Br.precondition with
  | none => True
  | some B =>
    GuardedPlusCal.PreconditionWellScopedIn inScope (B.begin ++ [B.last]) ∧
      GuardedPlusCal.PreconditionReceives c₀ (B.begin ++ [B.last])

/-- `p` has no duplicate name in any scope, no name shadows an enclosing scope's, and every
`receive` it makes is from the one channel it listens on — the `GuardedPlusCal` counterpart of
`CorePlusCal.WellScoped`'s per-process conjunct.

The mailbox is existential rather than a field: this is a `Prop`, and which channel it is does not
matter to any consumer — only that one channel serves the whole process, which is what
`Restrictions.lean`'s `checkOneReceive` establishes by installing the first `receive`'s channel and
comparing the rest against it. -/
structure GuardedPlusCal.Process.WellScoped (p : ComputableGuardedPlusCal.Process)
    (globalNames : List String) : Prop where
  locals_nodup : p.localState.names.Nodup
  locals_no_shadow : ∀ n ∈ p.localState.names, n ∉ globalNames
  branches_ws : ∃ mailbox : ComputableGuardedPlusCal.Ref,
    ∀ thread ∈ p.threads, ∀ blk ∈ thread, ∀ Br ∈ blk.branches,
      GuardedPlusCal.AtomicBranch.WellScopedIn (globalNames ++ p.localState.names) mailbox Br

/-- The `GuardedPlusCal` counterpart of `CorePlusCal.WellScoped` — `Guarded2Network`'s
refinement proof precondition. -/
structure GuardedPlusCal.Algorithm.WellScoped (algo : ComputableGuardedPlusCal.Algorithm) : Prop where
  global_nodup : algo.globalState.names.Nodup
  procs_ws : ∀ p ∈ algo.processes, GuardedPlusCal.Process.WellScoped p algo.globalState.names

end
