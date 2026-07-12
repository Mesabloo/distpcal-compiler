module

public import WellFormedness.Errors
public import Core.TypedPlusCal.Syntax
public import Core.CorePlusCal.Syntax

public section


/-!
  Well-scopedness (`PLAN.md` §5.2a): every name is fresh in the scope it's declared in — no
  duplicate names within one flat declaration list, and no name shadowing an already-in-scope
  one from an enclosing scope. The four scope classes (matching prior art's Σ/Δ/Γ/Ξ): global
  (`Algorithm.globalState`), process-local (`Process.localState`), and block-local (`with`'s
  own binder) — "channel" isn't a separate namespace from "global"/"process-local" in this
  repo's `Declarations` shape (`variables`/`channels`/`fifos` already coexist in one flat scope
  per `Declarations` value), so it's folded into whichever of those two applies.

  This is only the "no duplicate names / no shadowing" half — the "every reference resolves to
  a declared name" half is now redundant with type checking's own success (§5.2a's reorder) and
  isn't re-derived here.

  Two distinct things below, per §5.2a — don't conflate them:
  1. The **executable** check (`TypedPlusCal.Algorithm.checkWellScoped`), run by the driver.
  2. `CorePlusCal.WellScoped`, a **Prop** authored fresh (no such file exists in prior art at
     the `CorePlusCal` stage — only already-elaborated `GuardedPlusCal`/`TypedSetTheory`
     versions do), modeled on the same scope-class shape. This is infrastructure for a later
     preservation lemma (`CorePlusCal.WellScoped p → GuardedPlusCal.Algorithm.WellScoped
     (Typed2Guarded (Elaborator p))`, `PLAN.md` §2/§6.2/§9), not something (1) needs to invoke —
     nothing proves anything about it yet.

  **Deferred port, flagged here so it isn't missed**: prior art's `Core/GuardedPlusCal/Syntax/
  WellScopedness.lean` and `Core/TypedSetTheory/Syntax/WellScopedness.lean` are the
  already-elaborated restatements of this same discipline — port them (with cleanup) once
  whichever of Phase 8 (`TypedSetTheory`) / Phase 9 (`GuardedPlusCal`, via `Typed2Guarded`)
  actually creates those types. Neither exists in this repo yet.
-/

/-! ## 1. The executable check, over `TypedPlusCal.Algorithm` -/

/-- Every name a `Declarations` value binds, paired with the best position available to report
against it — the entry's own initializer/index expression if one exists, `SourceSpan.placeholder`
otherwise (a bare `variables x;` with no initializer, or an unindexed channel, carries no
position of its own to point at; matches `requireAnnotation SourceSpan.placeholder`'s own
fallback elsewhere in this codebase). `variables` ++ `channels` ++ `fifos`, matching
`checkPlusCalDeclarations`'s own binding order (`Elaborator/PlusCal.lean`). -/
private def TypedPlusCal.Declarations.namesWithPos (d : TypedPlusCal.Declarations) : List (String × SourceSpan) :=
  d.variables.map (λ (x, _, _, init) ↦ (x, init.elim SourceSpan.placeholder (posOf ·.2)))
  ++ d.channels.map (λ (x, _, idxs) ↦ (x, idxs.head?.elim SourceSpan.placeholder posOf))
  ++ d.fifos.map (λ (x, _, idxs) ↦ (x, idxs.head?.elim SourceSpan.placeholder posOf))

/-- Rejects the first repeated name within one flat list — `duplicateName` at *that* repeat's
own position, not the first occurrence's. -/
private def checkNoDuplicates {m : Type → Type} [Monad m] [MonadExceptOf WellFormednessError m] :
    List (String × SourceSpan) → m Unit
  | [] => pure ()
  | (n, _) :: rest =>
    match rest.find? (·.1 == n) with
    | some (_, pos) => throw (.duplicateName pos n)
    | none => checkNoDuplicates rest

/-- Rejects any of `names` already present in `inScope` — `shadowedName` at the shadowing
entry's own position. -/
private def checkNoShadow {m : Type → Type} [Monad m] [MonadExceptOf WellFormednessError m]
    (inScope : List String) (names : List (String × SourceSpan)) : m Unit :=
  names.forM λ (n, pos) ↦ do
    if inScope.contains n then throw (.shadowedName pos n)

/-- Walks every `with` binder reachable from `s`, checking it against `inScope` and extending
it for the sub-block. No other statement introduces a PlusCal-visible name. -/
partial def TypedPlusCal.Statement.checkWellScoped {b} {m : Type → Type} [Monad m]
    [MonadExceptOf WellFormednessError m] (inScope : List String) (s : TypedPlusCal.Statement b) : m Unit :=
  match_source s with
  | .if _ B₁ B₂, _ => do
    ElaboratedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkWellScoped inScope) B₁
    ElaboratedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkWellScoped inScope) B₂
  | .either branches, _ =>
    ElaboratedPlusCal.Branches.forStatements (TypedPlusCal.Statement.checkWellScoped inScope) branches
  | .while _ B, _ => ElaboratedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkWellScoped inScope) B
  | .with x _ _ _ B, pos => do
    if inScope.contains x then throw (.shadowedName pos x)
    ElaboratedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkWellScoped (x :: inScope)) B
  | .goto _, _ | .skip, _ | .print _, _ | .assign _, _ | .await _, _ | .assert _, _
  | .receive _ _ _, _ | .send _ _, _ | .multicast _ _, _ => pure ()

/-- Well-scopedness over a whole algorithm: global declarations fresh among themselves; each
process's own local declarations fresh among themselves and not shadowing a global one; every
`with` binder inside a process's threads fresh against global ++ that process's own locals ++
whatever outer `with`s it's nested in. -/
def TypedPlusCal.Algorithm.checkWellScoped {m : Type → Type} [Monad m]
    [MonadExceptOf WellFormednessError m] (algo : TypedPlusCal.Algorithm) : m Unit := do
  let globalNames := TypedPlusCal.Declarations.namesWithPos algo.globalState
  checkNoDuplicates globalNames
  for p in algo.processes do
    let localNames := TypedPlusCal.Declarations.namesWithPos p.localState
    checkNoDuplicates localNames
    checkNoShadow (globalNames.map Prod.fst) localNames
    let inScope := globalNames.map Prod.fst ++ localNames.map Prod.fst
    for thread in p.threads do
      for (_, blk) in thread do
        ElaboratedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkWellScoped inScope) blk

/-! ## 2. `CorePlusCal.WellScoped`, a Prop — authored fresh, not executed -/

/-- Every name a `Declarations` value binds — the `Prop`-side counterpart of
`TypedPlusCal.Declarations.namesWithPos`, with no position (irrelevant to a `Prop`). -/
def CorePlusCal.Declarations.names {α β} (d : CorePlusCal.Declarations α β) : List String :=
  (d.variables.map (·.1)) ++ (d.channels.map (·.1)) ++ (d.fifos.map (·.1))

mutual
  /-- `s` introduces no shadowing/duplicate name, given `inScope` already holds — the `Prop`
  counterpart of `TypedPlusCal.Statement.checkWellScoped`. -/
  partial def CorePlusCal.Statement.WellScopedIn {α β b} (inScope : List String) :
      CorePlusCal.Statement α β b → Prop
    | .if _ B₁ B₂ => CorePlusCal.Block.WellScopedIn inScope B₁ ∧ CorePlusCal.Block.WellScopedIn inScope B₂
    | .either branches => CorePlusCal.Branches.WellScopedIn inScope branches
    | .while _ B => CorePlusCal.Block.WellScopedIn inScope B
    | .with x _ _ _ B => x ∉ inScope ∧ CorePlusCal.Block.WellScopedIn (x :: inScope) B
    | .goto _ | .skip | .print _ | .assign _ | .await _ | .assert _
    | .receive _ _ | .send _ _ | .multicast _ _ => True

  partial def CorePlusCal.Block.WellScopedIn {α β b} (inScope : List String) (B : CorePlusCal.Block α β b) : Prop :=
    (∀ s ∈ B.begin, CorePlusCal.Statement.WellScopedIn inScope s) ∧ CorePlusCal.Statement.WellScopedIn inScope B.end

  partial def CorePlusCal.Branches.WellScopedIn {α β b} (inScope : List String) :
      CorePlusCal.Branches α β b → Prop
    | .either B => CorePlusCal.Block.WellScopedIn inScope B
    | .or B rest => CorePlusCal.Block.WellScopedIn inScope B ∧ CorePlusCal.Branches.WellScopedIn inScope rest
end

/-- `p` has no duplicate name in any scope, and no name shadows an enclosing scope's — the
`Prop` counterpart of `TypedPlusCal.Algorithm.checkWellScoped`, over the pre-`Elaborator`
`CorePlusCal.Algorithm`. Not proved or used by anything yet — see the module doc above. -/
def CorePlusCal.WellScoped {α β} (algo : CorePlusCal.Algorithm α β) : Prop :=
  algo.globalState.names.Nodup ∧
  ∀ p ∈ algo.processes,
    p.localState.names.Nodup ∧
    (∀ n ∈ p.localState.names, n ∉ algo.globalState.names) ∧
    ∀ thread ∈ p.threads, ∀ pair ∈ thread,
      CorePlusCal.Block.WellScopedIn (algo.globalState.names ++ p.localState.names) pair.2

end
