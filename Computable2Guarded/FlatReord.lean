module

public import Core.ComputablePlusCal.Syntax
public import Core.GuardedPlusCal.Syntax
public import Core.ComputableTLAPlus.Subst
public import Computable2Guarded.Errors

public section

/-!
  The merged `𝒞_flat`/`𝒞_reord` (thesis §3.2.2, `PLAN.md` §5.4): both are the same kind of
  operation — a single left-to-right walk over a block's statements — so this file goes straight
  from `ComputablePlusCal.Block` to `List GuardedPlusCal.AtomicBranch`, with no intermediate AST
  (no separate `𝒞_flat`-output/`𝒞_reord`-input staging type). Runs after `𝒞_cflow`/`𝒞_par`
  (`Computable2Guarded/CFlow.lean`/`Par.lean`), so no `if`/`while` survives anywhere in the tree
  (`𝒞_cflow` already rewrote every one into `either`/`await`), and every `assign` carries exactly
  one `(Ref, Expr)` pair (`𝒞_par` already reduced every parallel assignment) — both are runtime
  facts checked defensively (`GuardedError.internalInvariantViolated`), not type-level ones, same
  precedent `CFlow.lean` itself already uses for `while`-must-be-block-front.

  `walkBlock` threads two accumulators built up in original encounter order — `guards : List
  (GuardedPlusCal.Statement true false)` (`with`/`await`/`receive`) and `actions : List
  (GuardedPlusCal.Statement false false)` (everything else) — neither ever reordered *within*
  itself, only guards jump *actions* they were originally sequenced after:
  - **action-class statements** (`skip`/`print`/`assert`/`send`/`multicast`/single-target
    `assign`): translated directly and appended to `actions`, unchanged/uninspected. Implements
    no named subpass on its own — it's the "otherwise" case both `𝒞_flat`/`𝒞_reord` leave alone.
  - **`await`/`receive`**: **`𝒞_reord`'s own substitution case.** Needs to "see through" every
    action accumulated so far: `substActionsInExpr`/`substActionsInRef` fold `Expression.substRef`
    across `actions` in *reverse* (most-recently-accumulated action first, since it happened
    closest to this guard's original position — substituting right-to-left through the pending
    prefix realizes the thesis's single-step `e'[e\r]` rule applied once per intervening action).
    `actions` itself is **not** consumed/cleared (those statements still need to run, just after
    every guard) — only the guard being floated gets adjusted, then appended to `guards`.
  - **`with`**: no substitution (a fresh `with`-bound name is never re-bound, per §5.2a, so
    nothing about its own domain expression needs adjusting when it moves earlier). Its
    (body-less) binding is appended to `guards`, and its nested body is *un-nested* — spliced in
    front of whatever followed the `with` (`Block.append`) — before continuing the same walk.
    This un-nesting is sound because of the same freshness/no-shadowing invariant, and uniformly
    resolves `𝒞_par`'s own synthesized nested-`with`-chains too, with no separate case.
  - **`either`**: **`𝒞_flat`'s own fork/hoist case.** Splices each branch in front of whatever
    followed the `either` (again `Block.append`) and recurses independently per branch,
    concatenating every branch's resulting `AtomicBranch` list — the thesis's
    `𝒞_flat(B; either{B1}or…or{Bn}; B') = either{B;B1;B'}or…or{B;Bn;B'}` distribute-over-choice
    equation, applied directly during the walk (a nested `either`/`with`-body reached via
    splicing is discovered and handled the same way, no separate "hoist out of a `with`" rule
    needed).
  - **`goto`**: ends a branch — packages `(guards, actions, goto label)` into one
    `AtomicBranch`.

  This is sound for the `receive`-writes-a-variable-a-later-guard-reads case too: guards are only
  ever *appended* to `guards` in original relative order (never reordered against each other,
  only extracted past intervening actions), so a guard that depends on a preceding `receive`
  stays correctly ordered after it.
-/

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty GuardedError m]

abbrev Guard := ComputableGuardedPlusCal.Statement true false
abbrev Action := ComputableGuardedPlusCal.Statement false false

/-- Sequences a non-terminal block `B₁` in front of whatever continues afterward (`B₂`) — the
type-safe form of the thesis's `Bi.begin ++ [Bi.end] ++ rest` splicing (`𝒞_flat`'s `either`-hoist,
`with`-body un-nesting), reused for both. -/
private def ComputablePlusCal.Block.append {b} :
    ComputablePlusCal.Block false → ComputablePlusCal.Block b → ComputablePlusCal.Block b
  | ⟨begin₁, end₁⟩, ⟨begin₂, end₂⟩ => ⟨begin₁ ++ (end₁ :: begin₂), end₂⟩

/-- Flattens an `either`/`or` chain into a plain list of alternative blocks. -/
private def ComputablePlusCal.Branches.toList : ∀ {b}, ComputablePlusCal.Branches b → List (ComputablePlusCal.Block b)
  | _, .either B => [B]
  | _, .or B rest => B :: Branches.toList rest

/-- `𝒞_reord`'s `e'[e\r]`, folded across every accumulated action in reverse — see the module doc
above. Only `assign` actually substitutes anything (the others bind nothing). -/
private def substActionsInExpr (actions : List Action) (e : ComputablePlusCal.Expression) :
    ComputablePlusCal.Expression :=
  actions.reverse.foldl (λ acc stmt ↦ match stmt with
    | .assign r rhs => ComputableTLAPlus.Expression.substRef r rhs acc
    | _ => acc) e

/-- The same fold, applied per `.inr` (index) segment of a `Ref` — `receive`'s own channel/
destination arguments, per the module doc's `receive`-extension. -/
private def substActionsInRef (actions : List Action) (r : ComputablePlusCal.Ref) : ComputablePlusCal.Ref :=
  { r with args := r.args.map (Sum.map id (substActionsInExpr actions)) }

/-- Packages a nonempty `guards` list into `AtomicBranch.precondition`'s own `Block` shape
(`begin` and `last` share one type here, unlike `action`'s — see `Core/GuardedPlusCal/Syntax.lean`'s
module doc on `Block`'s generic index family). -/
private def guardsBlock (g : Guard) : List Guard → GuardedPlusCal.Block (ComputableGuardedPlusCal.Statement true) false
  | [] => ⟨[], g⟩
  | g' :: gs => let B := guardsBlock g' gs; ⟨g :: B.begin, B.last⟩

private def finalizeBranch (guards : List Guard) (actions : List Action) (l : String) :
    ComputableGuardedPlusCal.AtomicBranch :=
  { precondition := match guards with
      | [] => none
      | g :: gs => some (guardsBlock g gs)
    action := ⟨actions, .goto l⟩ }

namespace FlatReord

mutual
  /-- The entry point: `walkBlock [] [] block` for a top-level labelled `AtomicBlock`'s own body. -/
  partial def walkBlock {b} (guards : List Guard) (actions : List Action) :
      ComputablePlusCal.Block b → m (List ComputableGuardedPlusCal.AtomicBranch)
    | ⟨[], «end»⟩ => walkTerminal guards actions «end»
    | ⟨s :: rest, «end»⟩ => walkStep guards actions s ⟨rest, «end»⟩

  /-- One non-terminal statement `s`, given `rest` — everything else in `s`'s own containing
  block, continuing after it. -/
  partial def walkStep {b} (guards : List Guard) (actions : List Action)
      (s : ComputablePlusCal.Statement false) (rest : ComputablePlusCal.Block b) :
      m (List ComputableGuardedPlusCal.AtomicBranch) :=
    match s with
    | .skip => walkBlock guards (actions ++ [.skip]) rest
    | .print e => walkBlock guards (actions ++ [.print e]) rest
    | .assert e => walkBlock guards (actions ++ [.assert e]) rest
    | .send c e => walkBlock guards (actions ++ [.send c e]) rest
    | .multicast c filter => walkBlock guards (actions ++ [.multicast c filter]) rest
    | .assign [(r, e)] => walkBlock guards (actions ++ [.assign r e]) rest
    | .assign _ => throw (.internalInvariantViolated SourceSpan.placeholder
        "FlatReord: an `assign` with a target count ≠ 1 reached — 𝒞_par should already have \
reduced every parallel assignment to single targets")
    | .await e => walkBlock (guards ++ [.await (substActionsInExpr actions e)]) actions rest
    | .receive c r coe =>
      walkBlock (guards ++ [.receive (substActionsInRef actions c) (substActionsInRef actions r) coe]) actions rest
    | .with var ann «=|∈» val B =>
      walkBlock (guards ++ [.with var ann «=|∈» val]) actions (ComputablePlusCal.Block.append B rest)
    | .either branches => do
      let results ← (ComputablePlusCal.Branches.toList branches).mapM
        λ Bi ↦ walkBlock guards actions (ComputablePlusCal.Block.append Bi rest)
      pure results.flatten
    | .if .. => throw (.internalInvariantViolated SourceSpan.placeholder
        "FlatReord: `if` found — 𝒞_cflow should have eliminated every `if` already")
    | .while .. => throw (.internalInvariantViolated SourceSpan.placeholder
        "FlatReord: `while` found — 𝒞_cflow should have eliminated every `while` already")

  /-- The block's own final statement — no `rest` exists beyond it (any dangling non-`goto` `end`
  gets absorbed into a `begin`-position `walkStep` call instead, by `Block.append`'s own
  splicing, before ever reaching here — see the module doc). -/
  partial def walkTerminal {b} (guards : List Guard) (actions : List Action) :
      ComputablePlusCal.Statement b → m (List ComputableGuardedPlusCal.AtomicBranch)
    | .goto l => pure [finalizeBranch guards actions l]
    | .either branches => do
      let results ← (ComputablePlusCal.Branches.toList branches).mapM (walkBlock guards actions)
      pure results.flatten
    | .if .. => throw (.internalInvariantViolated SourceSpan.placeholder
        "FlatReord: `if` found at a block's own terminal position — 𝒞_cflow should have \
eliminated it already")
    | .while .. => throw (.internalInvariantViolated SourceSpan.placeholder
        "FlatReord: `while` found at a block's own terminal position — 𝒞_cflow should have \
eliminated it already")
    | .skip | .print .. | .assert .. | .send .. | .multicast .. | .assign .. | .await ..
    | .receive .. | .with .. => throw (.internalInvariantViolated SourceSpan.placeholder
        "FlatReord: reached a block's own end without a `goto` — every reachable path must \
terminate in one")
end

end FlatReord

end
