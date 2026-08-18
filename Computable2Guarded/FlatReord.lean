module

public import Core.ComputablePlusCal.Syntax
public import Core.GuardedPlusCal.Syntax
public import Core.ComputableTLAPlus.Subst
public import Computable2Guarded.Errors

public section

/-!
  The merged `𝒞_flat`/`𝒞_reord`: both are the same kind of operation — a single left-to-right
  walk over a block's statements — so this file goes straight from `ComputablePlusCal.Block` to
  `List GuardedPlusCal.AtomicBranch`, with no intermediate AST (no separate `𝒞_flat`-output/
  `𝒞_reord`-input staging type). Runs after `𝒞_cflow`/`𝒞_par` (`Computable2Guarded/CFlow.lean`/
  `Par.lean`), so no `if`/`while` survives anywhere in the tree (`𝒞_cflow` already rewrote every
  one into `either`/`await`), and every `assign` carries exactly one `(Ref, Expr)` pair (`𝒞_par`
  already reduced every parallel assignment) — both are runtime facts checked defensively
  (`GuardedError.internalInvariantViolated`), not type-level ones, same precedent `CFlow.lean`
  itself already uses for `while`-must-be-block-front.

  `walkBlock` threads two accumulators in original encounter order — `guards`
  (`with`/`await`/`receive`) and `actions` (everything else). Neither is reordered *within* itself;
  only guards jump actions they were originally sequenced after, and a floated guard is rewritten
  as it goes:

  ```
  𝒞_reord(r ≔ e ; await e') = await e'[e\r] ; r ≔ e
  𝒞_flat(B ; either{B₁}or…or{Bₙ} ; B') = either{B;B₁;B'}or…or{B;Bₙ;B'}
  ```

  A guard is only ever appended to `guards`, so guards keep their relative order and one reading a
  variable a preceding `receive` writes stays after it. A `goto` ends a branch, packaging
  `(guards, actions, label)` into one `AtomicBranch`.
-/

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty GuardedError m]

abbrev Guard := ComputableGuardedPlusCal.Statement true false
abbrev Action := ComputableGuardedPlusCal.Statement false false

/-- Sequences a non-terminal block `B₁` in front of whatever continues afterward (`B₂`) — the
type-safe form of `Bi.begin ++ [Bi.end] ++ rest` splicing (`𝒞_flat`'s `either`-hoist, `with`-body
un-nesting), reused for both. -/
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

/-- `pos` is the terminating `goto`'s own span, carried onto the `GuardedPlusCal` `goto` this
builds — the branch's every other statement was already registered by `walkStep`. -/
private def finalizeBranch (guards : List Guard) (actions : List Action) (l : String)
    (pos : SourceSpan) : ComputableGuardedPlusCal.AtomicBranch :=
  { precondition := match guards with
      | [] => none
      | g :: gs => some (guardsBlock g gs)
    action := ⟨actions, .goto l @@ pos⟩ }

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
    match_source s with
    | .skip, pos => walkBlock guards (actions ++ [.skip @@ pos]) rest
    | .print e, pos => walkBlock guards (actions ++ [.print e @@ pos]) rest
    | .assert e, pos => walkBlock guards (actions ++ [.assert e @@ pos]) rest
    | .send c e, pos => walkBlock guards (actions ++ [.send c e @@ pos]) rest
    | .multicast c filter, pos => walkBlock guards (actions ++ [.multicast c filter @@ pos]) rest
    | .assign [(r, e)], pos => walkBlock guards (actions ++ [.assign r e @@ pos]) rest
    | .assign _, pos => throw (.internalInvariantViolated pos
        "FlatReord: an `assign` with a target count ≠ 1 reached — 𝒞_par should already have \
reduced every parallel assignment to single targets")
    | .await e, pos => walkBlock (guards ++ [.await (substActionsInExpr actions e) @@ pos]) actions rest
    | .receive c r coe, pos =>
      walkBlock (guards ++ [.receive (substActionsInRef actions c) (substActionsInRef actions r) coe @@ pos])
        actions rest
    | .with var ann «=|∈» val B, pos =>
      walkBlock (guards ++ [.with var ann «=|∈» val @@ pos]) actions (ComputablePlusCal.Block.append B rest)
    | .either branches, _ => do
      let results ← (ComputablePlusCal.Branches.toList branches).mapM
        λ Bi ↦ walkBlock guards actions (ComputablePlusCal.Block.append Bi rest)
      pure results.flatten
    | .if .., pos => throw (.internalInvariantViolated pos
        "FlatReord: `if` found — 𝒞_cflow should have eliminated every `if` already")
    | .while .., pos => throw (.internalInvariantViolated pos
        "FlatReord: `while` found — 𝒞_cflow should have eliminated every `while` already")

  /-- The block's own final statement — no `rest` exists beyond it (any dangling non-`goto` `end`
  gets absorbed into a `begin`-position `walkStep` call instead, by `Block.append`'s own
  splicing, before ever reaching here — see the module doc). -/
  partial def walkTerminal {b} (guards : List Guard) (actions : List Action)
      (s : ComputablePlusCal.Statement b) : m (List ComputableGuardedPlusCal.AtomicBranch) :=
    match_source s with
    | .goto l, pos => pure [finalizeBranch guards actions l pos]
    | .either branches, _ => do
      let results ← (ComputablePlusCal.Branches.toList branches).mapM (walkBlock guards actions)
      pure results.flatten
    | .if .., pos => throw (.internalInvariantViolated pos
        "FlatReord: `if` found at a block's own terminal position — 𝒞_cflow should have \
eliminated it already")
    | .while .., pos => throw (.internalInvariantViolated pos
        "FlatReord: `while` found at a block's own terminal position — 𝒞_cflow should have \
eliminated it already")
    | .skip, pos | .print .., pos | .assert .., pos | .send .., pos | .multicast .., pos
    | .assign .., pos | .await .., pos | .receive .., pos | .with .., pos =>
      throw (.internalInvariantViolated pos
        "FlatReord: reached a block's own end without a `goto` — every reachable path must \
terminate in one")
end

end FlatReord

end
