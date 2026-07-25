module

public import Core.ComputablePlusCal.Syntax
public import Computable2Guarded.Errors

public section

/-!
  `𝒞_cflow`: eliminates `if`/`while` by rewriting them into `either`/`await` congruences. Same
  type in, same type out (`ComputablePlusCal.Statement`/`.Block`/`.Branches`) — `if`/`while` are
  eliminated as a runtime fact, not type-encoded; only the producer maintains the invariant that
  `while` must be immediately preceded by a label.

  ```
  𝒞_cflow(l: while e do {B1}; B2; goto l') = l: if e then {B1; goto l} else {B2; goto l'}
  𝒞_cflow(if e then B1 else B2) = either {await e; B1} or {await ¬e; B2}
  ```

  `if`'s rewrite is an ordinary per-statement congruence: both branches already share the `if`'s
  own terminal-ness, recurse and reassemble. `while`'s rewrite operates at the *block* level, not
  per-statement: since a `while` must be immediately preceded by a real label (already enforced
  by the desugarer), it's always the first statement of its containing block, so `Block.cflow`
  special-cases `while cond B1 :: rest` and absorbs whatever followed the `while` (`rest`) into
  the loop-exit branch. The loop-continue branch reuses `B1`'s own terminal statement directly if
  it's already terminal (a labelled step was extracted from the loop body, already ending in a
  `goto` back to the loop's own label); otherwise it synthesizes that `goto` itself (`coerceGoto`)
  — matching the doc comment on `ElaboratedPlusCal.Statement.while`'s own `B` field exactly.

  `¬e` is built directly as `opCall (var "\\neg" ...) [e]`, the same shape
  `Desugarer/TLAPlus.lean`'s `PrefixOperator.canonicalName`/`Elaborator/Declarations.lean`'s
  builtin-`Γ₀` entry for `\neg` already establish for this operator.
-/

open ComputablePlusCal (Expression Statement Block Branches)

/-- `¬e`, as an `opCall` against the same builtin `\neg` operator
`Elaborator/Declarations.lean`'s `Γ₀` already declares (`.operator [.bool] .bool`,
`origin := .intrinsic`). Registered at the rewritten `if`/`while`'s own span (`pos`) — the
negation has no source text of its own, but the condition it negates does, and a diagnostic
about it should point there. -/
private def negate (pos : SourceSpan) (e : Expression) : Expression :=
  .opCall (.var "\\neg" (.operator [.bool] .bool) .intrinsic @@ pos) [e] @@ pos

/-- Prepends `await g` to `B`'s own non-terminal statements — used to build both `𝒞_cflow`'s
`if`/`while` rewrite's guarded branches. The synthesized `await` carries the span of the
`if`/`while` whose condition it guards on. -/
private def awaitPrepend (pos : SourceSpan) (g : Expression) {b} (B : Block b) : Block b :=
  ⟨(.await g @@ pos) :: B.begin, B.end⟩

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty GuardedError m]

/-- Coerces `B` to end in an explicit `goto label` if it doesn't already, per
`ElaboratedPlusCal.Statement.while`'s own doc comment: a loop body already terminal (already
ending in its own `goto` back to the loop) passes through unchanged; a non-terminal one gets
`goto label` appended as its new terminal. The `(true, false)` case is unreachable — a body
already terminal can't be coerced to non-terminal without silently dropping a real `goto`.

`pos` is the rewritten `while`'s own span, reported on that unreachable case. The appended
`goto` itself is purely synthesized — there is no source text anywhere for "jump back to the top
of the loop" — so it takes `SourceSpan.placeholder` rather than a borrowed span. -/
private def coerceGoto (pos : SourceSpan) {b₀ b : Bool} (label : String) (B : Block b₀) : m (Block b) :=
  match b₀, b, B with
  | true, true, B => pure B
  | false, false, B => pure B
  | false, true, ⟨begin, «end»⟩ => pure ⟨begin.concat «end», .goto label @@ SourceSpan.placeholder⟩
  | true, false, _ => throw (.internalInvariantViolated pos
      "𝒞_cflow: while body already ends in its own goto, but the containing context is non-terminal")

mutual
  /-- `𝒞_cflow` over a single statement. `label` is the enclosing top-level block's own label,
  threaded through unchanged (only ever consulted by `Block.cflow`'s `while`-rewrite; harmless,
  unused for statements nested where a `while` can't legally occur). -/
  partial def ComputablePlusCal.Statement.cflow {b} (label : String) (s : Statement b) : m (Statement b) :=
    match_source s with
    | .goto l, pos => pure (.goto l @@ pos)
    | .skip, pos => pure (.skip @@ pos)
    | .print e, pos => pure (.print e @@ pos)
    | .assign asss, pos => pure (.assign asss @@ pos)
    | .await e, pos => pure (.await e @@ pos)
    | .assert e, pos => pure (.assert e @@ pos)
    | .send c e, pos => pure (.send c e @@ pos)
    | .multicast c filter, pos => pure (.multicast c filter @@ pos)
    | .receive c r coe, pos => pure (.receive c r coe @@ pos)
    | .with var ann «=|∈» val B, pos => (.with var ann «=|∈» val · @@ pos) <$> Block.cflow label B
    | .either branches, pos => (.either · @@ pos) <$> Branches.cflow label branches
    | .if cond B₁ B₂, pos => do
      let B₁' ← Block.cflow label B₁
      let B₂' ← Block.cflow label B₂
      return .either (.or (awaitPrepend pos cond B₁') (.either (awaitPrepend pos (negate pos cond) B₂'))) @@ pos
    -- `Block.cflow` intercepts every legitimate `while` (always at its containing block's own
    -- front) before recursing into individual statements — reaching this arm means one turned
    -- up elsewhere, violating the "immediately preceded by a label" invariant.
    | .while _ _, pos => throw (.internalInvariantViolated pos
        "𝒞_cflow: `while` found somewhere other than its containing block's own front")

  /-- `𝒞_cflow` over a block — the one place `while` actually gets rewritten, per the module doc
  above. -/
  partial def ComputablePlusCal.Block.cflow {b} (label : String) (B : Block b) : m (Block b) :=
    match B with
    | ⟨w@(.while cond B₁) :: rest, «end»⟩ => do
      let pos := posOf w
      let B₁' ← Block.cflow label B₁
      let loopBody ← coerceGoto pos label B₁'
      let restBlock ← Block.cflow label ⟨rest, «end»⟩
      return ⟨[], .either (.or (awaitPrepend pos cond loopBody)
        (.either (awaitPrepend pos (negate pos cond) restBlock))) @@ pos⟩
    | ⟨s :: rest, «end»⟩ => do
      let s' ← Statement.cflow label s
      let ⟨rest', end'⟩ ← Block.cflow label ⟨rest, «end»⟩
      return ⟨s' :: rest', end'⟩
    | ⟨[], «end»⟩ => (⟨[], ·⟩) <$> Statement.cflow label «end»

  partial def ComputablePlusCal.Branches.cflow {b} (label : String) : Branches b → m (Branches b)
    | .either B => .either <$> Block.cflow label B
    | .or B rest => .or <$> Block.cflow label B <*> Branches.cflow label rest
end

/-- `𝒞_cflow` over a whole algorithm: applied per `(label, Block)` pair, across every thread of
every process — the label a `while` inside that block would need for `coerceGoto`, per the
module doc above. -/
def ComputablePlusCal.Algorithm.cflow (algo : ComputablePlusCal.Algorithm) : m ComputablePlusCal.Algorithm := do
  let processes ← algo.processes.mapM λ p ↦ do
    let threads ← p.threads.mapM (·.mapM λ (label, block) ↦ (label, ·) <$> Block.cflow label block)
    pure ({ p with threads } @@ posOf p)
  pure ({ algo with processes } @@ posOf algo)

end
