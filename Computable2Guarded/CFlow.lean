module

public import Core.ComputablePlusCal.Syntax
public import Computable2Guarded.Errors

public section

/-!
  `𝒞_cflow` (thesis §3.2.2, `PLAN.md` §5.4): eliminates `if`/`while` by rewriting them into
  `either`/`await` congruences. Same type in, same type out (`ComputablePlusCal.Statement`/
  `.Block`/`.Branches`) — `if`/`while` are eliminated as a runtime fact, not type-encoded, the
  same "only the producer maintains the invariant" precedent §5.2a already uses for
  "`while` must be immediately preceded by a label."

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
`origin := .intrinsic`). -/
private def negate (e : Expression) : Expression :=
  .opCall (.var "\\neg" (.operator [.bool] .bool) .intrinsic) [e]

/-- Prepends `await g` to `B`'s own non-terminal statements — used to build both `𝒞_cflow`'s
`if`/`while` rewrite's guarded branches. -/
private def awaitPrepend (g : Expression) {b} (B : Block b) : Block b :=
  ⟨.await g :: B.begin, B.end⟩

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty GuardedError m]

/-- Coerces `B` to end in an explicit `goto label`, iff it doesn't already — i.e. the two real
cases from `ElaboratedPlusCal.Statement.while`'s own doc comment: a loop body already terminal
(ends in its own `goto` back to the loop, because a labelled step was extracted from it) passes
through unchanged; a non-terminal one gets `goto label` appended as its new terminal. The
`(true, false)` case is a genuine contradiction (a body that's already terminal can't be coerced
to non-terminal without silently dropping a real `goto`) — defensively unreachable given the
`while`-must-be-block-front invariant this pass relies on throughout. -/
private def coerceGoto {b₀ b : Bool} (label : String) (B : Block b₀) : m (Block b) :=
  match b₀, b, B with
  | true, true, B => pure B
  | false, false, B => pure B
  | false, true, ⟨begin, «end»⟩ => pure ⟨begin.concat «end», .goto label⟩
  | true, false, _ => throw (.internalInvariantViolated SourceSpan.placeholder
      "𝒞_cflow: while body already ends in its own goto, but the containing context is non-terminal")

mutual
  /-- `𝒞_cflow` over a single statement. `label` is the enclosing top-level block's own label,
  threaded through unchanged (only ever consulted by `Block.cflow`'s `while`-rewrite; harmless,
  unused for statements nested where a `while` can't legally occur). -/
  partial def ComputablePlusCal.Statement.cflow {b} (label : String) (s : Statement b) : m (Statement b) :=
    match s with
    | .goto l => pure (.goto l)
    | .skip => pure .skip
    | .print e => pure (.print e)
    | .assign asss => pure (.assign asss)
    | .await e => pure (.await e)
    | .assert e => pure (.assert e)
    | .send c e => pure (.send c e)
    | .multicast c filter => pure (.multicast c filter)
    | .receive c r coe => pure (.receive c r coe)
    | .with var ann «=|∈» val B => (.with var ann «=|∈» val ·) <$> Block.cflow label B
    | .either branches => .either <$> Branches.cflow label branches
    | .if cond B₁ B₂ => do
      let B₁' ← Block.cflow label B₁
      let B₂' ← Block.cflow label B₂
      return .either (.or (awaitPrepend cond B₁') (.either (awaitPrepend (negate cond) B₂')))
    -- Defensive: `Block.cflow` intercepts every legitimate `while` (always at its containing
    -- block's own front) before recursing into individual statements — reaching this arm means
    -- one turned up somewhere else, violating the "immediately preceded by a label" invariant.
    | .while _ _ => throw (.internalInvariantViolated SourceSpan.placeholder
        "𝒞_cflow: `while` found somewhere other than its containing block's own front")

  /-- `𝒞_cflow` over a block — the one place `while` actually gets rewritten, per the module doc
  above. -/
  partial def ComputablePlusCal.Block.cflow {b} (label : String) (B : Block b) : m (Block b) :=
    match B with
    | ⟨.while cond B₁ :: rest, «end»⟩ => do
      let B₁' ← Block.cflow label B₁
      let loopBody ← coerceGoto label B₁'
      let restBlock ← Block.cflow label ⟨rest, «end»⟩
      return ⟨[], .either (.or (awaitPrepend cond loopBody) (.either (awaitPrepend (negate cond) restBlock)))⟩
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
    pure { p with threads }
  pure { algo with processes }

end
