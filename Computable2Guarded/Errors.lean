module

public import Common.Errors
public import Core.TypedTLAPlus.Syntax

public section

/-! `Computable2Guarded`'s diagnostics — a single defense-in-depth catch-all, mirroring
`Typed2Computable/Errors.lean:34`'s `ComputableError.internalInvariantViolated` exactly. Every
case this pass can hit should be impossible given upstream guarantees (e.g. `𝒞_cflow` finding a
`while` not at block-front) — this pass introduces no genuinely new user-facing restriction. -/

/-- `Computable2Guarded`'s errors. -/
inductive GuardedError : Type
  /-- Defense-in-depth: an input shape this pass's own invariants guarantee can't occur (e.g. a
  `while` not immediately preceded by a labelled block) still turned up. No proof of
  unreachability exists yet, so this stays a runtime check rather than `absurd`/`nomatch`. `pos`
  is `SourceSpan.placeholder` at callers past the point where a real position is still available
  (`ElaboratedPlusCal`/`GuardedPlusCal.Statement` carry none), matching
  `Typed2Computable.lean`'s own precedent. -/
  | internalInvariantViolated (pos : SourceSpan) (description : String)
  deriving Repr, Inhabited, BEq

instance : CompilerDiagnostic GuardedError String where
  isError := true
  posOf
    | .internalInvariantViolated pos _ => pos
  msgOf
    | .internalInvariantViolated _ description =>
      s!"Internal invariant violated: {description}. This should be unreachable — please report this as a bug."

end
