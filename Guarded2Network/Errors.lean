module

public import Common.Errors

public section

/-! `Guarded2Network`'s diagnostics: a single defense-in-depth catch-all. Every case it reports is
one an earlier pass rules out — type checking establishes that a `receive`'s channel reference
resolves and is `Channel(_)`-shaped — but this pass has no proof of that to appeal to, so the checks
are real ones. -/

/-- `Guarded2Network`'s errors. -/
inductive G2NError : Type
  /-- Defense-in-depth: an input shape this pass's own invariants (or type checking's) guarantee
  can't occur (e.g. a `receive`'s channel resolving to a non-`Channel(_)` type, or not resolving
  at all) still turned up. No proof of unreachability exists yet, just facts established by
  earlier passes, so this stays a runtime check, not `absurd`/`nomatch`. `pos` is
  `SourceSpan.placeholder` at callers past the point a real position is still available
  (`GuardedPlusCal.Statement` carries none), matching `Typed2Computable.lean`'s precedent. -/
  | internalInvariantViolated (pos : SourceSpan) (description : String)
  deriving Repr, Inhabited, BEq

instance : CompilerDiagnostic G2NError String where
  isError := true
  code | .internalInvariantViolated .. => Diagnostics.networkInternalInvariant.code
  posOf
    | .internalInvariantViolated pos _ => pos
  msgOf
    | .internalInvariantViolated _ description =>
      s!"Internal invariant violated: {description}. This should be unreachable — please report this as a bug."

end
