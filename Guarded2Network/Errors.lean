module

public import Common.Errors

public section

/-! `Guarded2Network`'s diagnostics — a single defense-in-depth catch-all, mirroring
`Computable2Guarded/Errors.lean`'s `GuardedError.internalInvariantViolated` exactly. Every case
this pass can hit is "should be impossible given upstream guarantees": type checking already
guarantees a `receive`'s channel reference resolves and is `Channel(_)`-shaped (`Elaborator/
PlusCal.lean`'s `checkChannelDecl`/channel-reference checking), but no proof of that fact exists
yet — prior art's own two `panic!` sites for exactly this ("channel has wrong type" / "channel
not found", `~/Documents/distpcal-compiler/Guarded2Network/PlusCal.lean:96,99`) become real
runtime checks here instead, same rationale as `ComputableError.internalInvariantViolated`. -/

/-- `Guarded2Network`'s errors. -/
inductive G2NError : Type
  /-- Defense-in-depth: an input shape this pass's own invariants (or type checking's) guarantee
  can't occur (e.g. a `receive`'s channel resolving to a non-`Channel(_)` type, or not resolving
  at all) still turned up. No proof of unreachability exists for any of these yet — just facts
  established by earlier passes — so this stays a runtime check, not `absurd`/`nomatch`. `pos` is
  `SourceSpan.placeholder` at callers past the point where a real position is still available
  (`GuardedPlusCal.Statement` carries none), matching `Typed2Computable.lean`'s own precedent. -/
  | internalInvariantViolated (pos : SourceSpan) (description : String)
  deriving Repr, Inhabited, BEq

instance : CompilerDiagnostic G2NError String where
  isError := true
  posOf
    | .internalInvariantViolated pos _ => pos
  msgOf
    | .internalInvariantViolated _ description =>
      s!"Internal invariant violated: {description}. This should be unreachable — please report this as a bug."

end
