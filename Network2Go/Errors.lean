module

public import Common.Errors

public section

/-! `Network2Go`'s diagnostics — a single defense-in-depth catch-all, mirroring
`Guarded2Network/Errors.lean`'s `G2NError.internalInvariantViolated`. Every case this pass can hit
should be impossible given upstream guarantees: `Guarded2Network` already established the network
form's own invariants (every channel reference resolved, every process's threads well-formed), and
type checking established the TLA⁺-side ones this pass compiles against. No proof of either fact
exists yet, so these stay real runtime checks, same rationale as
`ComputableError.internalInvariantViolated`. Real, user-facing failure modes (an unsupported source
construct, say) get their own constructors as the compilation passes surface them. -/

/-- `Network2Go`'s errors. -/
inductive N2GError : Type
  /-- Defense-in-depth: an input shape this pass's own invariants (or those of an earlier pass)
  guarantee can't occur still turned up. No proof of unreachability exists yet, just facts
  established by earlier passes, so this stays a runtime check, not `absurd`/`nomatch`. `pos` is
  `SourceSpan.placeholder` at callers past the point a real position is still available
  (`NetworkPlusCal.Statement` carries none), matching `Guarded2Network`'s precedent. -/
  | internalInvariantViolated (pos : SourceSpan) (description : String)
  /-- A construct the Go backend cannot compile. Unlike `internalInvariantViolated` this is a real
  user-facing failure on well-formed, well-typed input: `Nat`/`Int` denote infinite sets no finite
  representation captures (§9.15), the `Bags` module has no runtime counterpart, and function
  equality would have to compare two lazy maps entry by entry. `construct` names what was written,
  `reason` says why it cannot be compiled. -/
  | unsupported (pos : SourceSpan) (construct : String) (reason : String)
  deriving Repr, Inhabited, BEq

instance : CompilerDiagnostic N2GError String where
  isError := true
  posOf
    | .internalInvariantViolated pos _ | .unsupported pos _ _ => pos
  msgOf
    | .internalInvariantViolated _ description =>
      s!"Internal invariant violated: {description}. This should be unreachable — please report this as a bug."
    | .unsupported _ construct reason =>
      s!"'{construct}' cannot be compiled to Go: {reason}."

end
