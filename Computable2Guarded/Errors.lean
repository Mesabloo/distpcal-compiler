module

public import Common.Errors
public import Core.TypedTLAPlus.Syntax

public section

/-! `Computable2Guarded`'s diagnostics — a single defense-in-depth catch-all, mirroring
`Typed2Computable/Errors.lean:34`'s `ComputableError.internalInvariantViolated` exactly. Every
case this pass can hit is "should be impossible given upstream guarantees" (e.g. `𝒞_cflow`
finding a `while` not at block-front, or `𝒞_reord`'s final precondition/action split finding an
action-class statement still ahead of a guard-class one after its walk claims to have
finished) — no genuinely new user-facing restriction is introduced by this pass itself. -/

/-- `Computable2Guarded`'s errors. -/
inductive GuardedError : Type
  /-- Defense-in-depth: an input shape this pass's own invariants guarantee can't occur (e.g. a
  `while` not immediately preceded by a labelled block, per §5.2a) still turned up. No proof of
  unreachability exists for any of these yet — just facts established by earlier passes — so
  this stays a runtime check, not `absurd`/`nomatch`. `pos` is `SourceSpan.placeholder` at
  callers past the point where a real position is still available (`ElaboratedPlusCal`/
  `GuardedPlusCal.Statement` carry none), matching `Typed2Computable.lean`'s own precedent. -/
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
