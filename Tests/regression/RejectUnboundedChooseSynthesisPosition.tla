---- MODULE RejectUnboundedChooseSynthesisPosition ----
\* Expect: rejected, `TCError.cannotInferType` (`Elaborator/Expressions.lean`, the
\* `.choose _ _ none _, pos => throw (.cannotInferType ...)` case: unbounded `CHOOSE` has no
\* synthesis rule at all, only a checking-mode one). `print e` gives its argument no expected type,
\* so `CHOOSE x : x = x` is synthesised, and there is no rule to synthesise it with -- `x`'s type
\* would have to come from somewhere, and nothing here supplies it.
\*
\* This fixture was parked as `Skip*` while `CHOOSE` had no parser production at all (§9.2), which
\* made it fail at `parse` and never reach the type checker. `parseChoose` exists now, so it reaches
\* the intended rejection and is a live `Reject*` again. See
\* `RejectUnboundedChooseWithExpectedType` for the checking-position counterpart, which types fine
\* and is rejected one stage later, by well-formedness check 3.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectUnboundedChooseSynthesisPosition {
    process (P = PID) {
    p1: print CHOOSE x : x = x;
        goto Done;
    }
}*)

====
