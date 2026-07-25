---- MODULE RejectIfBranchesIncomparableTypes ----
\* Expect: rejected, `TCError.ambiguousType` (`Elaborator/Expressions.lean`'s `lubAll`, the
\* `none => throw (.ambiguousType pos)` branch reached via `[Conditional]`'s `lub(tau_t, tau_f)`).
\* `IF TRUE THEN 1 ELSE TRUE` synthesizes `Int` for the `THEN` branch and `Bool` for the `ELSE`
\* branch -- neither is a subtype of the other, so no least upper bound exists.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectIfBranchesIncomparableTypes {
    process (P = PID) {
    p1: print IF TRUE THEN 1 ELSE TRUE;
        goto Done;
    }
}*)

====
