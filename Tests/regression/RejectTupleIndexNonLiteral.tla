---- MODULE RejectTupleIndexNonLiteral ----
\* Expect: rejected, `TCError.invalidTupleIndex` (`Elaborator/Expressions.lean`'s `indexInto`,
\* the `.tuple τs` case, non-`.nat` index branch). Unlike function/sequence access, tuple access
\* needs a literal index known at check time -- `<<1, 2>>[i]` can't pick which component's type
\* the result should be, even though `i : Int` at runtime.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectTupleIndexNonLiteral {
    variable i = 1;
    process (P = PID) {
    p1: print <<1, 2>>[i];
        goto Done;
    }
}*)

====
