---- MODULE RejectTupleIndexOutOfRange ----
\* Expect: rejected, `TCError.invalidTupleIndex` (`Elaborator/Expressions.lean`'s `indexInto`,
\* the `.tuple τs` / `.nat n` case). `<<1, 2>>` synthesizes as a 2-element tuple, so index `3`
\* is out of the required `1 <= i <= 2` range.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectTupleIndexOutOfRange {
    process (P = PID) {
    p1: print <<1, 2>>[3];
        goto Done;
    }
}*)

====
