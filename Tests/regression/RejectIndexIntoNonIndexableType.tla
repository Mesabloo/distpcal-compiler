---- MODULE RejectIndexIntoNonIndexableType ----
\* Expect: rejected, `TCError.notIndexable` (`Elaborator/Expressions.lean`'s `indexInto`, the
\* fallback case). `5[1]` requires `5`'s type to be a `Function`/`Seq`/`Tuple` -- `Int` is none
\* of those.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectIndexIntoNonIndexableType {
    process (P = PID) {
    p1: print 5[1];
        goto Done;
    }
}*)

====
