---- MODULE RejectUnknownRecordField ----
\* Expect: rejected, `TCError.unknownField` (`Elaborator/Expressions.lean`'s `stepInto`, the
\* `.inl field` case, `fs.lookup field = none` branch). `[a |-> 1]` synthesizes as `[a : Int]`,
\* which has no `b` field.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectUnknownRecordField {
    process (P = PID) {
    p1: print [a |-> 1].b;
        goto Done;
    }
}*)

====
