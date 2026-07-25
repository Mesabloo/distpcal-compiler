---- MODULE RejectRecordAccessOnNonRecord ----
\* Expect: rejected, `TCError.notARecordType` (`Elaborator/Expressions.lean`'s `stepInto`,
\* the `.inl field` case). `n.f` requires `n`'s synthesized type to be a `Record`; here `n : Int`
\* (from its initializer), so field access on it is a type error, not a parse error -- `.` is a
\* perfectly ordinary infix operator syntactically (`RejectRecordFieldAccessNotIdentifier.tla`
\* covers the desugar-time syntactic restriction on `.`'s right-hand side).

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectRecordAccessOnNonRecord {
    variable n = 3;
    process (P = PID) {
    p1: print n.f;
        goto Done;
    }
}*)

====
