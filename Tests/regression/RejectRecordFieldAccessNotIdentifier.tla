---- MODULE RejectRecordFieldAccessNotIdentifier ----
\* Expect: rejected, `DesugarError.invalidRecordFieldAccess` (`Desugarer/TLAPlus.lean`'s
\* `Expression.desugar`, the `.infixCall _ .«.» _` catch-all -- everything not matched by the
\* preceding `.infixCall e1 .«.» (.var x)` case). `.` parses as an ordinary infix operator, so
\* `r.(1)` is syntactically fine at the parser level; the desugarer is what rejects a
\* right-hand side that isn't a bare field-name identifier. Purely syntactic -- fires regardless
\* of `r`'s type, unlike `reject_record_access_on_non_record.tla`/`reject_unknown_record_field.tla`
\* (both type errors on an otherwise well-formed `r.name` access).

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectRecordFieldAccessNotIdentifier {
    variable r = [a |-> 1];
    process (P = PID) {
    p1: print r.(1);
        goto Done;
    }
}*)

====
