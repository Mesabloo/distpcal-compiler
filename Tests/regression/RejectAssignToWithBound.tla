---- MODULE RejectAssignToWithBound ----
\* Expect: rejected, `DesugarError.withBoundVarWritten`. A `with`-bound name is a local
\* binding to a fixed value, not a process variable with state to update, so assigning to
\* it directly (`with (x = 3) { x := 9; }`) is meaningless and must be rejected.

(*--algorithm RejectAssignToWithBound {
    variable y = 0;
    process (P = 0) {
    p1: with (x = 3) {
            x := 9;
        };
        goto p1;
    }
}*)

====
