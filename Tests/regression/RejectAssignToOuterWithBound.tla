---- MODULE RejectAssignToOuterWithBound ----
\* Expect: rejected, `DesugarError.withBoundVarWritten`. `with`-bound names accumulate
\* across nesting, not just the innermost `with` — assigning to an *outer* `with`'s bound
\* name from within a nested `with`'s body must still be rejected.

(*--algorithm RejectAssignToOuterWithBound {
    variable z = 0;
    process (P = 0) {
    p1: with (x = 3) {
            with (y = 4) {
                x := 9;
            };
        };
        goto p1;
    }
}*)

====
