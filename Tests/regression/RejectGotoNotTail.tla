---- MODULE RejectGotoNotTail ----
\* Expect: rejected, `DesugarError.gotoNotInTailPosition`. A `goto` immediately followed
\* by more, unlabelled statements is unreachable dead code, not something to route
\* around — `print x` here can never execute and is rejected rather than silently kept.

(*--algorithm RejectGotoNotTail {
    variable x = 0;
    process (P = 0) {
    p1: goto p1;
        print x;
    }
}*)

====
