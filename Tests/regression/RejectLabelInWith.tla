---- MODULE RejectLabelInWith ----
\* Expect: rejected, `DesugarError.nestedLabel`. A `with` body may never contain a
\* labeled statement (PlusCal manual §3.2.6) — `with`'s binding only makes sense within
\* one atomic step, so execution can never pause/reschedule in its middle.

(*--algorithm RejectLabelInWith {
    variable x = 0;
    process (P = 0) {
    p1: with (y = 1) {
    p2:     x := y;
        };
        goto p1;
    }
}*)

====
