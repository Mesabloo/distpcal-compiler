---- MODULE RejectAssignThenReceiveSameVariable ----
\* Expect: rejected. `x := 3; receive(c, x)` writes `x` via `assign`, then again via `receive`'s
\* target, within the same atomic step -- `receive`'s target counts as a write, same as
\* `assign`'s (`PLAN.md` §5.2a).

(*--algorithm RejectAssignThenReceiveSameVariable {
    fifos c;
    variables x = 0;
    process (P = 0) {
    p1: x := 3;
        receive(c, x);
        goto Done;
    }
}*)

====
