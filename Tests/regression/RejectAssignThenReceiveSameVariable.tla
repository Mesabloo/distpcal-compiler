---- MODULE RejectAssignThenReceiveSameVariable ----
\* Expect: rejected. `x := 3; receive(c, x)` writes `x` via `assign`, then again via `receive`'s
\* target, within the same atomic step -- `receive`'s target counts as a write, same as
\* `assign`'s.
(*--algorithm RejectAssignThenReceiveSameVariable {
    fifos c;
    process (P = 0) 
    variables x = 0;
    {
    p1: x := 3;
        receive(c, x);
        goto Done;
    }
}*)
====
