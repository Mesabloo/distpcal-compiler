---- MODULE RejectParallelAssignSameVariable ----
\* Expect: rejected. `x := 3 || x := 4` writes the same bare variable twice within one
\* `||`-list, i.e. the same atomic step.

(*--algorithm RejectParallelAssignSameVariable {
    variables x = 0;
    process (P = 0) {
    p1: x := 3 || x := 4;
        goto Done;
    }
}*)

====
