---- MODULE RejectSequentialAssignSameVariable ----
\* Expect: rejected. `x := 4; x := 0` writes the same bare variable twice within one atomic
\* step, even though the two assigns are separate (sequential, not `||`) statements
\* (`PLAN.md` §5.2a).

(*--algorithm RejectSequentialAssignSameVariable {
    variables x = 0;
    process (P = 0) {
    p1: x := 4;
        x := 0;
        goto Done;
    }
}*)

====
