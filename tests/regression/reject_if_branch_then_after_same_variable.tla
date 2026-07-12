---- MODULE RejectIfBranchThenAfterSameVariable ----
\* Expect: rejected. A write inside one `if` branch, followed by a write to the same variable
\* in whatever both branches converge to afterward, is a real conflict along the branch that
\* took it -- unlike two different branches writing the same variable (accepted,
\* `accept_if_branches_same_variable.tla`).

(*--algorithm RejectIfBranchThenAfterSameVariable {
    variables x = 0;
    process (P = 0) {
    p1: if (TRUE) {
            x := 1;
        } else {
            skip;
        };
        x := 2;
        goto Done;
    }
}*)

====
