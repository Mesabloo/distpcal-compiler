---- MODULE AcceptWhileLabelledInIfBranch ----
\* Expect: accepted. The `while` nested in the `if`'s then-branch has its own explicit
\* label (`p2`), and the continuation after the `if` is also explicitly labelled (`p3`) —
\* the fully-labelled counterpart to reject_while_not_labelled_in_if_branch.tla.

(*--algorithm AcceptWhileLabelledInIfBranch {
    variable x = 3;
    process (P = 0) {
    p1: if (x > 0) {
    p2:     while (x > 0) {
                x := x - 1;
            };
        } else {
            skip;
        };
    p3: goto p1;
    }
}*)

====
