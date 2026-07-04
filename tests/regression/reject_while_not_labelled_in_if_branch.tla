---- MODULE RejectWhileNotLabelledInIfBranch ----
\* Expect: rejected, `DesugarError.whileNotLabelled`. The `while` is the sole content of
\* the `if`'s then-branch, but being first inside a brace-delimited branch is not the same
\* thing as being immediately preceded by a real label — nothing labels this `while`. The
\* continuation after the `if` (`p2:`) is deliberately already labelled, to isolate this
\* error from `notFollowedByLabel` (see reject_if_not_followed_by_label.tla for that one).

(*--algorithm RejectWhileNotLabelledInIfBranch {
    variable x = 3;
    process (P = 0) {
    p1: if (x > 0) {
            while (x > 0) {
                x := x - 1;
            };
        } else {
            skip;
        };
    p2: goto p1;
    }
}*)

====
