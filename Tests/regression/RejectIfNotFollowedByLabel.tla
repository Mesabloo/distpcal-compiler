---- MODULE RejectIfNotFollowedByLabel ----
\* Expect: rejected, `DesugarError.notFollowedByLabel`. The `if`'s then-branch has a
\* nested label (`p2`), so the `if` must be followed by a labelled statement
\* (PlusCal manual §3.2.2) — but `print 3` here has none. Real PlusCal's default
\* (non-`-label`) behavior rejects this rather than inventing a continuation label, and
\* this compiler matches that. The fixed, accepted counterpart is accept_if_nested_label.tla.

(*--algorithm RejectIfNotFollowedByLabel {
    variable x = 0;
    process (P = 0) {
    p1: if (x > 0) {
    p2:     print 1;
        } else {
            print 2;
        };
        print 3;
        goto p1;
    }
}*)

====
