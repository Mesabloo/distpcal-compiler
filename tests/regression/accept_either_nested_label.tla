---- MODULE AcceptEitherNestedLabel ----
\* Expect: accepted. Only one `either` branch has a nested label (`p2`); same extraction
\* and continuation-labeling treatment as `if`, generalized to `either`'s n-ary branches.
\* The continuation label `p3` is required in the source (not synthesized) — this compiler
\* never invents one.

(*--algorithm AcceptEitherNestedLabel {
    variable x = 0;
    process (P = 0) {
    p1: either {
    p2:     x := 1;
        } or {
            x := 2;
        };
    p3: print 3;
        goto p1;
    }
}*)

====
