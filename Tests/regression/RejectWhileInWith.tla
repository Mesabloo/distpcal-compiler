---- MODULE RejectWhileInWith ----
\* Expect: rejected, `DesugarError.whileInWith`. A `while` may never appear inside a
\* `with` body at any nesting depth (PlusCal manual §3.2.6) — independent of `nestedLabel`,
\* since this `while` carries no label of its own anywhere near it.

(*--algorithm RejectWhileInWith {
    variable x = 3;
    process (P = 0) {
    p1: with (y = 1) {
            while (x > 0) {
                skip;
            };
        };
        goto p1;
    }
}*)

====
