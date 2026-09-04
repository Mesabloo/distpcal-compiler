---- MODULE RejectFairWithoutProcess ----
\* Expect: rejected at the parser, `E0002`, and **no** `W0001` (`fair`-ignored) warning.
\*
\* `parseProcess`'s `fair` probe (`test (token .fair)` then `warnIfFair`) is atomic through the
\* `process` keyword, so a stray `fair` with nothing after it rolls the warning back with the
\* position when the branch is abandoned.

(*--algorithm RejectFairWithoutProcess {
    process (P = 1) { l1: skip; }
    fair
}*)
====
