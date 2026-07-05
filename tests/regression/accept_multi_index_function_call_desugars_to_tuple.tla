---- MODULE AcceptMultiIndexFunctionCallDesugarsToTuple ----
\* Expect: accepted. `CoreTLAPlus.Expression.fnCall` is always unary -- a surface multi-index
\* call `f[e1, e2]` desugars to `f[<<e1, e2>>]`, while a single-index call `f[e]` stays exactly
\* that (never `f[<<e>>]`). Same rule for `EXCEPT`'s `![...]` index steps.

(*--algorithm AcceptMultiIndexFunctionCallDesugarsToTuple {
    variables f = [n \in {1, 2} |-> n];
    process (P = 0) {
    p1: print f[1];
        print f[1, 2];
        f := [f EXCEPT ![1] = 9];
        goto p2;
    p2: f := [f EXCEPT ![1, 2] = 9];
        goto Done;
    }
}*)

====
