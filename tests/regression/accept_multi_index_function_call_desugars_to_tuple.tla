---- MODULE AcceptMultiIndexFunctionCallDesugarsToTuple ----
\* Expect: accepted. `CoreTLAPlus.Expression.fnCall` is always unary -- a surface multi-index
\* call `f[e1, e2]` desugars to `f[<<e1, e2>>]`, while a single-index call `f[e]` stays exactly
\* that (never `f[<<e>>]`). Same rule for `EXCEPT`'s `![...]` index steps.
\* One variable per bracket shape (`f1`/`f2`) -- a single variable can't be genuinely well-typed
\* for both a single-index and a tuple-index access at once, and the Phase 5 type checker now
\* enforces that.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMultiIndexFunctionCallDesugarsToTuple {
    variables
        f1 = [n \in {1, 2} |-> n],
        f2 = [p \in {<<1, 2>>} |-> 0];
    process (P = PID) {
    p1: print f1[1];
        print f2[1, 2];
        f1 := [f1 EXCEPT ![1] = 9];
        goto p2;
    p2: f2 := [f2 EXCEPT ![1, 2] = 9];
        goto Done;
    }
}*)

====
