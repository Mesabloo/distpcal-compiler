---- MODULE AcceptMultiIndexRefDesugarsToTuple ----
\* Expect: accepted. `CorePlusCal.Ref` is unary per bracket group, same rule as `CoreTLAPlus.
\* Expression.fnCall`/`.except`: `f[e1, e2] := v` (one bracket group, two indices) desugars to
\* `f[<<e1, e2>>] := v`; `f[e1][e2] := v` (two separate bracket groups) stays two separate
\* single-index groups, not one tuple; `f[e] := v` (one index) stays exactly that.
\* One variable per bracket shape (`f1`/`f2`/`f3`) -- a single variable can't be genuinely
\* well-typed for all three access shapes at once (single-index, tuple-index, and curried
\* access each imply a different domain), and the Phase 5 type checker now enforces that.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMultiIndexRefDesugarsToTuple {
    variables
        f1 = [n \in {1, 2} |-> 0],
        f2 = [p \in {<<1, 2>>} |-> 0],
        f3 = [n \in {1, 2} |-> [m \in {1, 2} |-> n + m]];
    process (P = PID) {
    p1: f1[1] := 0;
        goto p2;
    p2: f2[1, 2] := 9;
        goto p3;
    p3: f3[1][2] := 3;
        goto Done;
    }
}*)

====
