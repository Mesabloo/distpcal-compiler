---- MODULE AcceptMultiIndexRefDesugarsToTuple ----
\* Expect: accepted. `CorePlusCal.Ref` is unary per bracket group, same rule as `CoreTLAPlus.
\* Expression.fnCall`/`.except`: `f[e1, e2] := v` (one bracket group, two indices) desugars to
\* `f[<<e1, e2>>] := v`; `f[e1][e2] := v` (two separate bracket groups) stays two separate
\* single-index groups, not one tuple; `f[e] := v` (one index) stays exactly that.

(*--algorithm AcceptMultiIndexRefDesugarsToTuple {
    variables f = [n \in {1, 2} |-> [m \in {1, 2} |-> n + m]];
    process (P = 0) {
    p1: f[1] := 0;
        goto p2;
    p2: f[1, 2] := 9;
        goto p3;
    p3: f[1][2] := 3;
        goto Done;
    }
}*)

====
