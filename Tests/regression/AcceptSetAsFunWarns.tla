---- MODULE AcceptSetAsFunWarns ----
\* Expect: accepted, all the way to Go, and the emitted Go must compile. `SetAsFun(S)` reads a
\* set of pairs as the function whose graph it is -- undefined (via Apalache) when two pairs
\* share a first component, so the generated program aborts there. Every use raises W0008
\* (`-Wunsafe`); `-Wno-unsafe` silences it.
\*
\* `EXTENDS Fugue` alone: the `1..1` range comes from `Naturals`, which `Fugue` extends.

EXTENDS Fugue

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptSetAsFunWarns {
    process (P = PID)
        variables
            \* @type: Set(<<Int, Int>>);
            pairs = {<<1, 10>>, <<2, 20>>},
            \* @type: Int -> Int;
            g = [i \in 1..1 |-> 0];
    {
    p1: g := SetAsFun(pairs);
        assert g[2] = 20;
        goto Done;
    }
}*)

====
