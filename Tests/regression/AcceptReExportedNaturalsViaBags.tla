---- MODULE AcceptReExportedNaturalsViaBags ----
\* Expect: accepted, all the way through Go code generation. The `EXTENDS Bags` surface of the
\* re-export bug `AcceptReExportedNaturalsViaSequences` covers: `Bags` `EXTENDS TLC, Naturals`,
\* so `<`/`+` reach this module re-exported and must stay tagged `Naturals`, not `Bags`.
\* This one showed the bug as a *different* diagnostic than the other three -- `Bags!<` matches
\* `compileBuiltinCall`'s `Bags` arm, which reports `E0061` ("the Bags module has no runtime
\* representation") rather than `E0060` -- so it is worth its own fixture rather than being folded
\* into the `Integers` one.
\* No `Bags` operator is referenced, for the reason that `E0061` states: `Bags` has no runtime
\* representation, so its own declarations cannot reach Go at all. The re-exported `Naturals`
\* operators are the whole point here.

EXTENDS Bags

CONSTANTS
    \* @type: Set(Address);
    Nodes

(*--algorithm AcceptReExportedNaturalsViaBags {
    process (node \in Nodes)
        variables
            \* @type: Int;
            clock = 0;
    {
    p1: await clock < 3;
        clock := clock + 1;
        goto Done;
    }
}*)

====
