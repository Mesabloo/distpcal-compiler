---- MODULE AcceptReExportedNaturalsViaFiniteSets ----
\* Expect: accepted, all the way through Go code generation. The `EXTENDS FiniteSets` surface of
\* the re-export bug `AcceptReExportedNaturalsViaSequences` covers. `FiniteSets` `EXTENDS`
\* *both* `Naturals` and `Sequences`, so `<` arrives here through two re-export hops of different
\* lengths and still has to come out `Naturals!<`.
\* `Cardinality` is `FiniteSets`'s own declaration, in the same expression, to pin down that
\* re-exported and own declarations of one module are tagged differently rather than uniformly.

EXTENDS FiniteSets

CONSTANTS
    \* @type: Set(Address);
    Nodes

(*--algorithm AcceptReExportedNaturalsViaFiniteSets {
    process (node \in Nodes)
        variables
            \* @type: Int;
            clock = 0;
    {
    p1: await clock < Cardinality(Nodes) + 3;
        clock := clock + 1;
        goto Done;
    }
}*)

====
