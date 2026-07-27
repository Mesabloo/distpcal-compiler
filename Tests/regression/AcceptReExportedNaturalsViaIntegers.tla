---- MODULE AcceptReExportedNaturalsViaIntegers ----
\* Expect: accepted, all the way through Go code generation. The `EXTENDS Integers` surface of the
\* same re-export bug `AcceptReExportedNaturalsViaSequences` covers: `Integers` `EXTENDS Naturals`
\* and declares only `Int` itself, so every arithmetic operator a module gets from `EXTENDS
\* Integers` alone is re-exported, and must stay tagged `Naturals` rather than `Integers`.
\* `Int` itself is deliberately not referenced: it denotes an infinite set, which this compiler's
\* finite-sets assumption has no runtime representation for.

EXTENDS Integers

CONSTANTS
    \* @type: Set(Address);
    Nodes

(*--algorithm AcceptReExportedNaturalsViaIntegers {
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
