---- MODULE AcceptExtendsAlgorithmWarns ----
\* Expect: accepted with W0006 -- `AcceptDepModuleWithAlgorithm` carries a PlusCal algorithm, and
\* EXTENDS imports declarations only, so that algorithm is silently dropped. The warning is
\* reported here, under the identifier in this module's EXTENDS clause, not in the dependency's
\* own file: the dependency is well-formed on its own, and this clause is what would have to
\* change. `Limit`, an ordinary declaration of the same module, still comes across.

EXTENDS AcceptDepModuleWithAlgorithm

CONSTANTS
    \* @type: Set(Address);
    Nodes

(*--algorithm AcceptExtendsAlgorithmWarns {
    process (node \in Nodes)
        variables
            \* @type: Int;
            clock = 0;
    {
    p1: await clock < Limit;
        clock := clock + 1;
        goto Done;
    }
}*)

====
