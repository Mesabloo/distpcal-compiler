---- MODULE AcceptDepModuleWithAlgorithm ----
\* Expect: accepted, standalone and warning-free -- an algorithm in the module you are compiling
\* is exactly what the compiler is for. Exists as an EXTENDS-ed dependency for
\* AcceptExtendsAlgorithmWarns, where the same algorithm is what W0006 fires on: the warning
\* belongs to the extending module's EXTENDS clause, never to this file.

EXTENDS Naturals

CONSTANTS
    \* @type: Set(Address);
    Workers

\* @type: Int;
Limit == 2

(*--algorithm AcceptDepModuleWithAlgorithm {
    process (worker \in Workers)
        variables
            \* @type: Int;
            done = 0;
    {
    w1: await done < Limit;
        done := done + 1;
        goto Done;
    }
}*)

====
