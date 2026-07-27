---- MODULE AcceptTransitiveExtendsThroughUserModule ----
\* Expect: accepted, all the way through Go code generation. `EXTENDS` is transitive through a
\* *user* module exactly as it is through a builtin: this module extends only
\* `AcceptDepModuleReExportsNaturals`, which extends `Naturals`, so `<` and `+` must be in scope
\* here without a second `EXTENDS Naturals`. Regression-covers `Driver/Modules.lean`'s
\* `resolveModule` `.file` case supplying `ResolvedDep.inherited`, which it used to leave empty.
\* Carries an algorithm so it reaches the Go backend: an inherited binding that arrived tagged
\* with the re-exporting module rather than `Naturals` type-checks fine and only fails there.

EXTENDS AcceptDepModuleReExportsNaturals

CONSTANTS
    \* @type: Set(Address);
    Nodes

(*--algorithm AcceptTransitiveExtendsThroughUserModule {
    process (node \in Nodes)
        variables
            \* @type: Int;
            clock = 0;
    {
    p1: await clock < Threshold;
        clock := clock + 1;
        goto Done;
    }
}*)

====
