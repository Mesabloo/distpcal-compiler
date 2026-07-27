---- MODULE AcceptReExportedNaturalsViaSequences ----
\* Expect: accepted, all the way through Go code generation. `<` and `+` are declared by
\* `Naturals` and reach this module twice over: directly, and re-exported through `Sequences`
\* (`Sequences` itself `EXTENDS Naturals`). Whichever path wins the merge, the operator must keep
\* the `Origin` of the module that *declared* it -- `Naturals!<`, never `Sequences!<`.
\* An operator tagged with a re-exporting module is not merely mislabelled: `builtinOpOf?`
\* (`Core/TypedTLAPlus/Builtins.lean`) and `compileBuiltinCall` (`Network2Go/Expression.lean`)
\* both dispatch on `(module, name)`, so a wrong module name matches no arm and code generation
\* fails with an internal-invariant error (`E0060`).
\* Reaching code generation is therefore the point of the fixture -- the type checker accepts the
\* mistagged operator perfectly happily, which is why
\* `AcceptSequencesExtendsNaturalsTransitively`, having no algorithm and so stopping at
\* `computable`, never caught this.
\* Regression-covers `Driver/Modules.lean`'s `ResolvedDep.bindings`: a dependency reports the
\* bindings it brings into scope already origin-tagged, rather than having the caller re-derive
\* them from a declaration list that has lost track of who declared what.

EXTENDS Naturals, Sequences

CONSTANTS
    \* @type: Set(Address);
    Nodes

(*--algorithm AcceptReExportedNaturalsViaSequences {
    process (node \in Nodes)
        variables
            \* @type: Int;
            clock = 0,
            \* @type: Seq(Int);
            log = <<>>;
    {
    p1: await clock < Len(log) + 3;
        clock := clock + 1;
        log := Append(log, clock);
        goto Done;
    }
}*)

====
