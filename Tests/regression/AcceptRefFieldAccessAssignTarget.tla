---- MODULE AcceptRefFieldAccessAssignTarget ----
\* Expect: accepted. `Ref.args` now supports `.field` segments interleaved with bracket-index
\* groups, not just indices -- checkpoint 0a's `Ref` field-access prerequisite for
\* `Typed2Guarded`. `r.a := e` assigns into a record field through a `Ref` (not a plain
\* expression), exercising `parseRef`'s new `.`-segment parsing, `Ref.desugarRef`'s passthrough
\* of `.inl` segments, and `inferRef`'s reuse of `Elaborator/Expressions.lean`'s `stepInto` for
\* the `.inl` typing case. `r.b[1] := e` chains a field step into an index step on the same `Ref`.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptRefFieldAccessAssignTarget {
    process (P = PID)
        variable r = [a |-> 1, b |-> [n \in {1, 2} |-> 0]];
    {
    p1: r.a := 2;
        goto p2;
    p2: r.b[1] := 9;
        goto Done;
    }
}*)

====
