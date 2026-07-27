---- MODULE AcceptInVariableWithoutParameter ----
\* Expect: accepted, all the way to Go, and the emitted Go must compile. An `\in`-initialized
\* process-local carrying no `@parameter` starts at an element of its set chosen at
\* initialization -- `tlaplus.Pick(S)`. The backend used to reject every `\in` initializer
\* outright, so this whole shape was unreachable even though the desugarer had always accepted it
\* (the `@parameter`-only rule is about `=`, see RejectParameterOnEqualsVariable.tla).
\*
\* The set is a CONSTANT rather than a literal so that the emitted Go names something the
\* compiler does not define -- which is what `_stubs/AcceptInVariableWithoutParameter.go` is for,
\* and what keeps that mechanism exercised.

EXTENDS Integers

CONSTANTS
    \* @type: Address;
    PID,
    \* @type: Set(Int);
    Vals

(*--algorithm AcceptInVariableWithoutParameter {
    process (P = PID)
        variable x \in Vals;
    {
    p1: x := x + 1;
        goto Done;
    }
}*)

====
