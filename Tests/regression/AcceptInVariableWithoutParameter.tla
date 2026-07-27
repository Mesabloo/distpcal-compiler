---- MODULE AcceptInVariableWithoutParameter ----
\* Expect: accepted, all the way to Go. An `\in`-initialized process-local carrying no
\* `@parameter` starts at an element of its set chosen at initialization -- `tlaplus.Pick(S)`.
\* The backend used to reject every `\in` initializer outright, so this whole shape was
\* unreachable even though the desugarer had always accepted it (the `@parameter`-only rule is
\* about `=`, see RejectParameterOnEqualsVariable.tla).

EXTENDS Integers

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptInVariableWithoutParameter {
    process (P = PID)
        variable x \in {1, 2, 3};
    {
    p1: x := x + 1;
        goto Done;
    }
}*)

====
