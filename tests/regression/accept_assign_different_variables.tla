---- MODULE AcceptAssignDifferentVariables ----
\* Expect: accepted. `x := 3; y := 4` writes two different variables in the same atomic step --
\* no conflict.

(*--algorithm AcceptAssignDifferentVariables {
    variables x = 0, y = 0;
    process (P = 0) {
    p1: x := 3;
        y := 4;
        goto Done;
    }
}*)

====
