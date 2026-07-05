---- MODULE AcceptWithAssignOtherVar ----
\* Expect: accepted. A `with`-bound name may be freely *read* inside its own body, and
\* assigning to any other (non-with-bound) variable from within a `with` body is fine —
\* only assigning to the `with`-bound name itself is rejected.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptWithAssignOtherVar {
    variable y = 0;
    process (P = PID) {
    p1: with (x = 3) {
            y := x + 1;
        };
        goto p1;
    }
}*)

====
