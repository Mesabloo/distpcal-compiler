---- MODULE AcceptGotoDoneFallthrough ----
\* Expect: accepted. `p1`'s block runs out of statements with no explicit terminal
\* (`goto`/`goto Done`) — the desugarer must auto-insert `goto Done`, the reserved
\* sentinel for thread termination, rather than erroring.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptGotoDoneFallthrough {
    variable x = 0;
    process (P = PID) {
    p1: x := 1;
        print x;
    }
}*)

====
