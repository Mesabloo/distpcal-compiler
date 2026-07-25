---- MODULE RejectGlobalTlaplusVariable ----
\* Expect: rejected, WellFormednessError.globalTLAPlusVariable (check 2(c)). Referencing a
\* module-level `VARIABLE` from inside the algorithm is banned outright -- a Distributed PlusCal
\* process must compile to a fully separate unit with no shared memory, and a TLA+ `VARIABLE` is
\* exactly the kind of implicit shared state that breaks that assumption.

VARIABLE
    \* @type: Int;
    V

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectGlobalTlaplusVariable {
    process (P = PID) {
    p1: assert V = V;
        goto Done;
    }
}*)

====
