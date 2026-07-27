---- MODULE AcceptParameterBoundNamesEarlierLocal ----
\* Expect: accepted, all the way to Go. A `@parameter`'s value is supplied by the caller, as a
\* parameter of the generated process function, and its declared bound becomes an assertion. The
\* assertion is emitted at the *declaration's* position rather than at function entry, so a bound
\* may name a local declared before it: `limit` has a Go local by the time `start \in 1..limit`
\* is checked.
\*
\* Asserting everything up front would have had to reject this, and would also report a worse
\* error for the mirror case -- a later initializer that panics on the very parameter value the
\* assertion exists to reject.

EXTENDS Integers

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptParameterBoundNamesEarlierLocal {
    process (P = PID)
        variables
            limit = 3,
            \* @parameter
            start \in 1..limit;
    {
    p1: skip;
        goto Done;
    }
}*)

====
