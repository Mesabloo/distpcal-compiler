---- MODULE RejectBareTemporal ----
\* Expect: rejected, WellFormednessError.bareTemporalOrAction (check 3, direct). `'` (prime) is
\* one of the eight reserved temporal/action operator spellings -- none may appear directly in a
\* statement the algorithm embeds. `x' = x` type-checks fine on its own (`'`'s builtinContext
\* entry, `(a) => a`), so this is purely a well-formedness rejection.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectBareTemporal {
    process (P = PID)
        variable x = 0;
    {
    p1: assert x' = x;
        goto Done;
    }
}*)

====
