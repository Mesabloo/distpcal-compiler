---- MODULE RejectTransitiveTemporal ----
\* Expect: rejected, WellFormednessError.bareTemporalOrAction (check 3, transitive), naming a
\* path through `IsStable` -- the algorithm never writes `[]`/`<>`/etc. directly, only calls
\* `IsStable(x)` (defined in `AcceptDepModuleTemporalOperator`, EXTENDS-ed here), whose own body
\* does. Exercises the one part of check 3 that needs the transitive walker, not just the direct
\* per-node match (reject_bare_temporal.tla covers the direct case).

EXTENDS AcceptDepModuleTemporalOperator

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectTransitiveTemporal {
    process (P = PID)
        variable x = 0;
    {
    p1: assert IsStable(x);
        goto Done;
    }
}*)

====
