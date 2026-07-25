---- MODULE RejectGlobalTlaplusVariableCrossModule ----
\* Expect: rejected, WellFormednessError.globalTLAPlusVariable (check 2(c)), naming
\* `AcceptDepModuleVariable` (not this module) as `V`'s origin -- exercises the cross-module half
\* of check 2(c)/`Origin.module`: a `VARIABLE` reachable only via `EXTENDS` is exactly as banned
\* as one declared directly in this module (reject_global_tlaplus_variable.tla covers the direct
\* case).

EXTENDS AcceptDepModuleVariable

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectGlobalTlaplusVariableCrossModule {
    process (P = PID) {
    p1: assert V = V;
        goto Done;
    }
}*)

====
