---- MODULE RejectGlobalPlusCalVariable ----
\* Expect: rejected, WellFormednessError.globalPlusCalVariable (check 2(d)). The algorithm's own
\* `variables` keyword declares state shared across all processes, which isn't allowed -- only
\* `fifos` may appear at algorithm level. (`Process.localState.variables`, genuine per-process
\* state, is untouched by this check -- see accept_channel_via_send_receive.tla and every other
\* fixture that already uses process-local `variable`/`variables`.)

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectGlobalPlusCalVariable {
    variables x = 0;
    process (P = PID) {
    p1: skip;
    }
}*)

====
