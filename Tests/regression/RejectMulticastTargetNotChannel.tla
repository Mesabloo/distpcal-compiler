---- MODULE RejectMulticastTargetNotChannel ----
\* Expect: rejected, `TCError.notAChannelType` (`Elaborator/PlusCal.lean`'s `[Multicast]` case,
\* the `some got => throw (.notAChannelType ...)` branch). `multicast(x, ...)` requires `x` to be
\* bound at `_ -> Channel(_)` in `Gamma` -- `x` here is an ordinary `Int` variable.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectMulticastTargetNotChannel {
    variable x = 0;
    process (P = PID) {
    p1: multicast(x, [y \in {PID} |-> 1]);
        goto Done;
    }
}*)

====
