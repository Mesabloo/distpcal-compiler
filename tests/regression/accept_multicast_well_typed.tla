---- MODULE AcceptMulticastWellTyped ----
\* Expect: accepted. No existing fixture exercises `multicast` at all yet. `ch : Address ->
\* Channel(Int)` (an indexed channel declaration), and `multicast(ch, [y \in {PID} |-> 1])` checks
\* the bind's domain against `Set(Address)` (`ch`'s own function domain) and the mapped value `1`
\* against `ch`'s element type `Int` (`Elaborator/PlusCal.lean`'s `[Multicast]` case).

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMulticastWellTyped {
    fifos
        \* @type: Address -> Channel(Int);
        ch[{PID}];
    process (P = PID) {
    p1: multicast(ch, [y \in {PID} |-> 1]);
        goto Done;
    }
}*)

====
