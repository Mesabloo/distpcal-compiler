---- MODULE RejectChannelElementOperator ----
\* Expect: rejected, TCError.notSendable. An operator value has no runtime representation to
\* send between processes -- `sendable`'s exclusion list bans it, same as `showable` does for
\* `print`.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectChannelElementOperator {
    fifos
        \* @type: Channel((Int) => Int);
        ch;
    process (P = PID) {
    p1: skip;
    }
}*)

====
