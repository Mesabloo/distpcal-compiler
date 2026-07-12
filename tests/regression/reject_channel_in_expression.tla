---- MODULE RejectChannelInExpression ----
\* Expect: rejected, WellFormednessError.channelInExpression (check 1). A channel
\* reference may only appear as `send`'s/`receive`'s channel argument or `multicast`'s target --
\* referencing it inside an ordinary expression (`ch = ch`, which type-checks fine on its own
\* since `Channel` has decidable/reflexive equality) is banned by well-formedness instead.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectChannelInExpression {
    fifos
        \* @type: Channel(Int);
        ch;
    process (P = PID) {
    p1: assert ch = ch;
        goto Done;
    }
}*)

====
