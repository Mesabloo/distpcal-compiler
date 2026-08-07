---- MODULE RejectReceiveTwoChannels ----
\* Expect: rejected, WellFormednessError.receiveChannelMismatch. `Guarded2Network` compiles every
\* `receive` of a process into reads off one shared `inbox` sequence, fed by a `.rx` thread per
\* channel -- so a process receiving from two channels loses track of which channel a message came
\* from, and `Head(inbox)` can hand the `receive(chB, ...)` a message that arrived on `chA`. Both
\* receives type-check fine on their own; well-formedness is what rejects the pair.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectReceiveTwoChannels {
    fifos
        \* @type: Channel(Int);
        chA,
        \* @type: Channel(Int);
        chB;
    process (P = PID)
        variables
        \* @type: Int;
        x = 0,
        \* @type: Int;
        y = 0;
    {
    p1: receive(chA, x);
        goto p2;
    p2: receive(chB, y);
        goto Done;
    }
}*)

====
