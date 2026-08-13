---- MODULE RejectReceiveTwoChannels ----
\* Expect: rejected, WellFormednessError.receiveChannelMismatch. `Guarded2Network` compiles every
\* `receive` of a process into reads off one shared `inbox` sequence, fed by a `.rx` thread per
\* channel -- so a process receiving from two channels loses track of which channel a message came
\* from, and `Head(inbox)` can hand the `receive(chB, ...)` a message that arrived on `chA`. Both
\* receives type-check fine on their own; well-formedness is what rejects the pair. The `@mailbox`
\* declaration is what makes `chA` the reference channel, and is required of any receiving process
\* (`RejectReceiveWithoutMailbox.tla`) -- without it the first `receive` is already an error and
\* the mismatch this fixture is about is never reached.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectReceiveTwoChannels {
    fifos
        \* @type: Channel(Int);
        chA,
        \* @type: Channel(Int);
        chB;
    (* @mailbox: chA; *) process (P = PID)
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
