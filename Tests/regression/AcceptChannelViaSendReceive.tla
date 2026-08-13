---- MODULE AcceptChannelViaSendReceive ----
\* Expect: accepted. A channel declared via `fifos`, used only through `send`/`receive`'s own
\* channel-argument position and an ordinary variable destination -- the legitimate way to use
\* one, matching every reject_channel_*/reject_receive_into_channel.tla fixture that shows what's
\* banned around it.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptChannelViaSendReceive {
    fifos
        \* @type: Channel(Int);
        ch;
    (* @mailbox: ch; *) process (P = PID)
        variable x = 0;
    {
    p1: send(ch, 1);
        goto p2;
    p2: receive(ch, x);
        goto Done;
    }
}*)

====
