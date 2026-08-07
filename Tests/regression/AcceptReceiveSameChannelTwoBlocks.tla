---- MODULE AcceptReceiveSameChannelTwoBlocks ----
\* Expect: accepted. The receive-channel restriction is one channel per *process*, not one
\* `receive` per process (`RejectReceiveSameChannelTwice.tla` covers the separate rule that two
\* receives may not share one *atomic step*): two receives naming the same channel share one `.rx` thread and one
\* `inbox`, and FIFO order is exactly what makes the second read the second message. Also covers
\* the nested case -- the second `receive` sits inside an `either`, which `Statement.forEachNode`
\* has to reach for the check to see it at all.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptReceiveSameChannelTwoBlocks {
    fifos
        \* @type: Channel(Int);
        ch;
    process (P = PID)
        variables
        \* @type: Int;
        x = 0,
        \* @type: Int;
        y = 0;
    {
    p1: receive(ch, x);
        goto p2;
    p2: either { receive(ch, y); }
        or { skip; };
        goto Done;
    }
}*)

====
