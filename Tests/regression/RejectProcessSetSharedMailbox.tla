---- MODULE RejectProcessSetSharedMailbox ----
\* Expect: rejected, WellFormednessError.mailboxNotIndexedBySelf. `process (P \in PIDs)` declares
\* one instance per element of `PIDs`, and `receive(ch, x)` names the same FIFO in all of them --
\* so two instances race for the same messages, and `Guarded2Network`'s per-process `inbox` can no
\* longer account for what left the channel. Indexing by `self` (`ch[self]`) gives each instance
\* its own FIFO, which is what the compilation assumes. A `=`-shaped process needs no index, since
\* it has exactly one instance (`RejectReceiveTwoChannels.tla` covers the separate rule that no
\* process may receive from two channels at all). The `@mailbox` declaration is present so that
\* this is the *only* thing wrong with the module: a receiving process without one is rejected by
\* `receiveWithoutMailbox` instead (`RejectReceiveWithoutMailbox.tla`).

CONSTANTS
    \* @type: Set(Address);
    PIDs

(*--algorithm RejectProcessSetSharedMailbox {
    fifos
        \* @type: Channel(Int);
        ch;
    (* @mailbox: ch; *) process (P \in PIDs)
        variables
        \* @type: Int;
        x = 0;
    {
    p1: receive(ch, x);
        goto Done;
    }
}*)

====
