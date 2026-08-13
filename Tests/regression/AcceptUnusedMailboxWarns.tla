---- MODULE AcceptUnusedMailboxWarns ----
\* Expect: accepted with W0007. A `@mailbox` on a process containing no `receive` says nothing
\* wrong about the program -- it just has no effect -- so it warns rather than rejects, and the
\* field is dropped. Dropping it is what makes `Process.mailbox` total on receiving processes:
\* after well-formedness it is `.some c` exactly when the process receives, and `c` is the channel
\* it receives on, which is what `Guarded2Network`'s per-process `inbox` is indexed by. The
\* opposite case -- a `receive` with no declaration -- is an error
\* (`RejectReceiveWithoutMailbox.tla`).

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptUnusedMailboxWarns {
    fifos
        \* @type: Channel(Int);
        ch;
    (* @mailbox: ch; *) process (P = PID)
        variables
        \* @type: Int;
        x = 0;
    {
    p1: send(ch, 1);
        goto p2;
    p2: x := 1;
        goto Done;
    }
}*)

====
