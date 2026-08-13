---- MODULE RejectReceiveWithoutMailbox ----
\* Expect: rejected, WellFormednessError.receiveWithoutMailbox. A process that receives must say
\* which channel it listens on: `Guarded2Network` compiles every `receive` into reads off one
\* `inbox` per process instance, and which channel that `inbox` stands for is what the refinement
\* proof's per-process mailbox is. Adopting the first `receive`'s channel instead would make that
\* depend on statement order rather than on anything the source declares, so the annotation is
\* required. The mirror case -- a `@mailbox` no `receive` uses -- is only a warning
\* (`AcceptUnusedMailboxWarns.tla`).

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectReceiveWithoutMailbox {
    fifos
        \* @type: Channel(Int);
        ch;
    process (P = PID)
        variables
        \* @type: Int;
        x = 0;
    {
    p1: receive(ch, x);
        goto Done;
    }
}*)

====
