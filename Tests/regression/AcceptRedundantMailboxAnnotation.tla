---- MODULE AcceptRedundantMailboxAnnotation ----
\* Expect: accepted. Two `@mailbox` annotations naming the *same* channel genuinely
\* disagree about nothing -- redundant, not ambiguous. Only a real conflict (a *different*
\* channel) is an error (`reject_duplicate_mailbox_annotation.tla`). The process receives on `ch`,
\* so that what the two annotations agree on is a mailbox that survives the well-formedness pass --
\* an unused one is dropped with a warning (`AcceptUnusedMailboxWarns.tla`).

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptRedundantMailboxAnnotation {
    fifos (* @type: Channel(Str); *) ch;

    (* @mailbox: ch; *) (* @mailbox: ch; *) process (P = PID)
        variable
            \* @type: Str;
            x = "";
    {
    p1: receive(ch, x);
    }
}*)

====
