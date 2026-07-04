---- MODULE AcceptRedundantMailboxAnnotation ----
\* Expect: accepted. Two `@mailbox` annotations naming the *same* channel genuinely
\* disagree about nothing -- redundant, not ambiguous. Only a real conflict (a *different*
\* channel) is an error (`reject_duplicate_mailbox_annotation.tla`).

(*--algorithm AcceptRedundantMailboxAnnotation {
    fifos (* @type: Channel(Str); *) ch;

    (* @mailbox: ch; *) (* @mailbox: ch; *) process (P = 0) {
    p1: skip;
    }
}*)

====
