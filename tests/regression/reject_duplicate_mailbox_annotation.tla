---- MODULE RejectDuplicateMailboxAnnotation ----
\* Expect: rejected, `DesugarError.duplicateAnnotation`. Two `@mailbox` annotations on the
\* same process are genuinely ambiguous (which channel is the real mailbox?), not merely
\* redundant -- unlike `@parameter`, `@mailbox` carries real content that can actually
\* disagree between instances.

(*--algorithm RejectDuplicateMailboxAnnotation {
    fifos (* @type: Channel(Str); *) ch1, (* @type: Channel(Str); *) ch2;

    (* @mailbox: ch1; *) (* @mailbox: ch2; *) process (P = 0) {
    p1: skip;
    }
}*)

====
