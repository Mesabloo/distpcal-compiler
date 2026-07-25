---- MODULE RejectMailboxOnTypeSite ----
\* Expect: rejected, `DesugarError.wrongAnnotationKindAtSite`. `@mailbox` only makes sense
\* immediately before a `process` declaration — attaching it to an ordinary variable
\* declaration (a `@type`-only site) must be rejected.

(*--algorithm RejectMailboxOnTypeSite {
    variable (* @mailbox: foo; *) x = 0;
    process (P = 0) {
    p1: skip;
    }
}*)

====
