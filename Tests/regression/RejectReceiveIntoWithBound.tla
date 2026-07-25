---- MODULE RejectReceiveIntoWithBound ----
\* Expect: rejected, `DesugarError.withBoundVarWritten`. `receive`'s target `Ref` writes a
\* received value into a variable the same way `assign` writes into its target, so
\* receiving into a `with`-bound name must be rejected too, for the same reason as a direct
\* assignment (`reject_assign_to_with_bound.tla`).

(*--algorithm RejectReceiveIntoWithBound {
    fifos (* @type: Channel(Str); *) ch;
    process (P = 0) {
    p1: with (x = "") {
            receive(ch, x);
        };
        goto p1;
    }
}*)

====
