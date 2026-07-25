---- MODULE AcceptWhileFreshReuse ----
\* Expect: accepted. The `while` is already the first (and only) statement of `p1`'s own
\* block — the canonical `lb: while … end while` shape — so the desugarer must reuse `p1`
\* directly as the loop's own loop-back target instead of synthesizing a fresh label.
\* Regression check for the fix in accept_while_nonfresh_extraction.tla.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptWhileFreshReuse {
    process (P = PID)
        variable x = 3;
    {
    p1: while (x > 0) {
            x := x - 1;
        };
        print 2;
        goto p1;
    }
}*)

====
