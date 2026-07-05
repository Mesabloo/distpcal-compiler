---- MODULE AcceptIfNestedLabel ----
\* Expect: accepted. Only the then-branch has a nested label (`p2`); the desugarer must
\* extract it and route both branches through the continuation label `p3` — which the
\* source itself already provides, since this compiler never invents one (see
\* reject_if_not_followed_by_label.tla for the same shape without that label).

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptIfNestedLabel {
    variable x = 0;
    process (P = PID) {
    p1: if (x > 0) {
    p2:     print 1;
        } else {
            print 2;
        };
    p3: print 3;
        goto p1;
    }
}*)

====
