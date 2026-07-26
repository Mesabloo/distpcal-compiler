---- MODULE RejectWithSetBinderInGo ----
\* Expect: rejected, at the Go backend rather than any earlier stage. A set-valued
\* `with (y \in e) { B }` type-checks and desugars like any other `with`, but has no compilation:
\* choosing an element of `e` that satisfies the branch's remaining guards is a search, and
\* thesis §7.2.3.1 rejects the construct outright rather than deferring it ("we choose not to
\* support such constructs as they do not necessarily carry much computational meaning anyway").
\*
\* This is a permanent rejection, not an unimplemented case -- the counterpart acceptance
\* fixture, `AcceptMultiBinderWithDesugarsToChain.tla`, uses only `=` binders for that reason.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectWithSetBinderInGo {
    process (P = PID) {
    p1: with (y \in {1, 2}) {
          print y;
        };
        goto Done;
    }
}*)

====
