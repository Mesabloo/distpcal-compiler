---- MODULE AcceptMultiBinderWithDesugarsToChain ----
\* Expect: accepted. A multi-binder `with (x = e1, y = e2, ...) { B }` desugars to a nested
\* chain of single-binder `with`s (`with (x = e1) { with (y = e2) { B } } }`) --
\* `CorePlusCal.Statement.with` only ever binds one variable at a time, by construction
\* (`Core/CorePlusCal/Syntax.lean`'s module doc).
\*
\* Every binder is `=`, so that this stays an acceptance end to end: a `\in` binder desugars the
\* same way but the Go backend refuses it (thesis §7.2.3.1 rejects set-valued `with` outright),
\* which `RejectWithSetBinderInGo.tla` pins separately.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMultiBinderWithDesugarsToChain {
    process (P = PID) {
    p1: with (x = 3, y = 4, z = 5) {
          print x + y + z;
        };
        goto Done;
    }
}*)

====
