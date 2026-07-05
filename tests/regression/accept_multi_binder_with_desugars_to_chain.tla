---- MODULE AcceptMultiBinderWithDesugarsToChain ----
\* Expect: accepted. A multi-binder `with (x = e1, y \in e2, ...) { B }` desugars to a nested
\* chain of single-binder `with`s (`with (x = e1) { with (y \in e2) { B } } }`) --
\* `CorePlusCal.Statement.with` only ever binds one variable at a time, by construction
\* (`Core/CorePlusCal/Syntax.lean`'s module doc).

(*--algorithm AcceptMultiBinderWithDesugarsToChain {
    process (P = 0) {
    p1: with (x = 3, y \in {1, 2}, z = 5) {
          print x + y + z;
        };
        goto Done;
    }
}*)

====
