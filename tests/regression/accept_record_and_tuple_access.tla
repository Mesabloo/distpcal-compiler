---- MODULE AcceptRecordAndTupleAccess ----
\* Expect: accepted. `r : [a : Int, b : <<Int, Int>>]`, synthesized from its literal initializer;
\* `r.a` is ordinary record-field access (`[Record field access]`), and `r.b[1]` chains a record
\* field step into a tuple-index step (`Elaborator/Expressions.lean`'s `stepInto`/`indexInto`).
\* No existing fixture combines the two accesses on the same value.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptRecordAndTupleAccess {
    process (P = PID)
        variable r = [a |-> 1, b |-> <<2, 3>>];
    {
    p1: print r.a;
        goto p2;
    p2: print r.b[1];
        goto Done;
    }
}*)

====
