---- MODULE AcceptWhileLabelledStep ----
\* Expect: accepted. A label may sit nested inside a `while` body (`l2`) — the desugarer
\* extracts it into its own top-level block, stitching `goto`s so `l2` loops back to `l1`
\* and falling out of the loop continues to `l3`. This is the project owner's own worked
\* example from the basic-block-extraction correction.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptWhileLabelledStep {
    process (P = PID)
        variable x = 3;
    {
    l1: while (x > 0) {
            print 1;
            await x > 0;
    l2:     print 2;
        };
        print 3;
    l3: skip;
        goto l1;
    }
}*)

====
