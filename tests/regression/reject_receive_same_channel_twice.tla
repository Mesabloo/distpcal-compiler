---- MODULE RejectReceiveSameChannelTwice ----
\* Expect: rejected. `receive(x, a); receive(x, b)` reads from the same channel `x` twice
\* within one atomic step -- the channel argument counts as a write too, not just the target
\* (`PLAN.md` §5.2a).

(*--algorithm RejectReceiveSameChannelTwice {
    variables a = 0, b = 0;
    fifos x;
    process (P = 0) {
    p1: receive(x, a);
        receive(x, b);
        goto Done;
    }
}*)

====
