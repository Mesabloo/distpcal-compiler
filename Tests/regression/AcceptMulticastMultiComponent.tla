---- MODULE AcceptMulticastMultiComponent ----
\* Expect: accepted, once `\X` resolves. A filter with more than one component: the recipients are
\* `{PID} \X {PID}`, so `ch` is indexed by a pair and the payload may name either part. The
\* desugarer collapses the components into one fresh binder over their Cartesian product,
\* rewriting each component name in the payload to a projection off it, exactly as a multi-binder
\* function literal `[x \in A, y \in B |-> e]` is collapsed.
\*
\* Type-checks; rejected at code generation. A tuple-domain channel's `Network` field would have
\* to be keyed by the pair, and the struct holds a `map[comm.Address]` -- the same limit
\* `compileSend` runs into for a channel indexed by more than one bracket group. Single-component
\* filters, which need no product, compile end to end.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMulticastMultiComponent {
    fifos
        \* @type: <<Address, Address>> -> Channel(Int);
        ch[{PID}];
    process (P = PID) {
    p1: multicast(ch, [m = PID, y \in {PID} |-> 1]);
        goto Done;
    }
}*)

====
