---- MODULE RejectMulticastMultiComponent ----
\* Expect: rejected at code generation, `N2GError.unsupported` (E0061). A filter with more than
\* one component: the recipients are `{PID} \X {PID}`, so `ch` is indexed by a pair and the payload
\* may name either part. The desugarer collapses the components into one fresh binder over their
\* Cartesian product, rewriting each component name in the payload to a projection off it, exactly
\* as a multi-binder function literal `[x \in A, y \in B |-> e]` is collapsed.
\*
\* Type-checks and passes well-formedness; the Go backend rejects it. A tuple-domain channel's
\* `Network` field would have to be keyed by the pair, and the struct holds a `map[comm.Address]`
\* -- the same limit `compileSend` runs into for a channel indexed by more than one bracket group.
\* §8's v1 subset spells multicast with a single binder (`multicast(x, [y \in e1 |-> e2])`), so a
\* multi-component filter is outside it, and this is a reject fixture rather than an `xfail` accept.
\* Single-component filters, which need no product, compile end to end.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectMulticastMultiComponent {
    fifos
        \* @type: <<Address, Address>> -> Channel(Int);
        ch[{PID}];
    process (P = PID) {
    p1: multicast(ch, [m = PID, y \in {PID} |-> 1]);
        goto Done;
    }
}*)

====
