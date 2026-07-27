---- MODULE RejectMulticastPartialAnnotation ----
\* Expect: W0005, then rejected at code generation, `N2GError.unsupported` (E0061). A
\* multi-component filter annotating one component and not the other. The desugarer collapses the
\* components into a single binder whose declared type is the tuple of theirs, which it can only
\* build when every component supplies one -- so a partial annotation is dropped rather than
\* half-applied, and warns (`partial-multicast-annotation`, W0005) instead of doing so silently.
\* Nothing is lost by the drop: the recipient's type is fixed by the channel's own declared domain
\* regardless.
\*
\* The warning fires and is asserted here. The compile then fails for the same reason
\* RejectMulticastMultiComponent does -- a tuple-domain channel has no `Network` field shape to
\* index -- and, like it, encodes a construct outside §8's single-binder multicast, so the
\* rejection is the expectation rather than an `xfail`. W0005 is reachable only through a filter
\* with more than one component, so this stays its only trigger.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectMulticastPartialAnnotation {
    fifos
        \* @type: <<Address, Address>> -> Channel(Int);
        ch[{PID}];
    process (P = PID) {
    p1: multicast(ch, [(* @type: Address; *) m = PID, y \in {PID} |-> 1]);
        goto Done;
    }
}*)

====
