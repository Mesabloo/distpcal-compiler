---- MODULE AcceptMulticastPartialAnnotation ----
\* Expect: accepted with a warning, once `\X` resolves. A multi-component filter annotating one
\* component and not the other. The desugarer collapses the components into a single binder whose
\* declared type is the tuple of theirs, which it can only build when every component supplies one
\* -- so a partial annotation is dropped rather than half-applied, and warns
\* (`partial-multicast-annotation`, W0005) instead of doing so silently. Nothing is lost by the
\* drop: the recipient's type is fixed by the channel's own declared domain regardless.
\*
\* The warning fires and is asserted here. The compile as a whole still fails, for the same reason
\* AcceptMulticastMultiComponent does -- a tuple-domain channel has no `Network` field shape to
\* index -- so this stays xfail until that is lifted, W0005 being reachable only through a filter
\* with more than one component.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMulticastPartialAnnotation {
    fifos
        \* @type: <<Address, Address>> -> Channel(Int);
        ch[{PID}];
    process (P = PID) {
    p1: multicast(ch, [(* @type: Address; *) m = PID, y \in {PID} |-> 1]);
        goto Done;
    }
}*)

====
