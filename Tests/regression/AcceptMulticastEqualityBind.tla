---- MODULE AcceptMulticastEqualityBind ----
\* Expect: accepted. A filter whose only component is an `=`-bind. The components of a multicast
\* filter name the parts of a recipient tuple, an `\in`-bind contributing its own set and an
\* `=`-bind the singleton holding its value -- so `[m = PID |-> 1]` reaches exactly `ch[PID]`, and
\* the desugarer (`Desugarer/PlusCal.lean`'s `MulticastFilter.collapse`) turns it into the same
\* single-binder shape an `\in`-bind produces, over `{PID}`. The distinction between the two bind
\* forms therefore does not survive desugaring, and no pass after it has to reconstruct which was
\* which.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMulticastEqualityBind {
    fifos
        \* @type: Address -> Channel(Int);
        ch[{PID}];
    process (P = PID) {
    p1: multicast(ch, [m = PID |-> 1]);
        goto Done;
    }
}*)

====
