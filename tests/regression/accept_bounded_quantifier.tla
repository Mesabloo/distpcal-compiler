---- MODULE AcceptBoundedQuantifier ----
\* Expect: accepted. A *bounded* `\A x \in S : P` inside a statement is unaffected by check 3's
\* new unbounded-quantifier half -- only a `dom = none` triggers `unboundedQuantifier`.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptBoundedQuantifier {
    process (P = PID) {
    p1: assert \A y \in {1, 2} : y > 0;
        goto Done;
    }
}*)

====
