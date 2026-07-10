---- MODULE AcceptMultilineConjunctionListAligned ----
\* Expect: accepted. A multi-line `/\` bulleted list whose bullets all share the same column as
\* the first one -- `Parser_/TLAPlus.lean`'s `parseJList`, wrapped in `aligned`, threads that
\* captured column through `indentGuard .eq col` for every subsequent bullet. No existing fixture
\* exercises a genuinely multi-line (as opposed to single-line) bulleted list.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMultilineConjunctionListAligned {
    process (P = PID) {
    p1: assert /\ 1 = 1
               /\ 2 = 2
               /\ 3 = 3;
        goto Done;
    }
}*)

====
