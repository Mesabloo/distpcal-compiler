---- MODULE AcceptCaseOtherArm ----
\* Expect: accepted. Plain `CASE ... [] OTHER -> e`, the shape TLA+ actually writes. Kept separate
\* from `accept_case_checked_heterogeneous_branches.tla` (which needs `OTHER` too, but is about
\* per-branch coercions) so a parser regression here reports as a parser problem rather than as a
\* type-checker one.
\*
\* `Parser_/TLAPlus.lean`'s `parseCase` used to parse the fallback arm as a bare `[] e`, never
\* consuming the `OTHER ->` keyword at all -- its `.other` token was defined but unused -- so this
\* module was a parse error and no fixture covered it.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptCaseOtherArm {
    process (P = PID)
        variable x = CASE FALSE -> 1
                       [] TRUE -> 2
                       [] OTHER -> 3;
    {
    p1: skip;
    }
}*)

====
