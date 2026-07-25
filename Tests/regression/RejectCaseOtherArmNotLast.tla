---- MODULE RejectCaseOtherArmNotLast ----
\* Expect: rejected, as a parse error. `OTHER` is `CASE`'s fallback arm, so it is only meaningful
\* as the *last* one -- `Parser_/TLAPlus.lean`'s `parseCase` parses the guarded branches with
\* `sepBy1` and then the `OTHER` arm once, after them, so "last" is enforced by the grammar itself
\* rather than checked after the fact. Nothing follows the `OTHER` arm in the production, hence the
\* error lands on the `[]` that tries to.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectCaseOtherArmNotLast {
    process (P = PID)
        variable x = CASE FALSE -> 1
                       [] OTHER -> 3
                       [] TRUE -> 2;
    {
    p1: skip;
    }
}*)

====
