---- MODULE AcceptIfBranchesSameVariable ----
\* Expect: accepted. Two *different* `if` branches writing to the same variable is fine -- only
\* one of them ever actually runs (`PLAN.md` §5.2a).

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptIfBranchesSameVariable {
    process (P = PID)
        variables x = 0;
    {
    p1: if (TRUE) {
            x := 1;
        } else {
            x := 2;
        };
        goto Done;
    }
}*)

====
