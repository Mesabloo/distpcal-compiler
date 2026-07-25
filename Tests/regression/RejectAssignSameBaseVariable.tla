---- MODULE RejectAssignSameBaseVariable ----
EXTENDS Naturals
\* Expect: rejected. `x[0] := 3; x[1] := 4` writes the same variable in one atomic block.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectAssignSameBaseVariables {
    process (P = PID)
        variables 
            \* @type: Int -> Int;
            x = [y \in Nat |-> y];
    {
    p1: x[0] := 3;
        x[1] := 4;
        goto Done;
    }
}*)

====
