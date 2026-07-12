---- MODULE RejectRepeatedIndexedAssign ----
\* Expect: rejected. `x[0] := 1; x[0] := 5` writes the same *base* variable `x` twice in one
\* atomic step -- the conflicting-assignment check tracks writes by base variable regardless of
\* indexing, since deciding whether two indexed writes actually alias is out of scope for this
\* purely syntactic check (`PLAN.md` §5.2a); `x[0]`/`x[0]` conflicts by this rule even though
\* the indices happen to be equal here.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectRepeatedIndexedAssign {
    process (P = PID)
        variables x = [n \in {0} |-> 0];
    {
    p1: x[0] := 1;
        x[0] := 5;
        goto Done;
    }
}*)

====
