---- MODULE AcceptRepeatedIndexedAssign ----
\* Expect: accepted. `x[0] := 1; x[0] := 5` writes the same *indexed* reference twice -- the
\* conflicting-assignment check only tracks bare variable writes (`x`, never `x[...]`), since
\* deciding whether two indexed writes actually conflict depends on whether the indices are
\* equal, which is out of scope for this purely syntactic check (`PLAN.md` §5.2a).

(*--algorithm AcceptRepeatedIndexedAssign {
    variables x = [n \in {0} |-> 0];
    process (P = 0) {
    p1: x[0] := 1;
        x[0] := 5;
        goto Done;
    }
}*)

====
