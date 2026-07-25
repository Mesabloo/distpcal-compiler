---- MODULE AcceptExceptNestedRecordThenIndex ----
\* Expect: accepted. `[r EXCEPT !.f[i] = v]` -- a single `EXCEPT` update chaining a record-field
\* step and an index step, exercised via `Desugarer/TLAPlus.lean`'s general path-walk (`!.f[i]`
\* parses as two steps, a field step then an index step, `Parser_/TLAPlus.lean`'s `parseExcept`)
\* and `Elaborator/Expressions.lean`'s `stepInto`/`checkExceptPath`, which threads the type through
\* each step in turn (record access first, narrowing to `r.f`'s function type, then a function-call
\* index on that). No existing fixture chains two different kinds of `EXCEPT` steps together.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptExceptNestedRecordThenIndex {
    process (P = PID)
        variable r = [f |-> [n \in {1, 2} |-> 0]];
    {
    p1: r := [r EXCEPT !.f[1] = 9];
        goto Done;
    }
}*)

====
