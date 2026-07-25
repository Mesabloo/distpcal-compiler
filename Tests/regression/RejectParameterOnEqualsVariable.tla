---- MODULE RejectParameterOnEqualsVariable ----
\* Expect: rejected, `DesugarError.wrongAnnotationKindAtSite`. `@parameter` only makes sense
\* on a process-local variable initialized with `∈` (a range of possible values the caller
\* supplies, `TPC2.tla`'s `aState ∈ {"accept","refuse"}` example) — attaching it to a
\* `=`-initialized variable (a single, fixed value) must be rejected.

(*--algorithm RejectParameterOnEqualsVariable {
    process (P = 0)
        variable (* @parameter *) x = 0;
    {
    p1: skip;
    }
}*)

====
