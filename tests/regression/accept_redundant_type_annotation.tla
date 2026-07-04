---- MODULE AcceptRedundantTypeAnnotation ----
\* Expect: accepted. Two `@type` annotations on the same binder that agree on the *same*
\* type genuinely disagree about nothing -- redundant, not ambiguous. Only a real conflict
\* (a *different* type) is an error (`reject_conflicting_type_annotation.tla`).

CONSTANTS
    \* @type: Int;
    \* @type: Int;
    Foo

(*--algorithm AcceptRedundantTypeAnnotation {
    process (P = 0) {
    p1: skip;
    }
}*)

====
