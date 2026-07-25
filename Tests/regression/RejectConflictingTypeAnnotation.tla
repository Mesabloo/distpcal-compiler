---- MODULE RejectConflictingTypeAnnotation ----
\* Expect: rejected, `DesugarError.duplicateAnnotation`. Two `@type` annotations on the
\* same binder naming *different* types are genuinely ambiguous (which one applies?),
\* unlike two identical ones (`accept_redundant_type_annotation.tla`).

CONSTANTS
    \* @type: Int;
    \* @type: Str;
    Foo

(*--algorithm RejectConflictingTypeAnnotation {
    process (P = 0) {
    p1: skip;
    }
}*)

====
