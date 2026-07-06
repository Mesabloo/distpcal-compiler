---- MODULE AcceptTypeAnnotationOnFirstDeclaration ----
\* Expect: accepted. A `\@type` annotation directly on the very first declaration of a
\* module -- no EXTENDS clause, no other declaration before it -- must still attach.
\* Regression test: the annotation comment used to be swallowed as blank whitespace by
\* the module-header parser before the declaration parser ever got a chance to see it,
\* so Id's type would silently resolve to none instead of the annotated function type.
\* (Note the `\@type` above is written escaped so this doc comment doesn't itself get
\* parsed as a bogus, argument-less annotation -- there's no EXTENDS/CONSTANTS keyword
\* between this comment and the declaration below to isolate the two runs.)

\* @type: (Int) => Int;
Id(x) == x

====
