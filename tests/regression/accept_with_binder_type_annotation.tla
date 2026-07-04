---- MODULE AcceptWithBinderTypeAnnotation ----
\* Expect: accepted. A `with`-bound variable may carry its own `@type` annotation, same as a
\* `variables`/`channels`/`fifos` entry. Also regression-covers a real parser bug: the first
\* binder immediately after `with`'s opening `(` must still see its own annotation, not have it
\* swallowed by the `(` token's own trailing-whitespace skip (the same class of bug `parseFilter`
\* already works around for `multicast`, `Parser_/PlusCal.lean`).

(*--algorithm AcceptWithBinderTypeAnnotation {
    process (P = 0) {
    p1: with ((* @type: Int; *) x = 3, y = 4) {
          print x + y;
        };
        goto Done;
    }
}*)

====
