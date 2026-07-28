---- MODULE RejectOperatorParamArityMismatch ----
\* Expect: rejected, `TCError.paramArityMismatch` (`Elaborator/Declarations.lean`'s
\* `checkParamArity`, the `σs.length != arity` branch). `F(_,_)` declares a higher-order parameter
\* of arity 2, while `Op`'s annotation gives `F`'s own position a 1-argument operator type
\* (`(Int) => Int`) -- an arity mismatch of 2 vs 1.
\*
\* Parked as `Skip*` until `Parser_/Annotations.lean`'s `parseType'` learned to nest an
\* operator-shaped (`=>`) type inside another operator type's argument list (§9.23): before that,
\* the annotation below did not parse at all and the fixture exited non-zero on
\* `TypeParseError.typeParseFailure`, never reaching the type checker. Note the neighbouring
\* `RejectHigherOrderParamNotOperatorType.tla` (`notAnOperatorType`), which pins the same
\* distinction from the other side: `Int -> Int` and `(Int) => Int` land in different `Typ`
\* constructors.

\* @type: ((Int) => Int, Int) => Int;
Op(F(_,_), x) == x
====
