---- MODULE RejectOperatorParamArityMismatch ----
\* Expect: rejected, `TCError.paramArityMismatch` (`Elaborator/Declarations.lean`'s
\* `checkParamArity`, the `sigmas.length != arity` branch) -- but currently rejected for a
\* completely different reason, a real parser gap, not this fixture's mistake. `F(_,_)` declares a
\* higher-order parameter of arity 2; the intent is to annotate `Op`'s type so `F`'s own position is
\* a 1-argument operator type (`(Int) => Int`), a genuine arity mismatch (2 vs 1) for
\* `checkParamArity` to catch. But `Parser_/Annotations.lean`'s `parseType'` has no way to write an
\* operator-shaped (`=>`) type *nested* inside another operator type's argument list: its `expr`
\* production (the only place that recognizes `argss => ret`) is only ever reached at the very top
\* of a type annotation or inside a parenthesized sub-expression, and threading a nested `=>` back
\* out through the enclosing `parens`/`fn` scaffolding leaves it either causing an outright parse
\* failure (as here) or getting misparsed as a plain `->` function type instead of an `Operator`
\* one (see `reject_higher_order_param_not_operator_type.tla`'s `notAnOperatorType`, which fires
\* precisely because `Int -> Int` und `(Int) => Int` land in different `Typ` constructors and
\* nesting the latter never actually parses). Confirmed by direct experimentation with several
\* nesting spellings, none of which parse a nested `Operator` type. Net effect: `paramArityMismatch`
\* is currently unreachable through any concrete annotation syntax at all -- this fixture exits
\* non-zero today (`TypeParseError.typeParseFailure`, not `TCError.paramArityMismatch`), which
\* happens to match what `reject_*` expects, but only coincidentally.

\* @type: ((Int) => Int, Int) => Int;
Op(F(_,_), x) == x
====
