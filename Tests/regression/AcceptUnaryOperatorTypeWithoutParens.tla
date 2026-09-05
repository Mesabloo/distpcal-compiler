---- MODULE AcceptUnaryOperatorTypeWithoutParens ----
\* Expect: accepted. `Parser_/Annotations.lean`'s `parseType'` required parens around a unary
\* operator type's own parameter -- `(Int) => Int` parsed, `Int => Int` didn't, failing at
\* `E0005` (`typeParseFailure`) before ever reaching the type checker. Fixed by letting the
\* argument-list step accept a single unparenthesized atom alongside the existing parenthesized
\* form. Exercises the bare case at top level (`F`'s own annotation) and the nested case inside a
\* parenthesized outer argument list (`Op`'s, one element of which is itself unparenthesized) --
\* both must parse and reach the type checker, matching `F`'s and `G(_)`'s real arities.

EXTENDS Naturals

\* @type: Int => Int;
F(x) == x + 1

\* @type: (Int => Int, Int) => Int;
Op(G(_), y) == G(y)
====
