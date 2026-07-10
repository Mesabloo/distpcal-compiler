---- MODULE RejectHigherOrderParamNotOperatorType ----
\* Expect: rejected, `TCError.notAnOperatorType` (`Elaborator/Declarations.lean`'s
\* `checkParamArity`, the `_ => throw (.notAnOperatorType pos tau)` branch). `F(_)` declares a
\* higher-order parameter of arity 1 (one `_`), but `Op`'s annotated type gives `F`'s own position
\* a plain `Int` -- not an `Operator` type at all, so there's no arity for `checkParamArity` to
\* even compare against. (An arity-0 higher-order-looking param, `F` with no parens/underscores at
\* all, needs no such check -- `checkParamArity`'s `if arity = 0 then pure ()` fast path -- so this
\* fixture deliberately uses `F(_)`, not bare `F`, to actually exercise the check.)

\* @type: (Int, Int) => Int;
Op(F(_), x) == x
====
