---- MODULE AcceptEmptyBagUsedTwiceConsistently ----
\* Expect: accepted. `x`'s own annotation pins both `EmptyBag` operands of `(+)` to the same
\* rigid element type `a` — nothing here is genuinely ambiguous, so this should type-check
\* trivially. It didn't right after the third follow-up (PLAN.md §9.19) landed: each `EmptyBag`
\* reference gets its own independently-freshened metavariable, both compared against a third,
\* shared metavariable from `(+)`'s own instantiation, and resolving that shared metavariable's
\* own reflexivity check (`subtype b b`, once `b` is itself an unresolved metavariable) hit a
\* genuine bug in `Elaborator/Subtyping.lean`'s `subtype`: its `.mvar a, .mvar b` case never
\* checked `a == b`, so comparing a metavariable against itself spuriously recorded a fresh,
\* self-referential pending bound instead of trivially succeeding, eventually tripping the
\* "metavariable with more than one recorded upper bound" guard.
\* Regression-covers `subtype`'s `.mvar a, .mvar b` case now checking `a == b` first (PLAN.md
\* §9.19, fourth follow-up).

EXTENDS Bags

\* @type: a -> Int;
x == EmptyBag (+) EmptyBag
====
