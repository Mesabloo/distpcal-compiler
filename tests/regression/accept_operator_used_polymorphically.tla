---- MODULE AcceptOperatorUsedPolymorphically ----
\* Expect: accepted. `Id(x) == x`, a genuine let-polymorphic identity operator: `x`'s own binder
\* type must stay rigid within `Id`'s body (never generalized — it's a binder, not a top-level
\* declaration), while each of `Id`'s two call sites gets its own independent instantiation of
\* `Id`'s type variable, once at `Int` and once at `Bool` in the very same module.
\* Regression-covers `Elaborator/Monad.lean`'s `Binding.isScheme` distinguishing a declaration
\* (always a scheme, any arity) from a binder (never one, via `extend`/`extendAll`) — the
\* motivating correctness constraint for PLAN.md §9.19's third follow-up, not just `EmptyBag`'s
\* narrower 0-ary case.

EXTENDS Naturals

\* @type: (a) => a;
Id(x) == x

\* @type: Int;
n == Id(5)

\* @type: Bool;
b == Id(TRUE)
====
