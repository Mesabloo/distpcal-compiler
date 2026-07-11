---- MODULE AcceptFunctionLiteralCartesianProductBinder ----
\* Expect: accepted -- but currently REJECTED with "Unbound variable `\X`", a real gap, not a
\* mistake in this fixture. `[x \in A, y \in B |-> e]` (two independent binders over different
\* domains, not a tuple pattern) collapses via `Desugarer/TLAPlus.lean`'s
\* `collapseToSingleBinder` to one fresh binder over the Cartesian product `A \X B`
\* (`cartesianProduct`, line 64, an explicit, deliberate desugaring choice -- see the doc comment
\* on `collapseToSingleBinder` itself, which distinguishes this product-collapse from
\* `nestQuantifier`'s sequential nesting used by plain `\A x, y : P`). The desugared call site
\* references the builtin operator named `\X`, but `Elaborator/Declarations.lean`'s
\* `builtinContext` -- the Gamma-0 prelude of core operators (`=`, `/\`, `\in`, `\cup`, `DOMAIN`,
\* etc.) -- has no entry for it, so every reference to `\X` is an unbound-variable error regardless
\* of how it got there. Once `builtinContext` gains a `\X : (Set(a), Set(b)) => Set(<<a,b>>)`
\* scheme (the same shape as `\cup`/`\cap`, just heterogeneous in its two element types), this
\* fixture should start passing without any change to the fixture itself -- the domain/body shape
\* here really is well-typed. `accept_except_multi_index_update.tla` deliberately avoids this
\* same gap by building its multi-index function via a single binder over a set of tuples
\* instead, so as to not depend on `\X` being fixed.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptFunctionLiteralCartesianProductBinder {
    variable f = [x \in {1, 2}, y \in {3, 4} |-> x + y];
    process (P = PID) {
    p1: print f[1, 3];
        goto Done;
    }
}*)

====
