---- MODULE AcceptFunctionLiteralCartesianProductBinder ----
\* Expect: accepted. `[x \in A, y \in B |-> e]` (two independent binders over different domains,
\* not a tuple pattern) collapses via `Desugarer/TLAPlus.lean`'s `collapseToSingleBinder` to one
\* fresh binder over the Cartesian product `A \X B` (`cartesianProduct`, an explicit, deliberate
\* desugaring choice -- see the doc comment on `collapseToSingleBinder` itself, which
\* distinguishes this product-collapse from `nestQuantifier`'s sequential nesting used by plain
\* `\A x, y : P`), with the body rewritten to project each original name back off it. This is
\* therefore the fixture that pins `\X`'s own builtin scheme, `(Set(a), Set(b)) => Set(<<a,b>>)`
\* (`Elaborator/Declarations.lean`'s `builtinContext`) -- the same shape as `\cup`/`\cap`, just
\* heterogeneous in its two element types.
\*
\* Two binders only, deliberately: `\X` is binary and left-associative here, so a third would
\* make the product `(A \X B) \X C`, whose elements are pairs holding a pair rather than the flat
\* triples TLA+ means, and the collapse's own `z[3]` projection would then be out of range.
\*
\* `AcceptExceptMultiIndexUpdate.tla` builds its multi-index function via a single binder over a
\* set of tuples instead, so it exercises the same shape without depending on `\X` at all.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptFunctionLiteralCartesianProductBinder {
    process (P = PID)
        variables
            \* @type: <<Int, Int>> -> Int;
            f = [x \in {1, 2}, y \in {3, 4} |-> x + y];
    {
    p1: print f[1, 3];
        goto Done;
    }
}*)

====
