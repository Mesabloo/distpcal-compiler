---- MODULE AcceptEmptyBagPolymorphicReference ----
\* Expect: accepted. `EmptyBag` (`Driver/Builtins.lean`) is 0-ary and polymorphic in real TLA+ —
\* every reference to it must get its own fresh instantiation of its element type, not a single
\* rigid one shared across the whole module. `SetToBag(S) (+) EmptyBag` pins `(+)`'s shared
\* element-type metavariable to `Int` via `S`, then checks the bare `EmptyBag` reference against
\* that already-pinned metavariable — this used to fail (`EmptyBag`'s `Typ.var` was bound once,
\* rigidly, with no per-reference generalization at all).
\* Regression-covers `Elaborator/Monad.lean`'s `Binding.isScheme`/`Elaborator/Expressions.lean`'s
\* `inferExpr`'s `.var` case unifying let-generalization at every `Γ`-reference.

EXTENDS Bags, Naturals

\* @type: Set(Int);
S == {1, 2, 3}

\* @type: Int -> Int;
x == SetToBag(S) (+) EmptyBag
====
