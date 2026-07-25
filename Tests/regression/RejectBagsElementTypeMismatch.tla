---- MODULE RejectBagsElementTypeMismatch ----
\* Expect: rejected. `SetToBag(IntSet) (+) SetToBag(BoolSet)` genuinely mixes an `Int`-element
\* bag with a `Bool`-element bag through `(+)`'s single shared element-type metavariable — this
\* must still fail after the third/fourth follow-ups generalized every top-level
\* declaration's references and fixed a self-comparison bug in `subtype`, neither of which is
\* meant to paper over an actual type conflict.
\* Regression-covers `Elaborator/Resolution.lean`'s new `resolveTypeMVarsForDisplay` too, even
\* though this runner only checks the exit code: the thrown error should name `Int`/`Bool`
\* directly (both metavariables are already resolved by the time the conflicting comparison
\* runs), not raw `?n` metavariable ids — verify by hand with `-t go` if touching that code path.

EXTENDS Bags, Naturals

\* @type: Set(Int);
IntSet == {1, 2, 3}

\* @type: Set(Bool);
BoolSet == {TRUE, FALSE}

\* @type: Int -> Int;
x == SetToBag(IntSet) (+) SetToBag(BoolSet)
====
