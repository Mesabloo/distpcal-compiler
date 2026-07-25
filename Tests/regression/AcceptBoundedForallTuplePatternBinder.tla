---- MODULE AcceptBoundedForallTuplePatternBinder ----
\* Expect: accepted. `\A <<x, y>> \in S : P` -- a tuple-pattern binder (`QuantifierBound.varTuple`,
\* `Desugarer/TLAPlus.lean`'s `flattenBound`, the `.varTuple xs dom` case) -- collapses to one
\* fresh binder over `dom`, substituting each of `x`/`y` in the body with the corresponding
\* projection out of the fresh variable. Distinct from
\* `accept_bounded_forall_multi_name_shared_domain.tla`'s `.vars` case, which needs no body
\* rewriting at all.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptBoundedForallTuplePatternBinder {
    process (P = PID) {
    p1: assert \A <<x, y>> \in {<<1, 2>>, <<3, 4>>} : x + y >= 0;
        goto Done;
    }
}*)

====
