---- MODULE AcceptBoundedForallMultiNameSharedDomain ----
\* Expect: accepted. `\A x, y \in S : P` -- two names sharing one domain (`QuantifierBound.vars`,
\* `Desugarer/TLAPlus.lean`'s `flattenBound`, the `.vars xs dom` case) -- expands to one binding
\* per name with no rewriting, unlike `.varTuple`'s fresh-projection substitution
\* (`accept_bounded_forall_tuple_pattern_binder.tla`) and unlike the existing PlusCal-`with`
\* multi-binder fixture (`accept_multi_binder_with_desugars_to_chain.tla`, a different construct
\* entirely -- sequential `with` nesting, not a shared-domain quantifier).

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptBoundedForallMultiNameSharedDomain {
    process (P = PID) {
    p1: assert \A x, y \in {1, 2} : x + y >= 0;
        goto Done;
    }
}*)

====
