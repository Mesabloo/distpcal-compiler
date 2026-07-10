---- MODULE AcceptExceptMultiIndexUpdate ----
\* Expect: accepted. `[f EXCEPT ![i, j] = v]` -- existing fixtures only cover multi-index access on
\* plain `fnCall`/`Ref` (`accept_multi_index_ref_desugars_to_tuple.tla`,
\* `accept_multi_index_function_call_desugars_to_tuple.tla`), never on `EXCEPT`'s own update path.
\* `Desugarer/TLAPlus.lean`'s `.except` desugaring reuses `wrapIndices` (line 109) the same way, so
\* `![1, 2]` (one bracket group, two indices) collapses to a single tupled index step, exactly
\* like a plain `f[1, 2]` access would. `f`'s domain is a set of pairs (single binder, not the
\* still-broken multi-binder Cartesian-product collapse -- see
\* `accept_function_literal_cartesian_product_binder.tla`), so this fixture is independent of that
\* gap.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptExceptMultiIndexUpdate {
    variable f = [p \in {<<1, 2>>} |-> 0];
    process (P = PID) {
    p1: f := [f EXCEPT ![1, 2] = 99];
        goto Done;
    }
}*)

====
