---- MODULE AcceptCaseCheckedHeterogeneousBranches ----
\* Expect: accepted. The `CASE` half of `accept_if_checked_heterogeneous_branches.tla` -- thesis
\* §3.1.3.6's `Γ ⊢ CASE p1 -> e1 [] ... [] OTHER -> e_n+1 ⇓ τ` rule. Each branch, and the `OTHER`
\* arm, is checked against `f`'s declared `Int -> Int` on its own, so all three get a *different*
\* coercion: `STR-TO-SEQ` then `SEQ-TO-FUN` for `"ab"`, `TUPLE-TO-SEQ` then `SEQ-TO-FUN` for
\* `<<1, 2>>`, and nothing at all (`Coercion.id`) for the already-`Int -> Int` function literal.
\*
\* Worth keeping distinct from the `IF` fixture: here the per-branch coercions differ in *length*,
\* not just in which axiom fires, so no single coercion shared across the whole expression could
\* work even in principle. It also covers the `OTHER` arm specifically, which is elaborated
\* separately from the guarded branches.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptCaseCheckedHeterogeneousBranches {
    process (P = PID)
        variable (* @type: Int -> Int; *) f = CASE TRUE -> "ab"
                                                [] FALSE -> <<1, 2>>
                                                [] OTHER -> [i \in {1} |-> i];
    {
    p1: skip;
    }
}*)

====
