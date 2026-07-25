---- MODULE RejectFunctionSetNotComputable ----
\* Expect: rejected, ComputableError.notComputable .fnSet (Typed2Computable). `[A -> B]` denotes
\* the set of *all* functions from `A` to `B` -- no finite runtime representation under this
\* compiler's finite-sets assumption. Neither the type checker nor WellFormedness bans this (it's
\* an ordinary, well-typed TLA+ set expression) -- this is the one genuinely new rejection
\* Typed2Computable itself introduces, once the operator using it is actually reachable from the
\* algorithm.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

\* @type: Set(Int -> Int);
FuncSet == [Nat -> Nat]

(*--algorithm RejectFunctionSetNotComputable {
    process (P = PID) {
    p1: assert FuncSet = FuncSet;
        goto Done;
    }
}*)

====
