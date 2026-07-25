---- MODULE AcceptAxiomChainTupleToSeqToFunction ----
\* Expect: accepted. `Elaborator/Subtyping.lean`'s `tryAxioms` doc comment calls out `Str <:
\* Seq(Int) <: Int -> Int` by name as the two-axiom transitive chain this module realizes without
\* a dedicated closure step; this fixture exercises the *other* entry point into the same chain,
\* `Tuple <: Seq(tau)` (`TUPLE-TO-SEQ`, uniform-element tuples only) recursing into `SEQ-TO-FUN`.
\* `f`'s declared type `Int -> Int` forces checking `<<1, 2, 3>>` (which synthesizes as
\* `<<Int,Int,Int>>`, not directly as a `Seq`) through both axioms in one go.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptAxiomChainTupleToSeqToFunction {
    process (P = PID)
        variable (* @type: Int -> Int; *) f = <<1, 2, 3>>;
    {
    p1: skip;
    }
}*)

====
