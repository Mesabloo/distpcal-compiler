---- MODULE AcceptAxiomChainStringToFunction ----
\* Expect: accepted. The other half of `Elaborator/Subtyping.lean`'s `tryAxioms` doc-comment
\* example: `Str <: Seq(Int) <: Int -> Int` (`STR-TO-SEQ` chaining into `SEQ-TO-FUN`). `g`'s
\* declared type `Int -> Int` forces checking the string literal `"abc"` through both axioms --
\* this is purely a compile-time type-checking fact (the checker never inspects the string's
\* actual characters), distinct from `accept_axiom_chain_tuple_to_seq_to_function.tla`'s `Tuple`
\* entry point into the same two-axiom chain.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptAxiomChainStringToFunction {
    variable (* @type: Int -> Int; *) g = "abc";
    process (P = PID) {
    p1: skip;
    }
}*)

====
