---- MODULE AcceptReceiveCoercionStringToFunction ----
\* Expect: accepted. Item 4's dedicated coverage for a `receive` whose channel element type and
\* destination type differ by a genuine non-identity coercion, exercising `Guarded2Network`'s
\* `Coercion.applyComputable` path (`Guarded2Network/PlusCal.lean`'s `Thread.toNetwork`) rather
\* than the left-alone-since-`Coercion.applyComputable`-didn't-exist-yet identity case every
\* other `receive` fixture uses. `ch`'s element type `Str` and `g`'s declared type `Int -> Int`
\* force the same two-axiom `STR-TO-SEQ`/`SEQ-TO-FUN` chain as
\* `accept_axiom_chain_string_to_function.tla`, but through `receive`'s own `elemTy <: refTy`
\* check (`Elaborator/PlusCal.lean`'s `[Receive]` rule) instead of a plain variable declaration --
\* the resulting `Coercion` ends up stored on the `GuardedPlusCal.Statement.receive` node and must
\* be discharged directly on the built `Head(inbox)`/`Tail(inbox)` expression once lowered to
\* `NetworkPlusCal`.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptReceiveCoercionStringToFunction {
    fifos
        \* @type: Channel(Str);
        ch;
    process (P = PID)
        variable (* @type: Int -> Int; *) g = "abc";
    {
    p1: receive(ch, g);
        goto Done;
    }
}*)

====
