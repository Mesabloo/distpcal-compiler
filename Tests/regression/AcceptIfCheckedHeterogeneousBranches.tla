---- MODULE AcceptIfCheckedHeterogeneousBranches ----
\* Expect: accepted. `IF` in *checking* position (thesis §3.1.3.6's `Γ ⊢ IF e1 THEN e2 ELSE e3 ⇓ τ`
\* rule): `f`'s declared `Int -> Int` flows into both branches, so each is checked against it
\* separately and picks up its own coercion chain -- `"ab"` via `STR-TO-SEQ` then `SEQ-TO-FUN`,
\* `<<1, 2>>` via `TUPLE-TO-SEQ` then `SEQ-TO-FUN`.
\*
\* The two branch types (`Str` and `<<Int,Int>>`) are incomparable to each other, so this is
\* exactly the case synthesis cannot handle: `Elaborator/Subtyping.lean`'s `lub` returns one of
\* its two arguments or `none`, and neither branch type is the join. Before the checking rule
\* existed, `IF` fell through to `checkExpr`'s generic `[Subtype]` fallback, which synthesizes
\* first -- so this was rejected with `ambiguousType` despite the annotation being right there.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptIfCheckedHeterogeneousBranches {
    process (P = PID)
        variable (* @type: Int -> Int; *) f = IF TRUE THEN "ab" ELSE <<1, 2>>;
    {
    p1: skip;
    }
}*)

====
