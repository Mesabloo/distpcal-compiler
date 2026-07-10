---- MODULE RejectUnboundedForallMissingAnnotation ----
\* Expect: rejected, `TCError.expectedTypeAnnotation` (`Elaborator/Expressions.lean`'s
\* `[Unbounded quantification]` case, `ann = none` branch). Unlike bounded `\A x \in S : P`
\* (whose element type comes from `S`), an unbounded `\A x : P` has nothing to synthesize `x`'s
\* type from. Genuinely unwritable any other way, too: `Parser_/TLAPlus.lean`'s `parseQuantifier`
\* parses an unbounded quantifier's variable list via bare `parseIdentifier` (no
\* `tryParseAnnotations` call, unlike the bounded-quantifier-bound parser used elsewhere), so a
\* concrete `@type` annotation can never actually reach `x` here -- every unbounded `\A`/`\E`
\* without a domain is a guaranteed type error under the current grammar, not just this one.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectUnboundedForallMissingAnnotation {
    process (P = PID) {
    p1: assert \A x : x = x;
        goto Done;
    }
}*)

====
