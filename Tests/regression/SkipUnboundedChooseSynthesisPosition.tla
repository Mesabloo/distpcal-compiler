---- MODULE SkipUnboundedChooseSynthesisPosition ----
\* Expect: rejected, `TCError.cannotInferType` (`Elaborator/Expressions.lean`, the
\* `.choose _ _ none _, pos => throw (.cannotInferType ...)` case: unbounded `CHOOSE` has no
\* synthesis rule at all, only a checking-mode one) -- but currently rejected for a completely
\* different reason, a real parser gap. `Parser_/TLAPlus.lean` lexes `CHOOSE` into its own
\* `.choose` token (`identifierOrKeyword`'s `mapKeywordToToken`) and both
\* `Core/SurfaceTLAPlus/Syntax.lean` and `Core/SurfaceTLAPlus/Pretty.lean` fully support a `.choose`
\* expression node -- but no parser production anywhere (`parseAtom`'s `first [...]` list, where
\* `\A`/`\E`/`IF`/`CASE`/etc. each get their own case) ever consumes the `.choose` token to build
\* one. So `CHOOSE` cannot be parsed in *any* position today, bounded or unbounded, checking or
\* synthesis; confirmed directly (`print CHOOSE x : x = x` and even a bare top-level
\* `x == CHOOSE n : n = n` both fail identically with "unexpected keyword 'CHOOSE'"/"unexpected
\* identifier"). This fixture exits non-zero today for that reason, which happens to match what
\* `reject_*` expects, but only coincidentally -- the intended `cannotInferType` check is never
\* actually reached. See `accept_unbounded_choose_with_expected_type.tla` for the accept-side
\* counterpart, which is genuinely broken (not coincidentally passing) by the same gap.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectUnboundedChooseSynthesisPosition {
    process (P = PID) {
    p1: print CHOOSE x : x = x;
        goto Done;
    }
}*)

====
