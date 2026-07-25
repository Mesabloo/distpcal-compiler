---- MODULE AcceptUnboundedChooseWithExpectedType ----
\* Expect: accepted -- `n`'s own `@type: Int;` annotation gives `checkVariable`
\* (`Elaborator/PlusCal.lean`) an expected type to check `n`'s initializer against, so unbounded
\* `CHOOSE m : m = m` hits `Elaborator/Expressions.lean`'s checking-mode `.choose x _ann none body`
\* case (`m` bound at `Int`, body checked against `Bool`) rather than the synthesis-only case that
\* has no rule at all -- but currently REJECTED, a real parser gap, not a mistake in this fixture.
\* `CHOOSE` has no parser production anywhere (see
\* `reject_unbounded_choose_synthesis_position.tla` for the full explanation), so this
\* genuinely-well-typed program cannot even be parsed today. Once a `CHOOSE`-parsing production is
\* added, this fixture should start passing without any change to the fixture itself.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptUnboundedChooseWithExpectedType {
    variable (* @type: Int; *) n = CHOOSE m : m = m;
    process (P = PID) {
    p1: skip;
    }
}*)

====
