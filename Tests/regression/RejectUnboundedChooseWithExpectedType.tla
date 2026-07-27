---- MODULE RejectUnboundedChooseWithExpectedType ----
\* Expect: rejected, `WellFormednessError.unboundedQuantifier` (check 3,
\* `WellFormedness/Restrictions.lean`'s `.choose _ _ dom _` case). `n`'s own `@type: Int;`
\* annotation gives `checkVariable` (`Elaborator/PlusCal.lean`) an expected type to check `n`'s
\* initializer against, so unbounded `CHOOSE m : m = m` hits `Elaborator/Expressions.lean`'s
\* checking-mode `.choose x _ann none body` case (`m` bound at `Int`, body checked against `Bool`)
\* rather than the synthesis-only case that has no rule at all -- so it type-checks. Well-formedness
\* rejects it anyway: an unbounded quantifier reachable from the algorithm has no finite runtime
\* meaning, whichever mode typed it. This is check 3's one reachable `unboundedQuantifier` trigger
\* (§9.13) -- unbounded `\A`/`\E` die at `TCError.expectedTypeAnnotation` first, their binder having
\* no annotation to carry a type.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectUnboundedChooseWithExpectedType {
    process (P = PID)
        variable (* @type: Int; *) n = CHOOSE m : m = m;
    {
    p1: skip;
    }
}*)

====
