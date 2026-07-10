---- MODULE RejectUnreferencedPolymorphicOperatorUnconstrained ----
\* Expect: rejected, `TCError.unconstrainedMetavariable` (`Elaborator/Resolution.lean`'s
\* `resolveTypeMVars`, reached from `resolveMVars` at the end of checking the `with` statement).
\* `Id`, a genuine let-polymorphic identity operator (`@type: (a) => a;`), is referenced here as a
\* bare value (`with (y = Id) ...`), never called -- `[Var]` freshens its `Typ.var "a"` into its
\* own metavariable `?n` at the reference site (`specializeType`), but since `y` is never used for
\* anything, nothing ever constrains `?n` to a concrete type before checking finishes. Distinct
\* from `accept_operator_used_polymorphically.tla`, where `Id`'s two references are each *called*
\* (pinning their own metavariable via argument checking) rather than left as bare values.

CONSTANTS
    \* @type: Address;
    PID

\* @type: (a) => a;
Id(x) == x

(*--algorithm RejectUnreferencedPolymorphicOperatorUnconstrained {
    process (P = PID) {
    p1: with (y = Id) {
            skip;
        };
        goto Done;
    }
}*)

====
