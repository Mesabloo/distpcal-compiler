---- MODULE AcceptVariableInitializerNamesSibling ----
\* Expect: accepted, all the way to Go. PlusCal's `variables` initializers are sequential --
\* `Elaborator/PlusCal.lean`'s `checkVariables` extends the context per entry -- so `y = x + 1`
\* may name the `x` declared beside it. This type-checked all along and then compiled to Go
\* naming an identifier that did not exist, because a process-local used to live only inside its
\* lock's struct; the initialization walk now emits a Go local per variable before the locks are
\* built, which is what makes the reference resolve.
\*
\* `base` deliberately ends up in no lock: nothing touches it after initialization, so the only
\* thing keeping it alive is `count`'s initializer naming it.

EXTENDS Integers

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptVariableInitializerNamesSibling {
    process (P = PID)
        variables base = 10, count = base + 1;
    {
    p1: count := count + 1;
        goto Done;
    }
}*)

====
