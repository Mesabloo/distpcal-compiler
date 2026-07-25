---- MODULE AcceptIfSynthesizedBranchCoercion ----
\* Expect: accepted. `IF` in *synthesis* position (no expected type: `f` is unannotated), where
\* the branches are comparable -- `Str <: Seq(Int)` -- so `lub` succeeds and returns `Seq(Int)`,
\* the `ELSE` branch's own type. The `THEN` branch must then be wrapped in `STR-TO-SEQ`.
\*
\* Caveat on what this fixture actually enforces: `tests/regression/run.sh` compares exit codes
\* only, and the missing coercion this was written for was *silently accepted* -- the elaborated
\* `IF` carried a bare `Str` branch under a `Seq(Int)` type. So passing here does not prove the
\* coercion is present; it only guards against this ever becoming a *rejection*. Verified by hand
\* instead, via `-d dump-typed`: the `THEN` branch appears as `Str2Seq("ab")`, and did not before
\* `coerceInto` was added to `Elaborator/Expressions.lean`'s three `lubAll` sites. Catching a
\* regression here automatically would need output comparison in the runner, which it has no
\* mode for today.

CONSTANTS
    \* @type: Address;
    PID,
    \* @type: Seq(Int);
    G

(*--algorithm AcceptIfSynthesizedBranchCoercion {
    process (P = PID)
        variable f = IF TRUE THEN "ab" ELSE G;
    {
    p1: skip;
    }
}*)

====
