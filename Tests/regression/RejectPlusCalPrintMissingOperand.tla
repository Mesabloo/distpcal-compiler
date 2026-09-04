---- MODULE RejectPlusCalPrintMissingOperand ----
\* Expect: rejected at the parser, `E0002`, pointing at the `+` whose right operand is missing
\* (`12:18-12:19`) — not relocated to the `print` statement keyword.
\*
\* The PlusCal counterpart of the two `parseAtom` bracket-rewind fixtures, and the one that
\* already reports at the failure point: a statement keyword commits, so the expression parser's
\* error survives out of `parseUnlabeledStatement`. Guards against a regression back to blaming
\* the `print` keyword.

(*--algorithm RejectPlusCalPrintMissingOperand {
    process (P = 1) {
    p1: print (1 + );
    }
}*)
====
