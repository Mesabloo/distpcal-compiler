---- MODULE RejectChannelDeclaredNonChannelType ----
\* Expect: rejected, `TCError.notAChannelType` (`Elaborator/PlusCal.lean`'s `checkChannelDecl`).
\* A `fifos`/`channels` entry's mandatory `@type` annotation must itself be a `Channel(_)` (or
\* `_ -> Channel(_)` for an indexed one) -- annotating it as a plain `Int` is rejected before any
\* `send`/`receive` ever gets a chance to use `ch`.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectChannelDeclaredNonChannelType {
    fifos
        \* @type: Int;
        ch;
    process (P = PID) {
    p1: skip;
    }
}*)

====
