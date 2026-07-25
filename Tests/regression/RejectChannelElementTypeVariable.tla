---- MODULE RejectChannelElementTypeVariable ----
\* Expect: rejected, TCError.notSendable. A rigid, unresolved type variable is never a concrete
\* value -- `sendable`'s exclusion list bans it, same as `showable` does for `print`. Channel
\* declarations are monomorphic (never a scheme, unlike a top-level `operator`/`function`), so
\* `a` here is a genuinely stuck, never-instantiated type variable, not a polymorphic parameter.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectChannelElementTypeVariable {
    fifos
        \* @type: Channel(a);
        ch;
    process (P = PID) {
    p1: skip;
    }
}*)

====
