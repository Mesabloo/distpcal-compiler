---- MODULE AcceptChannelElementCompoundSendable ----
\* Expect: accepted. `sendable` recurses through `Set`/`Seq`/`Tuple`/`Record`/`Function` the same
\* way `showable` does -- `Set(Int)` is sendable since `Int` is, confirming the recursive descent
\* doesn't over-reject a legitimate compound element type.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptChannelElementCompoundSendable {
    fifos
        \* @type: Channel(Set(Int));
        ch;
    process (P = PID) {
    p1: skip;
    }
}*)

====
