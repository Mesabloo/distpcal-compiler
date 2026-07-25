---- MODULE RejectChannelTypedVariable ----
\* Expect: rejected, WellFormednessError.channelTypedVariable (check 2(a)). A Channel-shaped
\* `variable`/`variables` entry is the `@type: Channel(τ)` loophole around check 1's own
\* restriction -- declare it via `channels`/`fifos` instead. No initializer needed (or even
\* writable -- there's no channel-literal syntax) to trigger this; the bare declared type alone
\* is already the violation.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectChannelTypedVariable {
    process (P = PID)
        variable (* @type: Channel(Int); *) ch;
    {
    p1: skip;
    }
}*)

====
