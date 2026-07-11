---- MODULE RejectChannelElementChannel ----
\* Expect: rejected, TCError.notSendable (`Elaborator/PlusCal.lean`'s `checkChannelDecl`,
\* `sendable`). A channel can't itself be sent over another channel -- `sendable`'s exclusion
\* list (operator/channel/const/rigid type variable, and anything containing one) mirrors
\* `showable`'s, checked once at channel-declaration time rather than at every `send`/`receive`/
\* `multicast` site. (This also supersedes an earlier draft of this fixture that tried to
\* exercise well-formedness's `channelInExpression` check via `receive`'s destination `r`
\* resolving to a channel-shaped type: that scenario needed the *source* channel's own element
\* type to itself be Channel-shaped too, matching `Channel`'s reflexivity-only subtyping rule --
\* which this very check now rejects first, at declaration time. See `PLAN.md` §9.25.)

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectChannelElementChannel {
    fifos
        \* @type: Channel(Channel(Int));
        ch;
    process (P = PID) {
    p1: skip;
    }
}*)

====
