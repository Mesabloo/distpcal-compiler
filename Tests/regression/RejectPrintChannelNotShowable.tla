---- MODULE RejectPrintChannelNotShowable ----
\* Expect: rejected, `TCError.notShowable` (`Elaborator/PlusCal.lean`'s `[Print]` case, using the
\* `showable` predicate defined just above it). `showable` is explicitly `false` for `Channel`
\* (and anything containing one) -- printing a channel reference directly must be rejected, unlike
\* printing an `Int`/`Bool`/`Str`/`Address`, or a `Function`/`Set`/`Seq`/`Tuple`/`Record` built only
\* from showable components.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectPrintChannelNotShowable {
    fifos
        \* @type: Channel(Int);
        ch;
    process (P = PID) {
    p1: print ch;
        goto Done;
    }
}*)

====
