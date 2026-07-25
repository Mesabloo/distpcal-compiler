---- MODULE AcceptParameterAndTypeOnInVariable ----
\* Expect: accepted. `@type` and `@parameter` may co-occur on the same process-local
\* variable, as long as it's `∈`-initialized (`TPC2.tla`'s `aState ∈ {"accept","refuse"}`
\* example) — and `@mailbox` immediately before a `process` is likewise fine.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptParameterAndTypeOnInVariable {
    fifos (* @type: Channel(Str); *) ch;

    (* @mailbox: ch; *) process (P = PID)
        variable
            \* @type: Str;
            \* @parameter
            x \in {"a", "b"};
    {
    p1: skip;
    }
}*)

====
