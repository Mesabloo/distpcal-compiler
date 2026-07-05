---- MODULE AcceptMailboxIndexedBySelf ----
\* Expect: accepted. `@mailbox: ch[self];` -- indexing a process's own mailbox by `self` -- is
\* the standard idiom for a per-process channel array (confirmed via hand-verification against
\* `TPC2.tla`, `~/Documents/distpcal-compiler/tests/TPC/TPC2.tla`). An earlier version of
\* `Elaborator/PlusCal.lean`'s `checkProcess` checked `mailbox` *before* extending `Γ` with
\* `self`, rejecting this with "Unbound variable `self`".

CONSTANTS
    \* @type: Set(Address);
    Agents

(*--algorithm AcceptMailboxIndexedBySelf {
    fifos
        \* @type: Address -> Channel(Str);
        ch[Agents];

    (* @mailbox: ch[self]; *) process (a \in Agents) {
    p1: skip;
    }
}*)

====
