---- MODULE AcceptMailboxIndexedBySelf ----
\* Expect: accepted. `@mailbox: ch[self];` -- indexing a process's own mailbox by `self` -- is
\* the standard idiom for a per-process channel array (confirmed via hand-verification against
\* a reference `TPC2.tla` two-phase-commit example). An earlier version of
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
