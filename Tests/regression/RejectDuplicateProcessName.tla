---- MODULE RejectDuplicateProcessName ----
\* Expect: rejected, `WellFormednessError.duplicateProcessName`. A process instance is
\* identified by its process's name together with its own `self`, and both languages'
\* semantics resolve one by `processes.find? (·.name == name)` -- the *first* process
\* carrying the name. Two processes named `P` would silently give every instance of the
\* second the first's code table and labels, while the initial state still contributed
\* instances from both. Nothing else rejects this: process names are in no declaration
\* scope, so `duplicateName`/`shadowedName` never look at them. The two `id`s differ, so
\* the instances themselves are distinct -- it is only the name they are dispatched on
\* that collides.

CONSTANTS
    \* @type: Address;
    PID1,
    \* @type: Address;
    PID2

(*--algorithm RejectDuplicateProcessName {
    process (P = PID1)
        variables x = 0;
    {
    p1: x := 1;
    }

    process (P = PID2)
        variables y = 0;
    {
    q1: y := 1;
    }
}*)

====
