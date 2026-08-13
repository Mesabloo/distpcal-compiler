---- MODULE TwoPhaseCommit ----
\* Adapted from a known two-phase-commit worked example (`Typed2Guarded`'s Checkpoint 3 case)
\* to this project's C-syntax convention. Not a
\* pass/fail regression fixture (see tests/regression/run.sh's own scope note) -- a hand-
\* verification aid: `fugue -d dump-guarded` on this file's `c2` block (the coordinator's second
\* thread) is compared structurally against that worked example's final post-`𝒞_D→G`
\* shape. `c2` alone already exercises every subpass: `𝒞_cflow` (the `while` and the nested
\* `if`/`else if` chain), `𝒞_flat` (hoisting the `if`s' `either`s), and `𝒞_reord` (floating
\* `receive`'s guard past nothing here, but floating the loop's own re-entry `await` past the
\* preceding `receive`/`assign`s).
CONSTANTS
    \* @type: Set(Address);
    Agents,    \* @type: Address;
         Coord


(*--algorithm TwoPhaseCommit {
    channels
        \* @type: Channel({type: Str, agent: Address});
        coord,
        \* @type: Address -> Channel(Str);
        agt[Agents];

    \* @mailbox: agt[self];
    process (a \in Agents)
        variable
            \* @parameter
            aState \in {"accept", "refuse"};
    {
    a1: send(coord, [type |-> aState, agent |-> self]);
    a2: await(aState \in {"commit", "abort"});
    }
    {
    a3: await(aState # "unknown");
        receive(agt[self], aState);
    a4: skip;
    }

    \* @mailbox: coord;
    process (c = Coord)
        variables
            cState = "unknown",
            \* @type: Set(Address);
            commits = {},
            \* @type: {type: Str, agent: Address};
            msg;
    {
    c1: await(cState \in {"commit", "abort"});
        multicast(agt, [ag \in Agents |-> cState]);
    }
    {
    c2: while (cState \notin {"abort", "commit"}) {
            receive(coord, msg);
            if (msg.type = "refuse") {
                cState := "abort";
            } else {
                if (msg.type = "accept") {
                    commits := commits \cup {msg.agent};
                    if (commits = Agents) {
                        cState := "commit";
                    };
                };
            };
        }
    }
}*)
====
