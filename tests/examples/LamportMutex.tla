------------------------ MODULE LamportMutex -------------------------
EXTENDS Naturals, Sequences

CONSTANT
    \* @type: Set(Address);
    Nodes

\* @type: (Int, Int) => Int;
Max(c, d) == IF c > d THEN c ELSE d
\* @type: ((Address -> Int), Address, Address) => Bool;
beats(req, a, b) ==
  \/ req[b] = 0
  \/ req[a] < req[b]
  \/ req[a] = req[b] /\ a < b
\* @type: (Address, Int) => {type: Str, clock: Int, agent: Address};
Request(agt, c) == [ type |-> "request", clock |-> c, agent |-> agt ]
\* @type: (Address, Int) => {type: Str, clock: Int, agent: Address};
Release(agt, c) == [ type |-> "release", clock |-> c, agent |-> agt ]
\* @type: (Address, Int) => {type: Str, clock: Int, agent: Address};
Acknowledge(agt, c) == [ type |-> "ack", clock |-> c, agent |-> agt ]

(* PlusCal options (-distpcal) *)
(**--algorithm LamportMutex {
    fifo
        \* @type: Address -> Channel({type: Str, clock: Int, agent: Address});
        network[Nodes];

    \* @mailbox: network[self];
    process (node \in Nodes)
        variables 
            \* @type: Int;
            clock = 0,
            \* @type: Address -> Int;
            req = [n \in Nodes |-> 0],
            \* @type: Set(Address);
            ack = {},
            \* @type: {type: Str, clock: Int, agent: Address};
            msg = Request(self, 0);
    {
ncs:    while (TRUE) {
            skip;  \* non-critical section
try:        clock := clock + 1; req[self] := clock; ack := {self};
            multicast(network, [m = self, nd \in Nodes |-> Request(clock)]);
enter:      await (ack = Nodes /\ \A nd \in Nodes \ {self} : beats(req, self, nd));
cs:         skip;  \* critical section
exit:       clock := clock + 1;
            multicast(network, [m = self, nd \in Nodes \ {self} |-> Release(clock)]);
        } 
    } 
    {
rcv:    while (TRUE) { 
            with (nd \in Nodes) {
                receive(network[nd,self], msg); sndr := nd;
                clock := Max(clock, msg.clock) + 1
            };
handle:     if (msg.type = "request") {
                req[sndr] := msg.clock;
                send(network[self, sndr], Acknowledge(clock))
            } else if (msg.type = "ack") { 
                ack := ack \cup {sndr}; 
            } else if (msg.type = "release") { 
                req[sndr] := 0; 
            }
        }
    }
} **)
====