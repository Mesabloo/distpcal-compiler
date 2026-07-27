------------------------ MODULE LamportMutex -------------------------
EXTENDS Naturals, Sequences, Fugue

CONSTANT
    \* @type: Set(Address);
    Nodes

\* @type: (Int, Int) => Int;
Max(c, d) == IF c > d THEN c ELSE d
\* @type: ((Address -> Int), Address, Address) => Bool;
beats(req, a, b) ==
  \/ req[b] = 0
  \/ req[a] < req[b]
  \/ req[a] = req[b] /\ a \prec b
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
            msg = Request(self, 0),
            \* @type: Address;
            sndr = self;
    {
ncs:    while (TRUE) {
            skip;  \* non-critical section
try:        clock := clock + 1; req[self] := clock; ack := {self};
            multicast(network, [nd \in Nodes |-> Request(self, clock)]);
enter:      await (ack = Nodes /\ \A nd \in Nodes \ {self} : beats(req, self, nd));
cs:         skip;  \* critical section
exit:       clock := clock + 1;
            multicast(network, [nd \in Nodes \ {self} |-> Release(self, clock)]);
        } 
    } 
    {
rcv:    while (TRUE) { 
            receive(network[self], msg);
            clock := Max(clock, msg.clock) + 1;
handle:     if (msg.type = "request") {
                req[msg.agent] := msg.clock;
                send(network[msg.agent], Acknowledge(self, clock))
            } else if (msg.type = "ack") { 
                ack := ack \cup {msg.agent}; 
            } else if (msg.type = "release") { 
                req[msg.agent] := 0; 
            }
        }
    }
} **)
====