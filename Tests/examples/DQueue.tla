\* https://github.com/DistCompiler/pgo/blob/main/systems/dqueue/dqueue.tla

------------ MODULE DQueue ---------------
EXTENDS Fugue

CONSTANTS
  \* @type: () => Str;
  Stream,
  \* @type: Set(Address);
  Nodes,
  \* @type: Address;
  Producer

(*--algorithm DQueue {
  fifos
    \* @type: Channel(Address);
    producer,
    \* @type: Address -> Channel(Str);
    consumer[Nodes];

  \* @mailbox: producer;
  process (Producer = Producer)
    variable
      \* @type: Address;
      addr = self;
  {
  p:  while (TRUE) {
  p1:   receive(producer, addr);
  p2:   send(consumer[addr], Stream());
      }
  }

  \* @mailbox: consumer[self];
  process (Consumer \in Nodes)
    variable
      \* @type: Str;
      msg;
  {
  c:  while (TRUE) {
  c1:   send(producer, self);
  c2:   receive(consumer[self], msg);
        print msg;
      }
  }
}*)

==========
