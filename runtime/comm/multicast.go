package comm

import "github.com/mesabloo/fugue/runtime/tlaplus"

// Multicast sends to every recipient in a set: for each address a in to, it
// sends f(a) along the endpoint ch[a].
//
// This is the whole compiled form of the source language's multicast statement.
// The iteration lives here rather than in generated code because there is
// nothing for generated code to decide: a specification's multicast fixes no
// order on the sends and gives no way to observe one, so any order refines it.
// That freedom is the caller's to keep — this implementation walks the set as
// it is stored, but nothing in the contract promises that, and a future
// implementation may send concurrently.
//
// The payload is a function of the recipient rather than a value because the
// source construct binds the recipient and may mention it: multicast(c, [n \in
// Nodes |-> Request(n)]) sends a different message to each n. A payload that
// ignores its argument is the constant case, and costs one call per recipient.
//
// The channel is a map because a multicast target is always an indexed channel:
// the recipient is what indexes it. A recipient with no entry in ch is a
// specification indexing a function outside its domain, which is undefined in
// TLA+, so this panics rather than silently dropping the message — the same
// choice the rest of the runtime makes for an undefined expression.
func Multicast[T any](ch map[Address]Sender[T], to tlaplus.Set[Address], f func(Address) T) {
	for _, a := range to {
		s, ok := ch[a]
		if !ok {
			panic("multicast: no channel endpoint for a recipient in the set")
		}
		s.Send(f(a))
	}
}
