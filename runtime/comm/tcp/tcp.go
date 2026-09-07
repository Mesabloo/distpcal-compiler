// Package tcp is a concrete implementation of the comm endpoints over TCP: a
// process reaches its peers across the network rather than over Go channels in
// one address space.
//
// The comm package deliberately ships only interfaces, leaving the medium to
// whoever builds a runnable system out of generated code. This package is one
// such choice, kept in the tree because a runnable distributed example needs
// endpoints that actually cross a machine boundary, and a hand-written pair per
// example is worse than one shared, tested implementation.
//
// The three pieces fit together as follows. Each process opens a Listen
// endpoint for its own mailbox and registers the address it bound to with a
// name server under a stable logical name. A process that needs to send to a
// peer looks that peer's name up, learns a host and port, and opens a Dial
// endpoint to it. Values on the wire are gob-encoded; a message carrying an
// address in an interface-typed field works because Name is registered with
// gob below.
//
// Nothing here attempts fault tolerance beyond reconnection: the source
// language has no vocabulary for a peer that has permanently failed, so a
// broken connection is treated as one that has not come up yet.
package tcp

import (
	"encoding/gob"

	"github.com/mesabloo/fugue/runtime/comm"
)

// Name is a process identity that is nothing but its logical name.
//
// The name server maps a Name to the host and port the process is currently
// reachable at, so generated code compares and routes on the stable name while
// the transport deals in addresses that change from run to run. self is a Name,
// the keys of a Network's indexed channel are Names, and the from field a Pong
// puts in its message is a Name.
//
// Eq and Lt are the comm.Address contract. The order is lexicographic on the
// name, which is the arbitrary-but-total choice the interface documents as the
// integrator's: it makes CHOOSE over a set of addresses resolve to the
// alphabetically first name. Both methods assume the other address is also a
// Name — every address in one running system comes from this package — and
// panic otherwise, the same stance comm's own tests take.
type Name string

// Eq reports whether two identities are the same name.
func (n Name) Eq(other comm.Address) bool { return n == other.(Name) }

// Lt orders identities lexicographically by name.
func (n Name) Lt(other comm.Address) bool { return n < other.(Name) }

func init() {
	// A message field typed as comm.Address travels as an interface value, and
	// gob refuses to encode a concrete type behind an interface unless it has
	// been registered. Both ends of every connection import this package, so
	// this runs on both.
	gob.Register(Name(""))
}
