package comm

import "github.com/mesabloo/fugue/runtime/tlaplus"

// Address is the identity of a process, left deliberately unspecified.
//
// Distributed PlusCal says nothing about what a process identity is, and the
// compiler emits no main function, so the concrete choice — a Unix socket path,
// an IP address and port, an index into a static table — belongs to whoever
// builds a runnable system out of the generated code. Generated code only ever
// passes addresses around and compares them.
//
// It lives here, with the message-passing endpoints, because that is what an
// address is for: naming the peer a Sender reaches. The Network a process is
// handed is a mapping from addresses to endpoints.
//
// Eq is required because specifications compare identities (self = p, and the
// filters on a multicast). Ord comes along with it because addresses reach
// places that need a total order, notably as keys of a lazy function.
type Address interface {
	tlaplus.Ord[Address]
}
