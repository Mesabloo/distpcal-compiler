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
// filters on a multicast). Lt comes along with it because addresses reach
// places that need a total order: a set of addresses is kept sorted, and a
// function keyed by address is a search tree. Requiring only equality would
// mean linear membership, quadratic normalization, and no minimum for CHOOSE
// to pick — and it would spread, since a record with an address field would
// lose its own order too.
//
// The two operations are spelled out here rather than embedded from tlaplus:
// that package's Ord is a dictionary struct, not an interface, so it cannot be
// an interface's method set. AddressOrd below bridges an implementation of this
// interface into one.
//
// The order the implementation supplies is arbitrary, and knowingly so. An IPv4
// address or a socket path has no natural ordering; all that is required is a
// total one, fixed for the lifetime of a program. Two consequences follow, and
// both are legal but worth knowing:
//
//   - CHOOSE x \in S : P(x) over a set of addresses resolves to the minimum
//     under whatever order this implementation defines, so two implementations
//     may pick different addresses from one specification. TLA+'s CHOOSE is
//     deterministic but unspecified, so each is a legal refinement — but the
//     generated program's behaviour then depends on a decision the
//     specification did not make.
//   - The same applies to any user-supplied constant type the compiler is
//     handed, for the same reason.
//
// If supplying an order is awkward, the natural fallback is to derive both
// operations from an injective key — comparing the bytes of a socket path, say.
type Address interface {
	Eq(other Address) bool
	Lt(other Address) bool
}

// AddressOrd is the dictionary for Address, bridging the interface's methods
// into the form the runtime's operations take.
//
// The bridge is method expressions: Address.Eq is the two-argument function
// taking the receiver first, which is exactly the shape Ord's fields want.
var AddressOrd = tlaplus.Ord[Address]{Eq: Address.Eq, Lt: Address.Lt}
