// Package comm covers message passing between compiled processes: the
// endpoints a channel is reached through, and the addresses identifying who
// sits at the other end.
//
// A channel in the source language is not a Go value and has no runtime
// representation of its own: channels are not first-class in Distributed
// PlusCal, so one is never stored, passed around, or placed in a data
// structure. It only ever appears at a send or receive site. What the generated
// code holds instead are these endpoints, handed to a process by whoever wires
// the system together.
//
// That is why the endpoints are interfaces rather than concrete types. The
// compiler emits no main function and takes no position on the medium: a Go
// channel between goroutines in one process, a Unix socket between processes on
// one machine, a TCP connection between machines. All three satisfy these
// interfaces, and the choice belongs to the person building a runnable system
// out of the generated code.
package comm

// Sender is the writing end of a channel.
//
// Send may block — a medium with bounded capacity has nowhere to put the value
// until a reader takes one out — and generated code is written on the
// assumption that it might.
//
// There is no error result. A medium that has failed permanently cannot be
// reported to a specification that has no vocabulary for failure, so the
// implementation decides: block, panic, or drop. This mirrors the absence of
// fault tolerance in the compilation scheme generally.
type Sender[T any] interface {
	Send(value T)
}

// Receiver is the reading end of a channel.
//
// Recv blocks until a value is available. It returns the value and true
// normally; when the medium has vanished — the peer closed it, the connection
// dropped — it returns the zero value and false, and keeps doing so. The flag
// is what lets a process's receive loop terminate instead of blocking forever
// against a channel nobody will write to again.
type Receiver[T any] interface {
	Recv() (T, bool)
}
