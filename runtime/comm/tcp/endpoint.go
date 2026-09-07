package tcp

import (
	"encoding/gob"
	"net"
	"sync"
	"time"

	"github.com/mesabloo/fugue/runtime/comm"
)

// retryDelay is how long a Sender waits before retrying a connection that was
// refused or that broke mid-stream. It trades reconnection latency against a
// busy loop while a peer is starting up.
const retryDelay = 100 * time.Millisecond

// mailboxBuffer is how many received values may sit between the network reader
// goroutines and a slow Recv caller before back-pressure reaches the sender.
const mailboxBuffer = 64

// sender is a Sender[T] that owns one reusable TCP connection to a fixed
// address.
//
// The connection and its gob encoder are created lazily on the first Send and
// recreated whenever a Send fails, so a Sender may be constructed before its
// peer exists. The mutex serialises encodes: a gob stream is stateful, and two
// concurrent writers would interleave type descriptors and values on it.
type sender[T any] struct {
	addr string

	mu   sync.Mutex
	conn net.Conn
	enc  *gob.Encoder
}

// Dial returns a Sender[T] that delivers values to a process listening at addr,
// a "host:port" string obtained from the name server.
//
// No connection is made here. The first Send opens it, and any Send may block
// while the peer is unreachable — the Sender contract permits blocking and has
// no way to report failure, so an unreachable peer is retried rather than
// reported.
func Dial[T any](addr string) comm.Sender[T] {
	return &sender[T]{addr: addr}
}

// Send encodes value and writes it to the peer, connecting first if needed and
// retrying until one full value has been handed to a live connection.
func (s *sender[T]) Send(value T) {
	s.mu.Lock()
	defer s.mu.Unlock()

	for {
		if s.enc == nil {
			conn, err := net.Dial("tcp", s.addr)
			if err != nil {
				time.Sleep(retryDelay)
				continue
			}
			s.conn = conn
			s.enc = gob.NewEncoder(conn)
		}

		if err := s.enc.Encode(&value); err != nil {
			s.conn.Close()
			s.conn = nil
			s.enc = nil
			time.Sleep(retryDelay)
			continue
		}
		return
	}
}

// receiver is a Receiver[T] fed by every process that dials its listener.
//
// One goroutine accepts connections; one more per connection decodes a stream
// of T values into a shared buffered channel. Recv reads that channel.
type receiver[T any] struct {
	ln net.Listener
	ch chan T
}

// Listen binds a TCP listener at bind ("host:port", or "host:0" for an
// arbitrary free port) and returns a Receiver[T] delivering the values sent to
// it together with the address actually bound, which is what a process
// registers with the name server.
//
// The Receiver treats its mailbox as permanently alive: Recv blocks while no
// value is available and never reports the medium gone, because a compiled
// process's receive loop is not expected to terminate and there is no
// distributed shutdown protocol here to end it cleanly.
func Listen[T any](bind string) (comm.Receiver[T], string, error) {
	ln, err := net.Listen("tcp", bind)
	if err != nil {
		return nil, "", err
	}
	r := &receiver[T]{ln: ln, ch: make(chan T, mailboxBuffer)}
	go r.accept()
	return r, ln.Addr().String(), nil
}

func (r *receiver[T]) accept() {
	for {
		conn, err := r.ln.Accept()
		if err != nil {
			return
		}
		go r.decode(conn)
	}
}

func (r *receiver[T]) decode(conn net.Conn) {
	defer conn.Close()
	dec := gob.NewDecoder(conn)
	for {
		var value T
		if err := dec.Decode(&value); err != nil {
			return
		}
		r.ch <- value
	}
}

// Recv returns the next value sent to this mailbox, blocking until one arrives.
// The boolean is always true: see Listen on why the medium is never reported
// gone.
func (r *receiver[T]) Recv() (T, bool) {
	v := <-r.ch
	return v, true
}

var (
	_ comm.Sender[int]   = (*sender[int])(nil)
	_ comm.Receiver[int] = (*receiver[int])(nil)
)
