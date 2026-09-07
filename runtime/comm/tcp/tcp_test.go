package tcp

import (
	"net"
	"testing"
	"time"

	"github.com/mesabloo/fugue/runtime/comm"
	"github.com/mesabloo/fugue/runtime/tlaplus"
)

// startNameServer brings up a name server on a free port and returns its
// address.
func startNameServer(t *testing.T) string {
	t.Helper()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("could not bind a name server listener: %v", err)
	}
	go serveNameServerOn(ln)
	return ln.Addr().String()
}

// TestLookupResolvesRegistration is the ordinary path: a name registered before
// it is looked up resolves to the address it was registered with.
func TestLookupResolvesRegistration(t *testing.T) {
	ns := startNameServer(t)

	if err := Register(ns, "Ping", "10.0.0.1:7001"); err != nil {
		t.Fatalf("Register: %v", err)
	}
	got, err := Lookup(ns, "Ping")
	if err != nil {
		t.Fatalf("Lookup: %v", err)
	}
	if got != "10.0.0.1:7001" {
		t.Errorf("Lookup(Ping) = %q, want %q", got, "10.0.0.1:7001")
	}
}

// TestLookupParksUntilRegistered pins the ordering guarantee: a Lookup for a
// name nobody has registered yet blocks rather than failing, and returns once
// the name arrives.
func TestLookupParksUntilRegistered(t *testing.T) {
	ns := startNameServer(t)

	resolved := make(chan string, 1)
	go func() {
		addr, err := Lookup(ns, "Pong1")
		if err != nil {
			t.Errorf("Lookup: %v", err)
		}
		resolved <- addr
	}()

	select {
	case <-resolved:
		t.Fatal("Lookup returned before the name was registered")
	case <-time.After(50 * time.Millisecond):
	}

	if err := Register(ns, "Pong1", "10.0.0.2:7002"); err != nil {
		t.Fatalf("Register: %v", err)
	}

	select {
	case addr := <-resolved:
		if addr != "10.0.0.2:7002" {
			t.Errorf("Lookup(Pong1) = %q, want %q", addr, "10.0.0.2:7002")
		}
	case <-time.After(time.Second):
		t.Fatal("Lookup did not return after the name was registered")
	}
}

// TestEndpointRoundTripCarriesAddress sends the shape Ping-Pong's ping channel
// carries — a record with a Str and an interface-typed address — through a
// Dial/Listen pair, checking both that gob moves it and that the address
// arrives as a Name that compares equal to the one that was sent.
func TestEndpointRoundTripCarriesAddress(t *testing.T) {
	type message = struct {
		From comm.Address
		Mes  tlaplus.Str
	}

	mailbox, addr, err := Listen[message]("127.0.0.1:0")
	if err != nil {
		t.Fatalf("Listen: %v", err)
	}

	out := Dial[message](addr)
	out.Send(message{From: Name("Pong1"), Mes: tlaplus.Str("Ping")})

	done := make(chan message, 1)
	go func() {
		v, _ := mailbox.Recv()
		done <- v
	}()

	select {
	case got := <-done:
		if got.Mes != "Ping" {
			t.Errorf("Mes = %q, want %q", got.Mes, "Ping")
		}
		if !comm.AddressOrd.Eq(got.From, comm.Address(Name("Pong1"))) {
			t.Errorf("From = %v, want Name(Pong1)", got.From)
		}
	case <-time.After(time.Second):
		t.Fatal("nothing arrived at the mailbox")
	}
}
