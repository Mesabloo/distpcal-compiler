package comm

import (
	"testing"

	"github.com/mesabloo/fugue/runtime/tlaplus"
)

// recorder is a Sender that keeps what it was handed, standing in for whatever
// endpoint an integrator supplies.
type recorder struct {
	received []int
}

func (r *recorder) Send(value int) { r.received = append(r.received, value) }

// network builds the map shape a compiled Network struct holds for an indexed
// channel, one recorder per address.
func network(addrs ...int) (map[Address]Sender[int], map[int]*recorder) {
	ch := map[Address]Sender[int]{}
	rs := map[int]*recorder{}
	for _, a := range addrs {
		r := &recorder{}
		rs[a] = r
		ch[Address(intAddress(a))] = r
	}
	return ch, rs
}

// TestMulticastReachesEveryRecipient is the construct's whole contract: one
// message per member of the set, and none to anybody outside it.
func TestMulticastReachesEveryRecipient(t *testing.T) {
	ch, rs := network(1, 2, 3)
	to := tlaplus.MkSet(AddressOrd, Address(intAddress(1)), Address(intAddress(3)))

	Multicast(ch, to, func(Address) int { return 7 })

	if got := rs[1].received; len(got) != 1 || got[0] != 7 {
		t.Errorf("recipient 1 received %v, want [7]", got)
	}
	if got := rs[3].received; len(got) != 1 || got[0] != 7 {
		t.Errorf("recipient 3 received %v, want [7]", got)
	}
	if got := rs[2].received; len(got) != 0 {
		t.Errorf("address 2 is not in the set but received %v", got)
	}
}

// TestMulticastPayloadSeesTheRecipient covers the reason the payload is a
// function at all: the source construct binds the recipient and the message
// may depend on it.
func TestMulticastPayloadSeesTheRecipient(t *testing.T) {
	ch, rs := network(1, 2)
	to := tlaplus.MkSet(AddressOrd, Address(intAddress(1)), Address(intAddress(2)))

	Multicast(ch, to, func(a Address) int { return int(a.(intAddress)) * 10 })

	if got := rs[1].received; len(got) != 1 || got[0] != 10 {
		t.Errorf("recipient 1 received %v, want [10]", got)
	}
	if got := rs[2].received; len(got) != 1 || got[0] != 20 {
		t.Errorf("recipient 2 received %v, want [20]", got)
	}
}

// TestMulticastEmptySetSendsNothing: an empty recipient set is a legal
// multicast, not an error.
func TestMulticastEmptySetSendsNothing(t *testing.T) {
	ch, rs := network(1)

	Multicast(ch, tlaplus.MkSet(AddressOrd), func(Address) int { return 1 })

	if got := rs[1].received; len(got) != 0 {
		t.Errorf("an empty recipient set still delivered %v", got)
	}
}

// TestMulticastPanicsOnUnknownRecipient pins the documented choice for a
// recipient the channel has no endpoint for: indexing a function outside its
// domain is undefined in TLA+, and the runtime panics on undefined rather than
// dropping the message.
func TestMulticastPanicsOnUnknownRecipient(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Errorf("multicasting to an address with no endpoint did not panic")
		}
	}()

	ch, _ := network(1)
	to := tlaplus.MkSet(AddressOrd, Address(intAddress(2)))
	Multicast(ch, to, func(Address) int { return 1 })
}
