package comm

import (
	"testing"

	"github.com/mesabloo/fugue/runtime/tlaplus"
)

// intAddress is a minimal integrator-supplied Address, standing in for the real
// thing: a socket path, a host and port, an index into a table. It orders
// numerically, which is exactly the arbitrary-but-total choice the interface
// documents as the integrator's to make.
type intAddress int

func (a intAddress) Eq(other Address) bool { return a == other.(intAddress) }
func (a intAddress) Lt(other Address) bool { return a < other.(intAddress) }

// TestAddressOrdBridges checks the method-expression bridge: the dictionary's
// operations must dispatch to the implementation's methods, receiver first.
func TestAddressOrdBridges(t *testing.T) {
	one, two := Address(intAddress(1)), Address(intAddress(2))

	if !AddressOrd.Eq(one, one) {
		t.Errorf("an address is not equal to itself")
	}
	if AddressOrd.Eq(one, two) {
		t.Errorf("two distinct addresses compare equal")
	}
	if !AddressOrd.Lt(one, two) || AddressOrd.Lt(two, one) {
		t.Errorf("the bridged ordering does not follow the implementation's")
	}
	// The derived operations come from the same two, so a wrong argument order
	// in the bridge would show up here as Gt agreeing with Lt.
	if !AddressOrd.Gt(two, one) || AddressOrd.Gt(one, two) {
		t.Errorf("Gt does not flip Lt")
	}
	if got := AddressOrd.Cmp(one, two); got >= 0 {
		t.Errorf("Cmp(1, 2) = %d, want negative", got)
	}
}

// TestAddressReachesContainers is the reason the interface demands an order at
// all: addresses appear in sets and as the domain of a function in the very
// first example specification.
func TestAddressReachesContainers(t *testing.T) {
	addrs := tlaplus.MkSet(AddressOrd, Address(intAddress(3)), Address(intAddress(1)), Address(intAddress(3)))
	if len(addrs) != 2 {
		t.Fatalf("the address set has %d elements, want 2", len(addrs))
	}
	if !tlaplus.SetIn(AddressOrd, addrs, Address(intAddress(1))) {
		t.Errorf("an address built separately is not found in the set")
	}

	// CHOOSE picks the minimum, so this is the documented
	// implementation-dependence in action: the answer is 1 because intAddress
	// happens to order numerically.
	if got := tlaplus.Choose(addrs, func(Address) bool { return true }); !AddressOrd.Eq(got, Address(intAddress(1))) {
		t.Errorf("CHOOSE gave %v, want the minimum under the supplied order", got)
	}

	f := tlaplus.FnConstructor(AddressOrd, addrs, func(a Address) tlaplus.Int {
		return tlaplus.MkInt(int(a.(intAddress)))
	})
	if got := tlaplus.FnApply(AddressOrd, f, Address(intAddress(3))); !tlaplus.IntOrd.Eq(got, tlaplus.MkInt(3)) {
		t.Errorf("f[3] = %v, want 3", got)
	}
}
