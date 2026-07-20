//go:build !fugue_machint

package tlaplus

import (
	"math"
	"math/big"
	"testing"
)

// TestExceedsMachineRange is the point of the default representation: values
// beyond a machine integer must be computed exactly rather than wrapping.
//
// It is build-tagged because it cannot hold under -tags fugue_machint, where
// the same computation is expected to wrap. Nothing else in the suite would
// notice the difference, since MkInt takes a machine int and so no literal can
// express an out-of-range value.
func TestExceedsMachineRange(t *testing.T) {
	// 2^64, four squarings up from 2^4.
	n := MkInt(16)
	for range 4 {
		n = Mul(n, n)
	}

	want := new(big.Int).Lsh(big.NewInt(1), 64)
	if got := n.val(); got.Cmp(want) != 0 {
		t.Fatalf("2^64 computed as %v, want %v", got, want)
	}
	if n.val().IsInt64() {
		t.Errorf("2^64 fits in an int64, so this test proves nothing")
	}

	// Arithmetic keeps working out there, rather than saturating.
	if got := Sub(n, MkInt(1)); !got.val().IsUint64() || got.val().Uint64() != math.MaxUint64 {
		t.Errorf("2^64 - 1 = %v, want %d", got, uint64(math.MaxUint64))
	}
	if got := Add(n, MkInt(0)); !IntOrd.Eq(got, n) {
		t.Errorf("adding zero out of machine range changed the value")
	}
	if !IntOrd.Gt(n, MkInt(math.MaxInt64)) {
		t.Errorf("2^64 does not compare as greater than MaxInt64")
	}
}

// TestToIntRejectsOutOfRange checks the documented panic, which is the price of
// letting sequences index with machine integers.
func TestToIntRejectsOutOfRange(t *testing.T) {
	n := MkInt(1)
	for range 4 {
		n = Mul(n, MkInt(math.MaxInt32))
	}

	defer func() {
		if recover() == nil {
			t.Errorf("ToInt of an out-of-range value did not panic")
		}
	}()
	ToInt(n)
}
