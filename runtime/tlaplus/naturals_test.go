package tlaplus

import (
	"slices"
	"testing"
)

func TestArithmetic(t *testing.T) {
	cases := []struct {
		name string
		got  Int
		want int
	}{
		{"Add", Add(MkInt(2), MkInt(3)), 5},
		{"Add negative", Add(MkInt(2), MkInt(-3)), -1},
		{"Sub", Sub(MkInt(5), MkInt(3)), 2},
		{"Sub below zero", Sub(MkInt(3), MkInt(5)), -2},
		{"Neg", Neg(MkInt(4)), -4},
		{"Neg of negative", Neg(MkInt(-4)), 4},
		{"Neg of zero", Neg(MkInt(0)), 0},
		{"Mul", Mul(MkInt(3), MkInt(4)), 12},
		{"Mul by zero", Mul(MkInt(3), MkInt(0)), 0},
		{"Mul negative", Mul(MkInt(-3), MkInt(4)), -12},
	}
	for _, c := range cases {
		if !eqInt(c.got, c.want) {
			t.Errorf("%s = %v, want %d", c.name, c.got, c.want)
		}
	}
}

// TestZeroValueIsZero is specific to the arbitrary-precision representation,
// where Int wraps a pointer that starts nil. Generated code declares variables
// with Go's `var x Int`, so every operation has to read that as 0 rather than
// dereferencing it.
func TestZeroValueIsZero(t *testing.T) {
	var zero Int

	if !eqInt(zero, 0) {
		t.Errorf("the zero value is not equal to 0")
	}
	if !eqInt(Add(zero, MkInt(3)), 3) {
		t.Errorf("Add on the zero value = %v, want 3", Add(zero, MkInt(3)))
	}
	if !eqInt(Add(MkInt(3), zero), 3) {
		t.Errorf("Add with the zero value on the right = %v, want 3", Add(MkInt(3), zero))
	}
	if !eqInt(Sub(zero, MkInt(3)), -3) {
		t.Errorf("Sub from the zero value = %v, want -3", Sub(zero, MkInt(3)))
	}
	if !eqInt(Mul(zero, MkInt(3)), 0) {
		t.Errorf("Mul on the zero value = %v, want 0", Mul(zero, MkInt(3)))
	}
	if !eqInt(Neg(zero), 0) {
		t.Errorf("Neg of the zero value = %v, want 0", Neg(zero))
	}
	if IntOrd.Lt(zero, MkInt(0)) || IntOrd.Gt(zero, MkInt(0)) {
		t.Errorf("the zero value does not compare as 0")
	}
	if got := ToInt(zero); got != 0 {
		t.Errorf("ToInt of the zero value = %d, want 0", got)
	}
	// Two independently declared zero values must be equal to each other, not
	// merely each equal to a constructed 0.
	var other Int
	if !IntOrd.Eq(zero, other) {
		t.Errorf("two zero values are not equal")
	}
}

// TestIntRoundTrip checks MkInt and ToInt against each other, including the
// boundaries where a machine integer stops being representable.
func TestIntRoundTrip(t *testing.T) {
	for _, n := range []int{0, 1, -1, 42, -42, 1 << 31, -(1 << 31)} {
		if got := ToInt(MkInt(n)); got != n {
			t.Errorf("ToInt(MkInt(%d)) = %d", n, got)
		}
	}
}

func TestIntRange(t *testing.T) {
	cases := []struct {
		lo, hi int
		want   []Int
	}{
		{1, 5, ints(1, 2, 3, 4, 5)},
		{0, 0, ints(0)},
		{-2, 2, ints(-2, -1, 0, 1, 2)},
		{-5, -3, ints(-5, -4, -3)},
		// hi < lo is the empty set, not an error and not a descending range.
		{5, 1, ints()},
		{1, 0, ints()},
	}
	for _, c := range cases {
		got := IntRange(MkInt(c.lo), MkInt(c.hi))
		if !intsEqual(got, c.want) {
			t.Errorf("%d..%d = %v, want %v", c.lo, c.hi, got, c.want)
		}
	}
}

// TestIntRangeSatisfiesSetInvariants checks that a range is usable as a Set
// without normalization: sorted, duplicate-free, and searchable by SetIn.
func TestIntRangeSatisfiesSetInvariants(t *testing.T) {
	r := IntRange(MkInt(-3), MkInt(7))

	if !slices.IsSortedFunc(r, IntOrd.Cmp) {
		t.Errorf("IntRange is not sorted: %v", r)
	}
	if normalized := MkSet(IntOrd, r...); !intsEqual(r, normalized) {
		t.Errorf("IntRange needed normalization: %v became %v", r, normalized)
	}
	for i := -3; i <= 7; i++ {
		if !SetIn(IntOrd, r, MkInt(i)) {
			t.Errorf("SetIn(-3..7, %d) = false, want true", i)
		}
	}
	for _, i := range []int{-4, 8, 100} {
		if SetIn(IntOrd, r, MkInt(i)) {
			t.Errorf("SetIn(-3..7, %d) = true, want false", i)
		}
	}
	if got := Choose(r, func(x Int) bool { return IntOrd.Gt(x, MkInt(0)) }); !eqInt(got, 1) {
		t.Errorf("CHOOSE x \\in -3..7 : x > 0 = %v, want 1", got)
	}
}
