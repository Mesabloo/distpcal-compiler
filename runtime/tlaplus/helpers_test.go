package tlaplus

import "slices"

// Helpers for writing tests against Int without spelling MkInt at every
// literal.
//
// These build real Int values, so the tests exercise whichever representation
// the build tag selected rather than a stand-in.

// ints builds a slice of Int.
func ints(ns ...int) []Int {
	out := make([]Int, len(ns))
	for i, n := range ns {
		out[i] = MkInt(n)
	}
	return out
}

// intSet builds a set, normalizing as MkSet does.
func intSet(ns ...int) Set[Int] { return MkSet(IntOrd, ints(ns...)...) }

// rawIntSet builds a Set from the given elements *without* normalizing, for
// tests that need to observe what an operation does to an arbitrary slice.
func rawIntSet(ns ...int) Set[Int] { return Set[Int](ints(ns...)) }

// intSeq builds a sequence.
func intSeq(ns ...int) Seq[Int] { return MkSeq(ints(ns...)...) }

// intsEqual compares by value.
//
// slices.Equal must not be used on []Int: under the arbitrary-precision
// representation Int is a struct holding a *big.Int, which is comparable, so
// slices.Equal compiles and then compares pointer identity — quietly reporting
// equal values as different.
func intsEqual(a, b []Int) bool {
	return slices.EqualFunc(a, b, IntOrd.Eq)
}

// eqInt reports whether x equals the given machine integer.
func eqInt(x Int, n int) bool { return IntOrd.Eq(x, MkInt(n)) }
