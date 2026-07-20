//go:build !fugue_machint

package tlaplus

import "math/big"

// Int is the TLA+ Int type, represented with arbitrary precision.
//
// This is the default. TLA+ integers are unbounded, and so are the integers of
// the denotational semantics the compiler is verified against, so a machine
// integer would silently wrap where the semantics says it should not — leaving
// any correctness argument to carry an overflow side condition on every
// arithmetic step. Building with -tags fugue_machint selects the faster
// machine-integer representation instead, accepting that trade.
//
// The struct wrapper is not an abstraction boundary; it is forced. Go does not
// allow methods on a defined pointer type, so `type Int *big.Int` could not
// carry the String method below.
//
// The zero value is a valid zero. Generated code declares variables with Go's
// `var x Int`, which leaves the pointer nil, so every operation reads it
// through val rather than dereferencing directly.
type Int struct{ v *big.Int }

// val returns the underlying value, treating the nil zero value as 0.
//
// The result must not be mutated: it may be the receiver's own value, shared
// with every copy of it.
func (n Int) val() *big.Int {
	if n.v == nil {
		return zeroInt
	}
	return n.v
}

// zeroInt backs the zero value. It is never mutated — every operation below
// allocates its result.
var zeroInt = big.NewInt(0)

// MkInt builds an Int from a machine integer, which is what an integer literal
// in a specification compiles to.
//
// A literal too large for a machine int is rejected by the Go compiler at the
// call site, since the argument is an untyped constant. Such a specification is
// out of range for the machine-integer build in any case.
func MkInt(n int) Int { return Int{big.NewInt(int64(n))} }

// ToInt converts back to a machine integer, for the places Go itself demands
// one — slice indices, lengths, capacities.
//
// It panics on a value too large to represent. That departs from TLA+, where
// the integer is perfectly well defined; the justification is that the only
// callers are indexing operations, and a sequence long enough to need such an
// index cannot be represented in memory to begin with.
func ToInt(n Int) int {
	v := n.val()
	if !v.IsInt64() {
		panic("Integer too large to use as a machine integer")
	}
	i := v.Int64()
	if int64(int(i)) != i {
		panic("Integer too large to use as a machine integer")
	}
	return int(i)
}

// IntOrd is the dictionary for Int, ordering by numeric value.
//
// Both operations go through val, so the nil zero value compares as 0 rather
// than panicking.
var IntOrd = Ord[Int]{
	Eq: func(x, y Int) bool { return x.val().Cmp(y.val()) == 0 },
	Lt: func(x, y Int) bool { return x.val().Cmp(y.val()) < 0 },
}

// String renders the integer in base 10.
func (n Int) String() string { return n.val().String() }

// Add compiles x + y.
func Add(x, y Int) Int { return Int{new(big.Int).Add(x.val(), y.val())} }

// Sub compiles x - y.
func Sub(x, y Int) Int { return Int{new(big.Int).Sub(x.val(), y.val())} }

// Neg compiles unary -x.
func Neg(x Int) Int { return Int{new(big.Int).Neg(x.val())} }

// Mul compiles x * y.
func Mul(x, y Int) Int { return Int{new(big.Int).Mul(x.val(), y.val())} }
