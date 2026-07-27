//go:build !fugue_machint

package tlaplus

import (
	"crypto/rand"
	"math/big"
)

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

// Div compiles x \div y, TLA+'s integer division: the unique q with
// x = y*q + r and 0 <= r < y. That is Euclidean division, which is what
// big.Int's Div implements — not Quo, which truncates toward zero and so
// disagrees for a negative x.
//
// TLA+ leaves x \div 0 undefined; big.Int panics on it, which surfaces the
// undefinedness rather than inventing a value for it.
func Div(x, y Int) Int { return Int{new(big.Int).Div(x.val(), y.val())} }

// Mod compiles x % y, the remainder paired with Div: the r of x = y*q + r with
// 0 <= r < |y|. big.Int's Mod is the Euclidean modulus, so the identity holds
// with Div above for a negative x too, where Rem's sign-following remainder
// would break it.
//
// Undefined at y = 0 in TLA+, and a panic here, as for Div.
func Mod(x, y Int) Int { return Int{new(big.Int).Mod(x.val(), y.val())} }

// Pow compiles x ^ y.
//
// A negative exponent panics. TLA+'s ^ ranges over Reals, where 2^-1 is 1/2 —
// the compiler types it Int x Int -> Int (Reals being out of scope), so the
// case has no representable answer and is rejected at the point it arises
// rather than silently given one. big.Int's Exp would answer 1.
func Pow(x, y Int) Int {
	if y.val().Sign() < 0 {
		panic("Negative exponent in ^: the result is not an integer")
	}
	return Int{new(big.Int).Exp(x.val(), y.val(), nil)}
}

// Rand returns a uniformly distributed integer in [lo, hi).
//
// An atomic block compiles to a loop that picks one of its branches at random
// and retries until one fires (thesis §7.2.3.1), and the two-argument shape is
// that use: generated code writes Rand(0, n) for an n-branch block. The picker
// is deliberately unfair — a branch can be passed over arbitrarily many times,
// matching the compiler's stance that PlusCal's fairness annotations are
// carried through unused. Nothing here is a scheduler in the operating-system
// sense: Go's runtime schedules the goroutines, and this only decides which
// branch a given iteration attempts. Pick in sets.go is the other caller.
//
// The source is crypto/rand rather than math/rand/v2, which this
// representation cannot use: v2 has no *big.Int path, and big.Int's own Rand
// wants a v1 *rand.Rand. Uniformity is what matters here, not
// unpredictability, so the choice costs speed and buys nothing beyond a
// working arbitrary-precision draw.
//
// It panics when hi <= lo, an empty range having no element to return. The
// compiler never emits one: an atomic block has at least one branch. It also
// panics if the entropy source fails, which nothing short of a broken system
// can cause.
func Rand(lo, hi Int) Int {
	n := new(big.Int).Sub(hi.val(), lo.val())
	if n.Sign() <= 0 {
		panic("Rand over an empty range")
	}
	k, err := rand.Int(rand.Reader, n)
	if err != nil {
		panic("Rand could not read from the system entropy source: " + err.Error())
	}
	return Int{k.Add(k, lo.val())}
}
