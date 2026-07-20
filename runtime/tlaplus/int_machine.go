//go:build fugue_machint

package tlaplus

import "strconv"

// Int is the TLA+ Int type, refined to a machine integer.
//
// This representation is selected by building with -tags fugue_machint. It
// is faster — no allocation per operation — but unsound against the semantics
// the compiler is verified against, since Go's int is 32 or 64 bits wide per
// the language specification and wraps on overflow where TLA+ integers are
// unbounded. The default build uses arbitrary precision; see int_big.go.
//
// It is a newtype over Go's int rather than int itself so that the compiler
// has one name to emit for it whichever representation is selected, and so
// that a dictionary can be declared for it here rather than for a type this
// package does not own.
type Int int

// MkInt builds an Int from a machine integer, which is what an integer literal
// in a specification compiles to.
//
// A literal too large for a machine int is rejected by the Go compiler at the
// call site, since the argument is an untyped constant. That is this
// representation's defining restriction, surfacing where it should.
func MkInt(n int) Int { return Int(n) }

// ToInt converts to a machine integer, for the places Go itself demands one.
// It cannot fail in this representation.
func ToInt(n Int) int { return int(n) }

// IntOrd is the dictionary for Int, ordering by numeric value.
var IntOrd = Ord[Int]{
	Eq: func(x, y Int) bool { return x == y },
	Lt: func(x, y Int) bool { return x < y },
}

// String renders the integer in base 10.
func (n Int) String() string { return strconv.Itoa(int(n)) }

// Add compiles x + y. It wraps on overflow, as Go's own + does.
func Add(x, y Int) Int { return x + y }

// Sub compiles x - y. It wraps on overflow.
func Sub(x, y Int) Int { return x - y }

// Neg compiles unary -x.
func Neg(x Int) Int { return -x }

// Mul compiles x * y. It wraps on overflow.
func Mul(x, y Int) Int { return x * y }
