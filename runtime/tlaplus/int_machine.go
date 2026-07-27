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

// Div compiles x \div y, TLA+'s integer division: the unique q with
// x = y*q + r and 0 <= r < |y|. That is Euclidean division. Go's / truncates
// toward zero, giving a negative remainder for a negative x, so the quotient
// is stepped one toward the sign of y to absorb it — matching int_big.go's use
// of big.Int's Div, which is Euclidean too (unlike Quo).
//
// TLA+ leaves x \div 0 undefined; Go panics on it, which surfaces the
// undefinedness rather than inventing a value for it.
func Div(x, y Int) Int {
	q := x / y
	if x%y < 0 {
		if y > 0 {
			q--
		} else {
			q++
		}
	}
	return q
}

// Mod compiles x % y, the remainder paired with Div: the r of x = y*q + r with
// 0 <= r < |y|. Go's % follows the sign of x, so a negative remainder is
// lifted by |y| to match big.Int's Euclidean Mod in int_big.go.
//
// Undefined at y = 0 in TLA+, and a panic here, as for Div.
func Mod(x, y Int) Int {
	r := x % y
	if r < 0 {
		if y > 0 {
			r += y
		} else {
			r -= y
		}
	}
	return r
}

// Pow compiles x ^ y, by squaring. It wraps on overflow, as Mul does.
//
// A negative exponent panics. TLA+'s ^ ranges over Reals, where 2^-1 is 1/2 —
// the compiler types it Int x Int -> Int (Reals being out of scope), so the
// case has no representable answer and is rejected at the point it arises
// rather than silently given one.
func Pow(x, y Int) Int {
	if y < 0 {
		panic("Negative exponent in ^: the result is not an integer")
	}
	acc := Int(1)
	for y > 0 {
		if y&1 == 1 {
			acc *= x
		}
		x *= x
		y >>= 1
	}
	return acc
}
