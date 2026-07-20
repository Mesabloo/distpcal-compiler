package tlaplus

// Bool is the TLA+ BOOLEAN type.
//
// It is a newtype over Go's bool rather than bool itself so that the compiler
// has one name to emit for it, and so that a dictionary can be declared for it
// here rather than for a type this package does not own.
type Bool bool

// BoolOrd is the dictionary for Bool.
//
// The ordering puts FALSE before TRUE. TLA+ does not order booleans, so the
// direction is arbitrary; what matters is that it is total and fixed, since
// sets rely on their element ordering for their representation.
var BoolOrd = Ord[Bool]{
	Eq: func(x, y Bool) bool { return x == y },
	Lt: func(x, y Bool) bool { return !bool(x) && bool(y) },
}
