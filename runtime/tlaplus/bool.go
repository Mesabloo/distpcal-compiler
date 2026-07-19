package tlaplus

// Bool is the TLA+ BOOLEAN type.
//
// It is a newtype over Go's bool rather than bool itself because Go forbids
// implementing an interface for a type declared in another package, and every
// value in generated code has to implement Eq and Ord.
type Bool bool

// Eq reports whether two booleans are equal.
func (b Bool) Eq(other Bool) bool { return b == other }

// Gt reports whether b is TRUE and other is FALSE.
func (b Bool) Gt(other Bool) bool { return bool(b) && !bool(other) }

// Lt reports whether b is FALSE and other is TRUE.
//
// The ordering puts FALSE before TRUE. TLA+ does not order booleans, so the
// direction is arbitrary; what matters is that it is total and fixed, since
// sets rely on their element ordering for their representation.
func (b Bool) Lt(other Bool) bool { return !bool(b) && bool(other) }
