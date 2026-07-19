package tlaplus

// Str is the TLA+ STRING type.
//
// It is a newtype over Go's string rather than string itself because Go forbids
// implementing an interface for a type declared in another package, and every
// value in generated code has to implement Eq and Ord.
type Str string

// Eq reports whether two strings are equal.
func (s Str) Eq(other Str) bool { return s == other }

// Gt reports whether s sorts after other.
func (s Str) Gt(other Str) bool { return s > other }

// Lt reports whether s sorts before other.
//
// The comparison is bytewise, which is Go's own ordering on strings. TLA+ does
// not specify one, so this only has to be total and fixed — sets rely on their
// element ordering for their representation.
func (s Str) Lt(other Str) bool { return s < other }
