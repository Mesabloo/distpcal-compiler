package tlaplus

// Str is the TLA+ STRING type.
//
// It is a newtype over Go's string rather than string itself so that the
// compiler has one name to emit for it, and so that a dictionary can be
// declared for it here rather than for a type this package does not own.
type Str string

// StrOrd is the dictionary for Str.
//
// The comparison is bytewise, which is Go's own ordering on strings. TLA+ does
// not specify one, so this only has to be total and fixed — sets rely on their
// element ordering for their representation.
var StrOrd = Ord[Str]{
	Eq: func(x, y Str) bool { return x == y },
	Lt: func(x, y Str) bool { return x < y },
}
