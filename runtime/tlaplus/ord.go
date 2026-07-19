package tlaplus

// Ord is the ordering interface, a super-interface of Eq: a type implementing
// Ord must implement Eq first.
//
// Only Gt and Lt are primitive. Le, Ge and Cmp below are derived once,
// generically, rather than being reimplemented by every type.
//
// An ordering is required in more places than TLA+ itself demands one, because
// two of the representations chosen for TLA+ values are ordered structures:
// CHOOSE picks the minimum of the candidate set to stay deterministic, and
// lazy functions key their cache by a comparator derived from Cmp.
type Ord[T any] interface {
	Eq[T]

	Gt(other T) bool
	Lt(other T) bool
}

// Le reports whether x is at most y.
func Le[T Ord[T]](x, y T) bool { return x.Eq(y) || x.Lt(y) }

// Ge reports whether x is at least y.
func Ge[T Ord[T]](x, y T) bool { return x.Eq(y) || x.Gt(y) }

// Cmp returns a negative number when x sorts before y, zero when they are
// equal, and a positive number when x sorts after y — the convention the
// standard library's slices package and this project's treemap both expect.
//
// It panics when an implementation reports x as none of equal to, greater than
// or less than y, which means that implementation is not a total order.
func Cmp[T Ord[T]](x, y T) int {
	switch {
	case x.Eq(y):
		return 0
	case x.Gt(y):
		return 1
	case x.Lt(y):
		return -1
	}
	panic("Incomparable elements")
}
