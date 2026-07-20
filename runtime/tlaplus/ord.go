// Package tlaplus is the runtime library the compiler's Go backend emits calls
// into. It is versioned with the compiler that targets it, not distributed
// separately.
//
// Each file corresponds to one TLA+ concept or standard module. Nothing here is
// specific to a particular specification: types generated per-specification
// (records, the process Network struct) are emitted by the compiler, along with
// the dictionaries witnessing their ordering.
package tlaplus

// Ord is the equality-and-ordering dictionary every operation that compares
// values takes explicitly.
//
// It is a struct of functions rather than an interface, and that is forced.
// Go's builtin == is not usable for TLA+ equality — set equality must ignore
// order, sets of sets must ignore it at every layer, and lazy functions must
// not compare caches, since two functions with equal graphs may have memoized
// different subsets of them. But an interface cannot express the obligation
// either, because Go has no conditional method sets: there is no way to say
// that Set[T] is ordered whenever T is. A method's receiver type parameters
// must repeat the declaration's constraints exactly, so `type Set[T any]` can
// have no method that calls T's own comparison, and `type Set[T Ord[T]]` would
// propagate the constraint into every use — making a tuple or a record with a
// function-typed component non-representable rather than merely non-comparable.
//
// A dictionary has neither problem. Set[T] stays [T any], and the ordering
// travels alongside the value rather than being attached to it: Set[Set[Int]]'s
// dictionary is SetOrd(SetOrd(IntOrd)), composed by the constructors in this
// package exactly as the compiler composes the type.
//
// Only Eq and Lt are primitive. Neq, Gt, Le, Ge and Cmp are derived once here
// rather than being supplied by every dictionary. Gt is derivable — which the
// interface version could not manage — because these are operations on two
// arguments rather than methods on a value, so flipping them is available.
//
// An ordering is required in more places than TLA+ itself demands one, because
// two of the representations chosen for TLA+ values are ordered structures:
// CHOOSE picks the minimum of the candidate set to stay deterministic, and
// lazy functions key their cache by a comparator derived from Cmp.
type Ord[T any] struct {
	Eq func(x, y T) bool
	Lt func(x, y T) bool
}

// Neq reports whether x and y differ, compiling TLA+'s #.
func (o Ord[T]) Neq(x, y T) bool { return !o.Eq(x, y) }

// Gt reports whether x sorts after y.
func (o Ord[T]) Gt(x, y T) bool { return o.Lt(y, x) }

// Le reports whether x is at most y.
func (o Ord[T]) Le(x, y T) bool { return o.Eq(x, y) || o.Lt(x, y) }

// Ge reports whether x is at least y.
func (o Ord[T]) Ge(x, y T) bool { return o.Eq(x, y) || o.Gt(x, y) }

// Cmp returns a negative number when x sorts before y, zero when they are
// equal, and a positive number when x sorts after y — the convention the
// standard library's slices package and this project's treemap both expect.
//
// It panics when a dictionary reports x as none of equal to, less than or
// greater than y, which means that dictionary is not a total order.
func (o Ord[T]) Cmp(x, y T) int {
	switch {
	case o.Eq(x, y):
		return 0
	case o.Lt(x, y):
		return -1
	case o.Gt(x, y):
		return 1
	}
	panic("Incomparable elements")
}
