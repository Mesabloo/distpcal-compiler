// Package tlaplus is the runtime library the compiler's Go backend emits calls
// into. It is versioned with the compiler that targets it, not distributed
// separately.
//
// Each file corresponds to one TLA+ concept or standard module. Nothing here is
// specific to a particular specification: types generated per-specification
// (records, tuples, the process Network struct) are emitted by the compiler and
// implement the interfaces declared here.
package tlaplus

// Eq is the equality interface every value in generated code implements.
//
// Go's builtin == is not usable for TLA+ equality. It cannot be implemented for
// a custom type — the comparable constraint is structural and not something a
// type can opt into — and it would be wrong even where it applies: set equality
// must ignore order, sets of sets must ignore it at every layer, and lazy
// functions must not compare caches, since two functions with equal graphs may
// have memoized different subsets of them.
// Go interfaces cannot be implemented for types declared in another package,
// which rules out implementing this one directly for bool, int and string. The
// primitive TLA+ types therefore get local newtypes, one per file: Bool, Int
// and Str.
type Eq[T any] interface {
	Eq(other T) bool
}

// Neq reports whether x and y differ, compiling TLA+'s #.
//
// Derived once here rather than being a second method every type has to
// implement, for the same reason Le, Ge and Cmp are derived from Gt and Lt.
func Neq[T Eq[T]](x, y T) bool { return !x.Eq(y) }
