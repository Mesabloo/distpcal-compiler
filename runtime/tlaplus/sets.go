package tlaplus

import "slices"

// Set is the representation of TLA+'s Set(t).
//
// The underlying slice carries two invariants the Go type cannot express: it is
// sorted ascending by the element type's own ordering, and it holds no
// duplicates. Every function here that constructs a Set is responsible for
// establishing both; every function that consumes one may rely on them.
//
// Sortedness is not required by TLA+ — a set has no order — but choosing a
// canonical representative for each set is what makes the operations on it
// cheap. Equality becomes an elementwise walk rather than a double subset test,
// membership a binary search rather than a scan, and CHOOSE's deterministic
// pick the first element rather than a search for the minimum. It also gives
// deduplication somewhere natural to happen, since sorting brings equal
// elements together.
//
// Computability restricts this to finite sets. Representing a set by its
// characteristic predicate — func(x t) bool — would admit infinite ones, but
// then set equality is not computable, so it is not an option here.
type Set[T any] []T

// MkSet builds a set from elements in arbitrary order, sorting and
// deduplicating them.
//
// This is what a set literal {e1, ..., en} compiles to. A bare composite
// literal will not do: whether two of those expressions denote the same value
// is generally not decidable until they are evaluated, so the literal may
// hold the same element twice and may hold it out of order.
func MkSet[T Ord[T]](elems ...T) Set[T] {
	return normalize(Set[T](elems))
}

// normalize establishes both invariants on a freshly built slice. It sorts in
// place and must therefore only ever be handed a slice its caller owns.
func normalize[T Ord[T]](s Set[T]) Set[T] {
	slices.SortFunc(s, Cmp[T])
	return slices.CompactFunc(s, func(a, b T) bool { return a.Eq(b) })
}

// SetIn reports whether x is an element of s, by binary search on the sorted
// representation.
func SetIn[T Ord[T]](s Set[T], x T) bool {
	_, found := slices.BinarySearchFunc(s, x, Cmp[T])
	return found
}

// SetEq reports whether two sets have the same elements.
//
// Because both are sorted and duplicate-free, equal sets are equal slices
// elementwise, so this is a single linear walk rather than a subset test in
// each direction.
func SetEq[T Eq[T]](s, other Set[T]) bool {
	return slices.EqualFunc(s, other, func(a, b T) bool { return a.Eq(b) })
}

// SetFilter compiles {x \in s : p(x)}.
//
// Removing elements preserves both invariants, so the result needs no
// renormalization. TLA+ values are immutable, so this copies before filtering:
// slices.DeleteFunc compacts in place and would otherwise corrupt s, which
// callers may still hold and which may share a backing array with other sets.
func SetFilter[T any](s Set[T], p func(y T) bool) Set[T] {
	return slices.DeleteFunc(slices.Clone(s), func(y T) bool { return !p(y) })
}

// SetMap compiles {f(x) : x \in s}.
//
// Neither invariant survives a mapping: f need not be monotone, so the results
// come out in no particular order, and it need not be injective either, so
// {x % 2 : x \in {1, 2, 3}} is two elements from three. Hence the constraint on
// U, and the renormalization.
func SetMap[T any, U Ord[U]](s Set[T], f func(y T) U) Set[U] {
	out := make(Set[U], len(s))
	for i, y := range s {
		out[i] = f(y)
	}
	return normalize(out)
}

// SetUnion compiles s \cup other, SetIntersect s \cap other, and
// SetDifference s \ other.
//
// All three merge the two sorted representations in one pass rather than
// building a result and renormalizing it: the operands are sorted and
// duplicate-free, so the output comes out that way by construction. None of
// them writes through either operand, both of which the caller still holds.
func SetUnion[T Ord[T]](s, other Set[T]) Set[T] {
	out := make(Set[T], 0, len(s)+len(other))
	i, j := 0, 0
	for i < len(s) && j < len(other) {
		switch c := Cmp(s[i], other[j]); {
		case c < 0:
			out = append(out, s[i])
			i++
		case c > 0:
			out = append(out, other[j])
			j++
		default:
			out = append(out, s[i])
			i++
			j++
		}
	}
	out = append(out, s[i:]...)
	return append(out, other[j:]...)
}

func SetIntersect[T Ord[T]](s, other Set[T]) Set[T] {
	out := make(Set[T], 0, min(len(s), len(other)))
	i, j := 0, 0
	for i < len(s) && j < len(other) {
		switch c := Cmp(s[i], other[j]); {
		case c < 0:
			i++
		case c > 0:
			j++
		default:
			out = append(out, s[i])
			i++
			j++
		}
	}
	return out
}

func SetDifference[T Ord[T]](s, other Set[T]) Set[T] {
	out := make(Set[T], 0, len(s))
	i, j := 0, 0
	for i < len(s) && j < len(other) {
		switch c := Cmp(s[i], other[j]); {
		case c < 0:
			out = append(out, s[i])
			i++
		case c > 0:
			j++
		default:
			i++
			j++
		}
	}
	return append(out, s[i:]...)
}

// SetSubseteq compiles s \subseteq other.
//
// Walks both sorted representations once looking for an element of s that other
// does not have, rather than doing len(s) binary searches.
func SetSubseteq[T Ord[T]](s, other Set[T]) bool {
	j := 0
	for i := 0; i < len(s); i++ {
		for j < len(other) && Cmp(other[j], s[i]) < 0 {
			j++
		}
		if j == len(other) || !other[j].Eq(s[i]) {
			return false
		}
	}
	return true
}

// Cardinality compiles FiniteSets!Cardinality(s). The representation is
// duplicate-free, so the element count is the slice length.
//
// FiniteSets!IsFiniteSet needs no counterpart here: every Set is finite by
// construction, so it compiles to the constant true.
func Cardinality[T any](s Set[T]) Int {
	return MkInt(len(s))
}

// Choose compiles CHOOSE x \in s : p(x).
//
// Hilbert's choice operator is deterministic — (CHOOSE x \in s : p) = (CHOOSE x
// \in s : p) has to hold — so this cannot pick at random. Taking the smallest
// satisfying element makes the result depend only on the set's contents, which
// is required: CHOOSE x \in {1, 2} : p and CHOOSE x \in {2, 1} : p must agree,
// those being the same set. Since the representation is sorted, the smallest
// satisfying element is the first one encountered, so this neither builds the
// filtered set nor searches it for a minimum.
//
// It panics when no element satisfies p, that being an undefined expression in
// TLA+.
func Choose[T any](s Set[T], p func(y T) bool) T {
	for _, y := range s {
		if p(y) {
			return y
		}
	}
	panic("CHOOSE in an empty set")
}
