package tlaplus

import "slices"

// Seq is the representation of TLA+'s Seq(t).
//
// TLA+ sequences are 1-indexed, so the underlying slice keeps slot 0 unused:
// element i of the sequence lives at index i of the slice. That slot is never
// observed, and its contents are meaningless — it exists so that indexing needs
// no arithmetic, which is the operation sequences see most.
//
// A sequence of n elements therefore has an underlying length of n+1, with one
// exception: the zero value (a nil slice) is a valid empty sequence, so that
// `var s Seq[T]` in generated code needs no initialization. Len accounts for
// it.
//
// Unlike Set, Seq carries no ordering or uniqueness invariant. A sequence is
// ordered by definition and may repeat elements.
type Seq[T any] []T

// MkSeq builds a sequence from its elements, in order.
//
// This is what a sequence literal <<e1, ..., en>> compiles to. A bare composite
// literal will not do: it would put the first element in the unused slot.
func MkSeq[T any](elems ...T) Seq[T] {
	var unused T
	return append(Seq[T]{unused}, elems...)
}

// length is Len as a machine integer, for internal use where Go itself needs
// one. Kept separate so that the public Len can speak in TLA+ integers without
// every caller here converting back.
func length[T any](s Seq[T]) int {
	if len(s) == 0 {
		return 0
	}
	return len(s) - 1
}

// Len compiles Len(s).
//
// The nil sequence and the sequence holding only the unused slot are both
// empty, and both report zero.
func Len[T any](s Seq[T]) Int {
	return MkInt(length(s))
}

// checkIndex converts a TLA+ index to a slice index, rejecting anything outside
// 1..Len(s).
//
// Out of range is undefined in TLA+, hence the panic rather than reading the
// unused slot or running off the end. ToInt panics in its own right on an index
// too large to be a machine integer, which no representable sequence could have
// been indexed by anyway.
func checkIndex[T any](s Seq[T], i Int) int {
	idx := ToInt(i)
	if idx < 1 || idx > length(s) {
		panic("Sequence index out of bounds")
	}
	return idx
}

// SeqIndex compiles the application s[i].
//
// Indices run from 1 to Len(s); anything else is undefined in TLA+.
func SeqIndex[T any](s Seq[T], i Int) T {
	return s[checkIndex(s, i)]
}

// SeqUpdate compiles the sequence case of [s EXCEPT ![i] = e], and PlusCal's
// s[i] := e.
//
// It copies: TLA+ values are immutable, so overwriting in place would be
// visible through every other sequence sharing this backing array, which
// includes every result of Tail. Indices run from 1 to Len(s), as for
// SeqIndex.
func SeqUpdate[T any](s Seq[T], i Int, e T) Seq[T] {
	idx := checkIndex(s, i)
	out := slices.Clone(s)
	out[idx] = e
	return out
}

// Head compiles Head(s). It panics on the empty sequence, that being undefined
// in TLA+.
func Head[T any](s Seq[T]) T {
	if length(s) == 0 {
		panic("Head of an empty sequence")
	}
	return s[1]
}

// Tail compiles Tail(s). It panics on the empty sequence, that being undefined
// in TLA+.
//
// Dropping the first element is a reslice rather than a copy: the old element 1
// becomes the new unused slot, and every subsequent element shifts down one
// index for free. This shares the backing array with s, which is safe because
// nothing here writes through a Seq — see Append.
func Tail[T any](s Seq[T]) Seq[T] {
	if length(s) == 0 {
		panic("Tail of an empty sequence")
	}
	return s[1:]
}

// Append compiles Append(s, e).
//
// This copies rather than appending in place. TLA+ values are immutable, and
// appending to a slice with spare capacity would write into a backing array
// that s — or any sequence sharing it, as every result of Tail does — is still
// using.
//
// The empty case goes through MkSeq rather than falling into the append below,
// which would otherwise put e at index 0: the unused slot, where Len cannot
// count it and Head cannot reach it.
func Append[T any](s Seq[T], e T) Seq[T] {
	if len(s) == 0 {
		return MkSeq(e)
	}
	return append(slices.Clone(s), e)
}

// SeqEq reports whether two sequences are equal: same length, equal elements,
// in the same order.
// The comparison starts at index 1: the unused slot is never observed, so two
// sequences agreeing everywhere it can be read are equal whatever it holds.
func SeqEq[T any](o Ord[T], s, other Seq[T]) bool {
	if length(s) != length(other) {
		return false
	}
	for i := 1; i <= length(s); i++ {
		if !o.Eq(s[i], other[i]) {
			return false
		}
	}
	return true
}

// SeqCmp orders two sequences lexicographically, shorter-and-equal-prefix
// first.
//
// TLA+ does not order sequences, so the direction is arbitrary; it exists so
// that a sequence can be an element of a set, a member of a function's domain,
// or a component of a tuple.
func SeqCmp[T any](o Ord[T], s, other Seq[T]) int {
	for i := 1; i <= min(length(s), length(other)); i++ {
		if c := o.Cmp(s[i], other[i]); c != 0 {
			return c
		}
	}
	return length(s) - length(other)
}

// SeqOrd builds the dictionary for Seq[T] from the dictionary for T.
func SeqOrd[T any](e Ord[T]) Ord[Seq[T]] {
	return Ord[Seq[T]]{
		Eq: func(x, y Seq[T]) bool { return SeqEq(e, x, y) },
		Lt: func(x, y Seq[T]) bool { return SeqCmp(e, x, y) < 0 },
	}
}
