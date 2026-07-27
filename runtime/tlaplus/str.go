package tlaplus

// Str is the TLA+ STRING type.
//
// It is a newtype over Go's string rather than string itself so that the
// compiler has one name to emit for it, and so that a dictionary can be
// declared for it here rather than for a type this package does not own.
type Str string

// StrToSeq compiles the Str <: Seq(Int) subtyping coercion.
//
// TLA+ leaves STRING's elements unspecified, so the choice of what a character
// is belongs to this implementation: a string is the sequence of its Unicode
// code points, one Int per code point. Len("é") is therefore 1, not the 2 bytes
// its UTF-8 encoding occupies, and indexing can never land inside a character.
// That is deliberately not StrOrd's bytewise ordering — an ordering only has to
// be total and fixed, while this decides what the sequence *is*.
//
// Invalid UTF-8 in the string yields U+FFFD per code point, which is Go's own
// []rune conversion; a Str reaching here holds a source literal, which the lexer
// has already read as text.
//
// The result is built with the unused slot 0 that every Seq carries, so it is
// 1-indexed like any other sequence.
func StrToSeq(s Str) Seq[Int] {
	runes := []rune(string(s))
	out := make(Seq[Int], len(runes)+1)
	for i, r := range runes {
		out[i+1] = MkInt(int(r))
	}
	return out
}

// StrOrd is the dictionary for Str.
//
// The comparison is bytewise, which is Go's own ordering on strings. TLA+ does
// not specify one, so this only has to be total and fixed — sets rely on their
// element ordering for their representation.
var StrOrd = Ord[Str]{
	Eq: func(x, y Str) bool { return x == y },
	Lt: func(x, y Str) bool { return x < y },
}
