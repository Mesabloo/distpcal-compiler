package tlaplus

import "testing"

// StrToSeq is what the Str <: Seq(Int) coercion compiles to, so what it produces
// has to be an ordinary sequence in every respect the rest of this package
// assumes: 1-indexed, Len counting elements rather than slots, Head/Tail/SeqIndex
// reaching the same elements. These tests pin that alongside the code-point
// decision itself.

func TestStrToSeqIsAnOrdinarySequence(t *testing.T) {
	s := StrToSeq("abc")

	if got := ToInt(Len(s)); got != 3 {
		t.Fatalf("Len is %d, want 3", got)
	}
	// 'a' is U+0061. Reached through SeqIndex, so the unused slot 0 is what the
	// indexing skips.
	for i, want := range []int{'a', 'b', 'c'} {
		if got := ToInt(SeqIndex(s, MkInt(i+1))); got != want {
			t.Errorf("element %d is %d, want %d", i+1, got, want)
		}
	}
	if got := ToInt(Head(s)); got != 'a' {
		t.Errorf("Head is %d, want %d", got, 'a')
	}
	if got := ToInt(Len(Tail(s))); got != 2 {
		t.Errorf("Len(Tail) is %d, want 2", got)
	}
	if got := ToInt(Head(Tail(s))); got != 'b' {
		t.Errorf("Head(Tail) is %d, want %d", got, 'b')
	}
}

func TestStrToSeqEmpty(t *testing.T) {
	if got := ToInt(Len(StrToSeq(""))); got != 0 {
		t.Errorf("Len(StrToSeq(\"\")) is %d, want 0", got)
	}
}

// The code-point decision, which is the half of it a byte-oriented conversion
// would get wrong: "é" is one element holding U+00E9, not the two bytes 0xC3
// 0xA9 its UTF-8 encoding occupies.
func TestStrToSeqIsCodePoints(t *testing.T) {
	s := StrToSeq("é")

	if got := ToInt(Len(s)); got != 1 {
		t.Fatalf("Len(StrToSeq(\"é\")) is %d, want 1", got)
	}
	if got := ToInt(SeqIndex(s, MkInt(1))); got != 0xE9 {
		t.Errorf("the element is %d, want %d", got, 0xE9)
	}
	// A code point outside the BMP, which a UTF-16 conversion would split in two.
	if got := ToInt(Len(StrToSeq("🐘"))); got != 1 {
		t.Errorf("Len(StrToSeq(\"🐘\")) is %d, want 1", got)
	}
}

// The coercion's result is compared and ordered like any other sequence — a set
// of strings-as-sequences works, which needs SeqOrd(IntOrd) to accept it.
func TestStrToSeqOrders(t *testing.T) {
	o := SeqOrd(IntOrd)

	if !o.Eq(StrToSeq("ab"), StrToSeq("ab")) {
		t.Errorf("equal strings do not convert to equal sequences")
	}
	if !o.Lt(StrToSeq("ab"), StrToSeq("b")) {
		t.Errorf("\"ab\" does not precede \"b\" under the sequence ordering")
	}
	if got := MkSet(o, StrToSeq("a"), StrToSeq("b"), StrToSeq("a")); len(got) != 2 {
		t.Errorf("a set of converted strings has %d elements, want 2", len(got))
	}
}
