package tlaplus

import "testing"

// asInts reads a sequence back through the public accessors, so that tests
// assert on observable contents rather than on the underlying slice and its
// unused slot.
func asInts(s Seq[Int]) []Int {
	out := make([]Int, 0, ToInt(Len(s)))
	for i := 1; i <= ToInt(Len(s)); i++ {
		out = append(out, SeqIndex(s, MkInt(i)))
	}
	return out
}

func TestSeqBasics(t *testing.T) {
	s := intSeq(10, 20, 30)

	if !eqInt(Len(s), 3) {
		t.Errorf("Len = %v, want 3", Len(s))
	}
	if got := Head(s); !eqInt(got, 10) {
		t.Errorf("Head = %v, want 10", got)
	}
	for i, want := range []int{10, 20, 30} {
		if got := SeqIndex(s, MkInt(i+1)); !eqInt(got, want) {
			t.Errorf("s[%d] = %v, want %d", i+1, got, want)
		}
	}
}

// TestSeqEmpty covers the zero value, which has to be a usable empty sequence
// so that a generated `var s Seq[T]` needs no initialization.
func TestSeqEmpty(t *testing.T) {
	var zero Seq[Int]
	if !eqInt(Len(zero), 0) {
		t.Errorf("Len of the zero value = %v, want 0", Len(zero))
	}
	if !eqInt(Len(intSeq()), 0) {
		t.Errorf("Len of MkSeq() = %v, want 0", Len(intSeq()))
	}
	if got := asInts(Append(zero, MkInt(1))); !intsEqual(got, ints(1)) {
		t.Errorf("Append onto the zero value = %v, want [1]", got)
	}
}

// TestSeqOneIndexed pins the indexing convention: index 1 is the first element,
// and neither 0 nor Len+1 is readable.
func TestSeqOneIndexed(t *testing.T) {
	s := intSeq(7, 8)
	for _, i := range []int{-1, 0, 3, 99} {
		func() {
			defer func() {
				if recover() == nil {
					t.Errorf("s[%d] did not panic", i)
				}
			}()
			SeqIndex(s, MkInt(i))
		}()
	}
}

// seqWithSpareCapacity builds <<elems...>> in an array with room left over.
//
// Without this the aliasing tests below prove nothing: MkSeq tends to leave a
// sequence exactly full, so reslicing it in Tail yields len == cap and any
// append reallocates whether or not it was asked to copy. Spare capacity is
// what gives an in-place append somewhere to write, and so what makes the
// hazard observable.
func seqWithSpareCapacity(ns ...int) Seq[Int] {
	var unused Int
	s := make(Seq[Int], 0, len(ns)+8)
	return append(append(s, unused), ints(ns...)...)
}

func TestSeqUpdate(t *testing.T) {
	s := intSeq(10, 20, 30)
	got := SeqUpdate(s, MkInt(2), MkInt(99))

	if want := ints(10, 99, 30); !intsEqual(asInts(got), want) {
		t.Errorf("[s EXCEPT ![2] = 99] = %v, want %v", asInts(got), want)
	}
	if want := ints(10, 20, 30); !intsEqual(asInts(s), want) {
		t.Errorf("SeqUpdate mutated its input: %v, want %v", asInts(s), want)
	}

	// Both ends, since an off-by-one in the bounds check would only show there.
	if got := asInts(SeqUpdate(s, MkInt(1), MkInt(0))); !eqInt(got[0], 0) {
		t.Errorf("updating index 1 gave %v", got)
	}
	if got := asInts(SeqUpdate(s, MkInt(3), MkInt(0))); !eqInt(got[2], 0) {
		t.Errorf("updating index Len gave %v", got)
	}
}

// TestSeqUpdateOutOfBounds checks that the unused slot is not reachable by
// writing to it, the mirror of TestSeqOneIndexed's read case.
func TestSeqUpdateOutOfBounds(t *testing.T) {
	s := intSeq(7, 8)
	for _, i := range []int{-1, 0, 3, 99} {
		func() {
			defer func() {
				if recover() == nil {
					t.Errorf("SeqUpdate at index %d did not panic", i)
				}
			}()
			SeqUpdate(s, MkInt(i), MkInt(0))
		}()
	}
}

// TestSeqUpdateDoesNotAliasTail is SeqUpdate's version of the property Append
// has: a sequence produced by Tail shares its array with the original, so
// writing through one must not be visible in the other.
func TestSeqUpdateDoesNotAliasTail(t *testing.T) {
	s := seqWithSpareCapacity(1, 2, 3)
	tail := Tail(s)

	updated := SeqUpdate(tail, MkInt(1), MkInt(99))

	if got := asInts(s); !intsEqual(got, ints(1, 2, 3)) {
		t.Errorf("SeqUpdate on a tail wrote through to the original: %v", got)
	}
	if got := asInts(tail); !intsEqual(got, ints(2, 3)) {
		t.Errorf("SeqUpdate mutated the sequence it updated: %v", got)
	}
	if got := asInts(updated); !intsEqual(got, ints(99, 3)) {
		t.Errorf("SeqUpdate = %v, want [99 3]", got)
	}
}

// TestTailSharesWithoutAliasing is the property Tail's reslicing depends on:
// dropping the head is a view onto the same array, so Append must not write
// into it.
func TestTailSharesWithoutAliasing(t *testing.T) {
	s := seqWithSpareCapacity(1, 2, 3)
	tail := Tail(s)
	if cap(tail) <= len(tail) {
		t.Fatalf("test is vacuous: tail has no spare capacity (len %d, cap %d)", len(tail), cap(tail))
	}

	if got := asInts(tail); !intsEqual(got, ints(2, 3)) {
		t.Fatalf("Tail = %v, want [2 3]", got)
	}

	// tail has spare capacity in s's array; appending must not overwrite it.
	appended := Append(tail, MkInt(99))
	if got := asInts(tail); !intsEqual(got, ints(2, 3)) {
		t.Errorf("Append mutated the sequence it appended to: %v", got)
	}
	if got := asInts(s); !intsEqual(got, ints(1, 2, 3)) {
		t.Errorf("Append wrote through a shared backing array: s = %v", got)
	}
	if got := asInts(appended); !intsEqual(got, ints(2, 3, 99)) {
		t.Errorf("Append = %v, want [2 3 99]", got)
	}

	// Two appends onto the same sequence must not see each other.
	a, b := Append(tail, MkInt(1)), Append(tail, MkInt(2))
	if !eqInt(asInts(a)[2], 1) || !eqInt(asInts(b)[2], 2) {
		t.Errorf("two appends onto one sequence interfered: %v and %v", asInts(a), asInts(b))
	}
}

// TestTailRepeatedly walks a sequence down to empty, checking the index shift
// holds at every step rather than only the first.
func TestTailRepeatedly(t *testing.T) {
	s := intSeq(1, 2, 3, 4)
	for want := 1; want <= 4; want++ {
		if got := Head(s); !eqInt(got, want) {
			t.Fatalf("Head = %v, want %d", got, want)
		}
		if got := Len(s); !eqInt(got, 5-want) {
			t.Fatalf("Len = %v, want %d", got, 5-want)
		}
		s = Tail(s)
	}
	if !eqInt(Len(s), 0) {
		t.Errorf("Len after exhausting the sequence = %v, want 0", Len(s))
	}
}

func TestHeadTailEmptyPanics(t *testing.T) {
	for name, f := range map[string]func(){
		"Head": func() { Head(Seq[Int]{}) },
		"Tail": func() { Tail(Seq[Int]{}) },
	} {
		t.Run(name, func(t *testing.T) {
			defer func() {
				if recover() == nil {
					t.Errorf("%s of the empty sequence did not panic", name)
				}
			}()
			f()
		})
	}
}

func TestSeqEq(t *testing.T) {
	if !SeqEq(intSeq(1, 2), intSeq(1, 2)) {
		t.Errorf("<<1,2>> /= <<1,2>>")
	}
	// Order matters, unlike sets.
	if SeqEq(intSeq(1, 2), intSeq(2, 1)) {
		t.Errorf("<<1,2>> = <<2,1>>, want false")
	}
	if SeqEq(intSeq(1, 2), intSeq(1, 2, 3)) {
		t.Errorf("<<1,2>> = <<1,2,3>>, want false")
	}
	if !SeqEq(Seq[Int]{}, intSeq()) {
		t.Errorf("the two spellings of the empty sequence are not equal")
	}
	// Equality must ignore the unused slot.
	if !SeqEq(Seq[Int](ints(99, 1, 2)), intSeq(1, 2)) {
		t.Errorf("equality observed the unused slot")
	}
}

func TestSeqCmp(t *testing.T) {
	cases := []struct {
		a, b Seq[Int]
		want int
	}{
		{intSeq(1, 2), intSeq(1, 2), 0},
		{intSeq(1, 2), intSeq(1, 3), -1},
		{intSeq(1, 3), intSeq(1, 2), 1},
		{intSeq(1), intSeq(1, 2), -1},
		{intSeq(1, 2), intSeq(1), 1},
		{Seq[Int]{}, intSeq(1), -1},
		{Seq[Int]{}, Seq[Int]{}, 0},
	}
	for _, c := range cases {
		got := SeqCmp(c.a, c.b)
		if (got < 0) != (c.want < 0) || (got > 0) != (c.want > 0) {
			t.Errorf("SeqCmp(%v, %v) = %d, want sign of %d", asInts(c.a), asInts(c.b), got, c.want)
		}
	}
}
