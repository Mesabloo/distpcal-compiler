package tlaplus

import "testing"

// --- FunAsSeq -------------------------------------------------------------

// TestFunAsSeqMaterializesGraph checks the happy path: a function over 1..n
// becomes the sequence of its values, in order.
func TestFunAsSeqMaterializesGraph(t *testing.T) {
	f := FnConstructor(IntOrd, IntRange(MkInt(1), MkInt(3)), func(x Int) Int { return Mul(x, x) })

	got := FunAsSeq(f)
	if !SeqEq(IntOrd, got, intSeq(1, 4, 9)) {
		t.Fatalf("FunAsSeq(f) = %v, want <<1, 4, 9>>", got)
	}
	// The result is a real sequence: 1-indexed, Len/Head/index all agree.
	if !eqInt(Len(got), 3) {
		t.Errorf("Len(FunAsSeq(f)) = %v, want 3", Len(got))
	}
	if !eqInt(Head(got), 1) {
		t.Errorf("Head(FunAsSeq(f)) = %v, want 1", Head(got))
	}
	if !eqInt(SeqIndex(got, MkInt(2)), 4) {
		t.Errorf("FunAsSeq(f)[2] = %v, want 4", SeqIndex(got, MkInt(2)))
	}
}

// TestFunAsSeqEmpty checks that the empty function is the empty sequence.
func TestFunAsSeqEmpty(t *testing.T) {
	f := FnConstructor(IntOrd, IntRange(MkInt(1), MkInt(0)), func(x Int) Int { return x })

	if got := FunAsSeq(f); length(got) != 0 {
		t.Errorf("FunAsSeq of the empty function = %v, want <<>>", got)
	}
}

// TestFunAsSeqSingleton checks the n = 1 boundary.
func TestFunAsSeqSingleton(t *testing.T) {
	f := FnConstructor(IntOrd, IntRange(MkInt(1), MkInt(1)), func(x Int) Int { return MkInt(42) })

	if got := FunAsSeq(f); !SeqEq(IntOrd, got, intSeq(42)) {
		t.Errorf("FunAsSeq of {1 |-> 42} = %v, want <<42>>", got)
	}
}

// TestFunAsSeqAdversarialDomains checks every way a domain can fail to be 1..n.
func TestFunAsSeqAdversarialDomains(t *testing.T) {
	cases := []struct {
		name string
		dom  Set[Int]
	}{
		{"starts at 0", intSet(0, 1, 2)},
		{"starts at 2", intSet(2, 3, 4)},
		{"gap in the middle", rawIntSet(1, 2, 4)},
		{"negative element", intSet(-1, 1, 2, 3)},
		{"1..n plus an extra", rawIntSet(1, 2, 3, 5)},
		{"single element, not 1", intSet(7)},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			f := FnConstructor(IntOrd, c.dom, func(x Int) Int { return x })
			defer func() {
				if recover() == nil {
					t.Errorf("FunAsSeq of a %s domain did not panic", c.name)
				}
			}()
			FunAsSeq(f)
		})
	}
}

// TestFunAsSeqRoundTrip checks that reading a sequence out as a function and
// back yields the same sequence -- the two representations really are the same.
func TestFunAsSeqRoundTrip(t *testing.T) {
	orig := intSeq(5, 6, 7, 8)
	asFun := FnConstructor(IntOrd, IntRange(MkInt(1), MkInt(4)), func(x Int) Int {
		return SeqIndex(orig, x)
	})

	if got := FunAsSeq(asFun); !SeqEq(IntOrd, got, orig) {
		t.Errorf("FunAsSeq round trip = %v, want %v", got, orig)
	}
}

// --- SetAsFun ------------------------------------------------------------

// pair stands in for the anonymous struct <<a, b>> compiles to. The runtime
// never names that type -- it is handed the two projections -- so a test-local
// struct with its own field names exercises SetAsFun exactly as generated code
// would.
type pair struct{ fst, snd Int }

func pairOrd() Ord[pair] {
	return Ord[pair]{
		Eq: func(x, y pair) bool { return IntOrd.Eq(x.fst, y.fst) && IntOrd.Eq(x.snd, y.snd) },
		Lt: func(x, y pair) bool {
			if !IntOrd.Eq(x.fst, y.fst) {
				return IntOrd.Lt(x.fst, y.fst)
			}
			return IntOrd.Lt(x.snd, y.snd)
		},
	}
}

func fst(p pair) Int { return p.fst }
func snd(p pair) Int { return p.snd }

func mkPairs(kv ...int) Set[pair] {
	ps := make([]pair, 0, len(kv)/2)
	for i := 0; i+1 < len(kv); i += 2 {
		ps = append(ps, pair{MkInt(kv[i]), MkInt(kv[i+1])})
	}
	return MkSet(pairOrd(), ps...)
}

// TestSetAsFunReadsGraph checks the happy path.
func TestSetAsFunReadsGraph(t *testing.T) {
	f := SetAsFun(IntOrd, mkPairs(1, 10, 2, 20, 3, 30), fst, snd)

	if !SetEq(IntOrd, Domain(f), intSet(1, 2, 3)) {
		t.Fatalf("DOMAIN SetAsFun(s) = %v, want {1, 2, 3}", Domain(f))
	}
	for _, kv := range [][2]int{{1, 10}, {2, 20}, {3, 30}} {
		if got := FnApply(IntOrd, f, MkInt(kv[0])); !eqInt(got, kv[1]) {
			t.Errorf("SetAsFun(s)[%d] = %v, want %d", kv[0], got, kv[1])
		}
	}
	// Applying twice hits the memo path in FnApply.
	if got := FnApply(IntOrd, f, MkInt(2)); !eqInt(got, 20) {
		t.Errorf("SetAsFun(s)[2] on reapplication = %v, want 20", got)
	}
}

// TestSetAsFunEmpty checks the empty set becomes the empty function.
func TestSetAsFunEmpty(t *testing.T) {
	f := SetAsFun(IntOrd, MkSet(pairOrd()), fst, snd)

	if len(Domain(f)) != 0 {
		t.Errorf("DOMAIN SetAsFun({}) = %v, want {}", Domain(f))
	}
}

// TestSetAsFunOutsideDomainPanics: the result is a genuine function, so applying
// it off its domain is undefined.
func TestSetAsFunOutsideDomainPanics(t *testing.T) {
	f := SetAsFun(IntOrd, mkPairs(1, 10), fst, snd)
	defer func() {
		if recover() == nil {
			t.Errorf("applying SetAsFun's result outside its domain did not panic")
		}
	}()
	FnApply(IntOrd, f, MkInt(9))
}

// TestSetAsFunNonFunctionalPanics checks the undefined case in every arrangement
// of the clashing pairs: adjacent, and separated by an unrelated key.
func TestSetAsFunNonFunctionalPanics(t *testing.T) {
	cases := []struct {
		name  string
		pairs Set[pair]
	}{
		{"adjacent clash", mkPairs(1, 10, 1, 20)},
		{"clash separated by another key", mkPairs(1, 10, 2, 99, 1, 20)},
		{"three values for one key", mkPairs(5, 1, 5, 2, 5, 3)},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			defer func() {
				if recover() == nil {
					t.Errorf("SetAsFun of a non-functional pair set (%s) did not panic", c.name)
				}
			}()
			SetAsFun(IntOrd, c.pairs, fst, snd)
		})
	}
}

// TestSetAsFunSameValueRepeatedKeyStillPanics: even when both pairs would map the
// key to the same value, a functional reading is not guaranteed by the pair set
// alone -- MkSet keeps <<1,10>> and <<1,10>>... actually dedups those. This
// checks the boundary: distinct pairs, equal second component.
func TestSetAsFunEqualValuesDistinctPairsPanics(t *testing.T) {
	// <<1, 10>> and <<1, 10>> are the same pair and collapse; use a value that
	// differs so the pairs stay distinct but the first component still repeats.
	f := func() (caught bool) {
		defer func() { caught = recover() != nil }()
		SetAsFun(IntOrd, mkPairs(1, 10, 1, 11), fst, snd)
		return false
	}
	if !f() {
		t.Errorf("SetAsFun of {<<1,10>>, <<1,11>>} did not panic")
	}
}
