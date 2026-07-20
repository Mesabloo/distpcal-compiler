package tlaplus

import (
	"slices"
	"testing"
)

// TestSetFilterDoesNotMutate is the immutability property from §7.2.1.2: TLA+
// data is immutable, so {x \in S : P} must leave S alone. It is worth an
// explicit test because slices.DeleteFunc compacts in place, so getting this
// wrong corrupts the input rather than merely returning the wrong answer.
func TestSetFilterDoesNotMutate(t *testing.T) {
	s := intSet(1, 2, 3, 4, 5)
	before := slices.Clone(s)

	got := SetFilter(s, func(x Int) bool { return IntOrd.Lt(x, MkInt(3)) })

	if !intsEqual(s, before) {
		t.Errorf("SetFilter mutated its input: %v, was %v", s, before)
	}
	if want := ints(1, 2); !intsEqual(got, want) {
		t.Errorf("SetFilter = %v, want %v", got, want)
	}
}

// TestSetFilterDoesNotMutateSharedBacking checks the sharper version of the
// same property: a set that shares a backing array with a larger slice must not
// have its neighbours clobbered either.
func TestSetFilterDoesNotMutateSharedBacking(t *testing.T) {
	backing := intSet(1, 2, 3, 4, 5, 6)
	s := backing[:3]
	before := slices.Clone(backing)

	SetFilter(s, func(x Int) bool { return IntOrd.Eq(x, MkInt(2)) })

	if !intsEqual(backing, before) {
		t.Errorf("SetFilter wrote through a shared backing array: %v, was %v", backing, before)
	}
}

// TestSetIn checks membership against the element type's own ordering rather
// than pointer or structural identity. Every position is probed, since a binary
// search can be wrong at the ends without being wrong in the middle.
func TestSetIn(t *testing.T) {
	s := MkSet(StrOrd, "a", "b", "c", "d")
	for _, x := range []Str{"a", "b", "c", "d"} {
		if !SetIn(StrOrd, s, x) {
			t.Errorf("SetIn(s, %q) = false, want true", x)
		}
	}
	for _, x := range []Str{"", "aa", "e", "z"} {
		if SetIn(StrOrd, s, x) {
			t.Errorf("SetIn(s, %q) = true, want false", x)
		}
	}
	if SetIn(StrOrd, Set[Str]{}, "a") {
		t.Errorf("SetIn on the empty set = true, want false")
	}
}

// TestSetInByValue checks membership for an element type whose values are not
// comparable by pointer identity — the arbitrary-precision Int, where a freshly
// constructed 3 is a different allocation from the 3 already in the set.
func TestSetInByValue(t *testing.T) {
	s := intSet(1, 2, 3)
	for _, n := range []int{1, 2, 3} {
		if !SetIn(IntOrd, s, MkInt(n)) {
			t.Errorf("SetIn(s, %d) = false: membership is comparing identity, not value", n)
		}
	}
	if SetIn(IntOrd, s, MkInt(4)) {
		t.Errorf("SetIn(s, 4) = true, want false")
	}
}

// TestMkSet checks that a literal built from arbitrary input comes out sorted
// and duplicate-free — the two invariants everything else relies on.
func TestMkSet(t *testing.T) {
	if got, want := intSet(3, 1, 2, 3, 1), ints(1, 2, 3); !intsEqual(got, want) {
		t.Errorf("MkSet(3,1,2,3,1) = %v, want %v", got, want)
	}
	if got := intSet(); len(got) != 0 {
		t.Errorf("MkSet() = %v, want empty", got)
	}
	if got, want := intSet(7, 7, 7), ints(7); !intsEqual(got, want) {
		t.Errorf("MkSet(7,7,7) = %v, want {7}", got)
	}
}

// TestSetEq checks that equality is contents-based, and in particular that it
// holds between sets written in different orders — which is exactly what the
// sorted representation buys.
func TestSetEq(t *testing.T) {
	if !SetEq(IntOrd, intSet(1, 2, 3), intSet(3, 2, 1)) {
		t.Errorf("{1,2,3} /= {3,2,1}, but those are the same set")
	}
	if !SetEq(IntOrd, intSet(1, 1, 2), intSet(2, 1)) {
		t.Errorf("{1,1,2} /= {2,1}, but those are the same set")
	}
	if SetEq(IntOrd, intSet(1, 2), intSet(1, 2, 3)) {
		t.Errorf("{1,2} = {1,2,3}, want false")
	}
	if SetEq(IntOrd, intSet(1, 2), intSet(1, 3)) {
		t.Errorf("{1,2} = {1,3}, want false")
	}
	if !SetEq(IntOrd, Set[Int]{}, Set[Int]{}) {
		t.Errorf("the empty set is not equal to itself")
	}
}

func TestSetMap(t *testing.T) {
	s := intSet(1, 2, 3)
	got := SetMap(IntOrd, s, func(x Int) Int { return Mul(x, MkInt(2)) })
	if want := ints(2, 4, 6); !intsEqual(got, want) {
		t.Errorf("SetMap = %v, want %v", got, want)
	}
	if want := ints(1, 2, 3); !intsEqual(s, want) {
		t.Errorf("SetMap mutated its input: %v", s)
	}
}

// TestSetMapRenormalizes covers both invariants, neither of which survives a
// mapping: a non-injective function must not leave the same element twice, and
// a non-monotone one must not leave the result out of order.
func TestSetMapRenormalizes(t *testing.T) {
	// Collapses 1 and 2 onto the same value: not injective.
	clamp := func(x Int) Int {
		if IntOrd.Lt(x, MkInt(3)) {
			return MkInt(0)
		}
		return MkInt(1)
	}
	if got, want := SetMap(IntOrd, intSet(1, 2, 3), clamp), ints(0, 1); !intsEqual(got, want) {
		t.Errorf("a non-injective mapping gave %v, want %v", got, want)
	}

	// Order-reversing, so the mapped elements arrive descending.
	negated := SetMap(IntOrd, intSet(1, 2, 3), Neg)
	if want := ints(-3, -2, -1); !intsEqual(negated, want) {
		t.Errorf("{-x : x \\in {1,2,3}} = %v, want %v", negated, want)
	}

	if got := SetMap(StrOrd, intSet(4, 5, 6), func(x Int) Str { return "c" }); len(got) != 1 {
		t.Errorf("a constant mapping gave %v, want a single element", got)
	}
	if got := SetMap(IntOrd, Set[Int]{}, func(x Int) Int { return x }); len(got) != 0 {
		t.Errorf("SetMap over the empty set = %v, want empty", got)
	}
}

// TestChooseIsDeterministic is the property that forced CHOOSE away from a
// random pick: Hilbert's choice must return the same element for the same set
// and predicate, and {1,2} and {2,1} are the same set.
func TestChooseIsDeterministic(t *testing.T) {
	positive := func(x Int) bool { return IntOrd.Gt(x, MkInt(0)) }

	a, b := Choose(intSet(1, 2), positive), Choose(intSet(2, 1), positive)
	if !IntOrd.Eq(a, b) {
		t.Errorf("CHOOSE over {1,2} = %v but over {2,1} = %v; permutations denote the same set", a, b)
	}

	// Repeated evaluation must also agree, which a random pick would not.
	s := intSet(5, 3, 9, 1, 7)
	first := Choose(s, positive)
	for range 10 {
		if got := Choose(s, positive); !IntOrd.Eq(got, first) {
			t.Fatalf("CHOOSE returned %v then %v over the same set", first, got)
		}
	}
	if !eqInt(first, 1) {
		t.Errorf("CHOOSE = %v, want the minimum 1", first)
	}
}

// TestChooseRespectsPredicate checks that the choice is made among satisfying
// elements only, not simply the set minimum.
func TestChooseRespectsPredicate(t *testing.T) {
	s := intSet(5, 1, 4, 2, 3)
	if got := Choose(s, func(x Int) bool { return IntOrd.Gt(x, MkInt(2)) }); !eqInt(got, 3) {
		t.Errorf("CHOOSE x \\in s : x > 2 = %v, want the smallest satisfying element 3", got)
	}
}

// TestChooseEmptyPanics checks the undefined case.
func TestChooseEmptyPanics(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Errorf("CHOOSE with no satisfying element did not panic")
		}
	}()
	Choose(intSet(1, 2, 3), func(x Int) bool { return IntOrd.Gt(x, MkInt(99)) })
}

// TestOrdDerivations checks Neq, Gt, Le, Ge and Cmp against the primitive
// Eq/Lt they are derived from, including the reflexive cases the derivations
// exist to get right.
func TestOrdDerivations(t *testing.T) {
	cases := [][2]int{{1, 2}, {2, 1}, {2, 2}}
	for _, c := range cases {
		x, y := MkInt(c[0]), MkInt(c[1])
		if got, want := IntOrd.Gt(x, y), c[0] > c[1]; got != want {
			t.Errorf("Gt(%d, %d) = %v, want %v", c[0], c[1], got, want)
		}
		if got, want := IntOrd.Le(x, y), c[0] <= c[1]; got != want {
			t.Errorf("Le(%d, %d) = %v, want %v", c[0], c[1], got, want)
		}
		if got, want := IntOrd.Ge(x, y), c[0] >= c[1]; got != want {
			t.Errorf("Ge(%d, %d) = %v, want %v", c[0], c[1], got, want)
		}
		if got, want := IntOrd.Neq(x, y), c[0] != c[1]; got != want {
			t.Errorf("Neq(%d, %d) = %v, want %v", c[0], c[1], got, want)
		}
		want := 0
		switch {
		case c[0] < c[1]:
			want = -1
		case c[0] > c[1]:
			want = 1
		}
		if got := IntOrd.Cmp(x, y); got != want {
			t.Errorf("Cmp(%d, %d) = %d, want %d", c[0], c[1], got, want)
		}
	}

	// FALSE sorts before TRUE.
	if !BoolOrd.Lt(false, true) || !BoolOrd.Gt(true, false) {
		t.Errorf("Bool ordering does not put FALSE before TRUE")
	}
	if got := BoolOrd.Cmp(false, true); got != -1 {
		t.Errorf("Cmp(FALSE, TRUE) = %d, want -1", got)
	}
}

// TestCmpPanicsOnPartialOrder checks the total-order obligation a dictionary
// carries: a comparison that answers no to all three questions is not one, and
// Cmp says so rather than silently reporting equal.
func TestCmpPanicsOnPartialOrder(t *testing.T) {
	never := Ord[Int]{
		Eq: func(x, y Int) bool { return false },
		Lt: func(x, y Int) bool { return false },
	}
	defer func() {
		if recover() == nil {
			t.Errorf("Cmp under a non-total dictionary did not panic")
		}
	}()
	never.Cmp(MkInt(1), MkInt(2))
}

// TestSetUnion, TestSetIntersect and TestSetDifference check the answers and,
// just as importantly, that the merge produces a representation the rest of the
// package may rely on: sorted and duplicate-free without a renormalization pass.
func TestSetUnion(t *testing.T) {
	cases := []struct {
		name     string
		s, other Set[Int]
		want     []Int
	}{
		{"disjoint", intSet(1, 3, 5), intSet(2, 4), ints(1, 2, 3, 4, 5)},
		{"overlapping", intSet(1, 2, 3), intSet(2, 3, 4), ints(1, 2, 3, 4)},
		{"identical", intSet(1, 2), intSet(1, 2), ints(1, 2)},
		{"left empty", intSet(), intSet(1, 2), ints(1, 2)},
		{"right empty", intSet(1, 2), intSet(), ints(1, 2)},
		{"both empty", intSet(), intSet(), ints()},
		{"left exhausted first", intSet(1), intSet(2, 3, 4), ints(1, 2, 3, 4)},
		{"right exhausted first", intSet(1, 2, 3), intSet(0), ints(0, 1, 2, 3)},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			if got := SetUnion(IntOrd, c.s, c.other); !intsEqual(got, c.want) {
				t.Errorf("SetUnion(%v, %v) = %v, want %v", c.s, c.other, got, c.want)
			}
		})
	}
}

func TestSetIntersect(t *testing.T) {
	cases := []struct {
		name     string
		s, other Set[Int]
		want     []Int
	}{
		{"disjoint", intSet(1, 3, 5), intSet(2, 4), ints()},
		{"overlapping", intSet(1, 2, 3), intSet(2, 3, 4), ints(2, 3)},
		{"identical", intSet(1, 2), intSet(1, 2), ints(1, 2)},
		{"left empty", intSet(), intSet(1, 2), ints()},
		{"right empty", intSet(1, 2), intSet(), ints()},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			if got := SetIntersect(IntOrd, c.s, c.other); !intsEqual(got, c.want) {
				t.Errorf("SetIntersect(%v, %v) = %v, want %v", c.s, c.other, got, c.want)
			}
		})
	}
}

func TestSetDifference(t *testing.T) {
	cases := []struct {
		name     string
		s, other Set[Int]
		want     []Int
	}{
		{"disjoint", intSet(1, 3, 5), intSet(2, 4), ints(1, 3, 5)},
		{"overlapping", intSet(1, 2, 3), intSet(2, 3, 4), ints(1)},
		{"identical", intSet(1, 2), intSet(1, 2), ints()},
		{"left empty", intSet(), intSet(1, 2), ints()},
		{"right empty", intSet(1, 2), intSet(), ints(1, 2)},
		{"tail survives", intSet(1, 2, 3, 4), intSet(1), ints(2, 3, 4)},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			if got := SetDifference(IntOrd, c.s, c.other); !intsEqual(got, c.want) {
				t.Errorf("SetDifference(%v, %v) = %v, want %v", c.s, c.other, got, c.want)
			}
		})
	}
}

// TestSetOpsDoNotMutate covers all three at once. They append into a freshly
// allocated slice, but the cheap implementation of union — append other's tail
// onto s and return it — would alias, so the property is worth pinning.
func TestSetOpsDoNotMutate(t *testing.T) {
	ops := map[string]func(o Ord[Int], s, other Set[Int]) Set[Int]{
		"SetUnion":      SetUnion[Int],
		"SetIntersect":  SetIntersect[Int],
		"SetDifference": SetDifference[Int],
	}
	for name, op := range ops {
		t.Run(name, func(t *testing.T) {
			s, other := intSet(1, 2, 3), intSet(2, 3, 4)
			sBefore, otherBefore := slices.Clone(s), slices.Clone(other)

			got := op(IntOrd, s, other)
			// Writing through the result must not reach either operand.
			for i := range got {
				got[i] = MkInt(-1)
			}

			if !intsEqual(s, sBefore) {
				t.Errorf("%s mutated its left operand: %v, was %v", name, s, sBefore)
			}
			if !intsEqual(other, otherBefore) {
				t.Errorf("%s mutated its right operand: %v, was %v", name, other, otherBefore)
			}
		})
	}
}

// TestSetSubseteq pins the reflexive and empty-set edges alongside the ordinary
// cases: the walk advances two cursors, so an element of s past everything in
// other is exactly where an off-by-one shows up.
func TestSetSubseteq(t *testing.T) {
	cases := []struct {
		name     string
		s, other Set[Int]
		want     bool
	}{
		{"proper subset", intSet(1, 3), intSet(1, 2, 3), true},
		{"equal", intSet(1, 2), intSet(1, 2), true},
		{"empty is subset of anything", intSet(), intSet(1), true},
		{"empty subset of empty", intSet(), intSet(), true},
		{"nothing is a subset of empty", intSet(1), intSet(), false},
		{"missing element", intSet(1, 4), intSet(1, 2, 3), false},
		{"element below the range", intSet(0), intSet(1, 2), false},
		{"element above the range", intSet(3), intSet(1, 2), false},
		{"superset", intSet(1, 2, 3), intSet(1, 2), false},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			if got := SetSubseteq(IntOrd, c.s, c.other); got != c.want {
				t.Errorf("SetSubseteq(%v, %v) = %v, want %v", c.s, c.other, got, c.want)
			}
		})
	}
}

// TestSetOrdNests is the construction the dictionary design exists for, and the
// one the interface design could not express at all: MkSet[T Ord[T]] rejected
// Set[Int] as an element type, so Set[Set[Int]] was not constructible.
//
// It also pins that the composed dictionary is the right one — the outer set
// must deduplicate {3,1} against {1,3}, which needs the *inner* dictionary's
// notion of equality, not Go's.
func TestSetOrdNests(t *testing.T) {
	setOrd := SetOrd(IntOrd)

	s := MkSet(setOrd, intSet(3, 1), intSet(2), intSet(1, 3))
	if len(s) != 2 {
		t.Fatalf("{{3,1}, {2}, {1,3}} has %d elements, want 2: {3,1} and {1,3} are the same set", len(s))
	}
	if !SetIn(setOrd, s, intSet(1, 3)) {
		t.Errorf("{1,3} \\notin {{1,3}, {2}}")
	}
	if SetIn(setOrd, s, intSet(1, 2)) {
		t.Errorf("{1,2} \\in {{1,3}, {2}}, want false")
	}

	// And once more round, since nothing about the composition is special-cased
	// at depth one.
	deep := MkSet(SetOrd(setOrd), s, MkSet(setOrd, intSet(2), intSet(1, 3)))
	if len(deep) != 1 {
		t.Errorf("a set of two equal sets-of-sets has %d elements, want 1", len(deep))
	}
}

// TestSetOrdOrdering checks the lexicographic order SetOrd imposes. The
// direction is arbitrary — TLA+ does not order sets — so what is pinned is
// that it is a total order consistent with SetEq, which is what CHOOSE and the
// sorted representation need of it.
func TestSetOrdOrdering(t *testing.T) {
	setOrd := SetOrd(IntOrd)
	cases := []struct {
		name string
		a, b Set[Int]
		want int
	}{
		{"equal", intSet(1, 2), intSet(2, 1), 0},
		{"differing element", intSet(1, 2), intSet(1, 3), -1},
		{"prefix is smaller", intSet(1), intSet(1, 2), -1},
		{"empty is smallest", intSet(), intSet(1), -1},
		{"both empty", intSet(), intSet(), 0},
		{"first element decides", intSet(0, 9), intSet(1), -1},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			if got := setOrd.Cmp(c.a, c.b); (got < 0) != (c.want < 0) || (got > 0) != (c.want > 0) {
				t.Errorf("Cmp(%v, %v) = %d, want sign of %d", c.a, c.b, got, c.want)
			}
			// Antisymmetry, which Cmp's own panic would otherwise catch only
			// in one direction.
			if got := setOrd.Cmp(c.b, c.a); (got > 0) != (c.want < 0) || (got < 0) != (c.want > 0) {
				t.Errorf("Cmp(%v, %v) = %d, want sign of %d", c.b, c.a, got, -c.want)
			}
		})
	}
}

// TestCardinality relies on the duplicate-free invariant: the count is the slice
// length only because MkSet already removed the repeats.
func TestCardinality(t *testing.T) {
	if got := Cardinality(MkSet(IntOrd, ints(3, 1, 2, 1, 3)...)); !eqInt(got, 3) {
		t.Errorf("Cardinality({3, 1, 2, 1, 3}) = %v, want 3", got)
	}
	if got := Cardinality(intSet()); !eqInt(got, 0) {
		t.Errorf("Cardinality({}) = %v, want 0", got)
	}
}
