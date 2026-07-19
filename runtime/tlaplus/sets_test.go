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

	got := SetFilter(s, func(x Int) bool { return x.Lt(MkInt(3)) })

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

	SetFilter(s, func(x Int) bool { return x.Eq(MkInt(2)) })

	if !intsEqual(backing, before) {
		t.Errorf("SetFilter wrote through a shared backing array: %v, was %v", backing, before)
	}
}

// TestSetIn checks membership against the element type's own ordering rather
// than pointer or structural identity. Every position is probed, since a binary
// search can be wrong at the ends without being wrong in the middle.
func TestSetIn(t *testing.T) {
	s := MkSet[Str]("a", "b", "c", "d")
	for _, x := range []Str{"a", "b", "c", "d"} {
		if !SetIn(s, x) {
			t.Errorf("SetIn(s, %q) = false, want true", x)
		}
	}
	for _, x := range []Str{"", "aa", "e", "z"} {
		if SetIn(s, x) {
			t.Errorf("SetIn(s, %q) = true, want false", x)
		}
	}
	if SetIn(Set[Str]{}, "a") {
		t.Errorf("SetIn on the empty set = true, want false")
	}
}

// TestSetInByValue checks membership for an element type whose values are not
// comparable by pointer identity — the arbitrary-precision Int, where a freshly
// constructed 3 is a different allocation from the 3 already in the set.
func TestSetInByValue(t *testing.T) {
	s := intSet(1, 2, 3)
	for _, n := range []int{1, 2, 3} {
		if !SetIn(s, MkInt(n)) {
			t.Errorf("SetIn(s, %d) = false: membership is comparing identity, not value", n)
		}
	}
	if SetIn(s, MkInt(4)) {
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
	if !SetEq(intSet(1, 2, 3), intSet(3, 2, 1)) {
		t.Errorf("{1,2,3} /= {3,2,1}, but those are the same set")
	}
	if !SetEq(intSet(1, 1, 2), intSet(2, 1)) {
		t.Errorf("{1,1,2} /= {2,1}, but those are the same set")
	}
	if SetEq(intSet(1, 2), intSet(1, 2, 3)) {
		t.Errorf("{1,2} = {1,2,3}, want false")
	}
	if SetEq(intSet(1, 2), intSet(1, 3)) {
		t.Errorf("{1,2} = {1,3}, want false")
	}
	if !SetEq(Set[Int]{}, Set[Int]{}) {
		t.Errorf("the empty set is not equal to itself")
	}
}

func TestSetMap(t *testing.T) {
	s := intSet(1, 2, 3)
	got := SetMap(s, func(x Int) Int { return Mul(x, MkInt(2)) })
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
		if x.Lt(MkInt(3)) {
			return MkInt(0)
		}
		return MkInt(1)
	}
	if got, want := SetMap(intSet(1, 2, 3), clamp), ints(0, 1); !intsEqual(got, want) {
		t.Errorf("a non-injective mapping gave %v, want %v", got, want)
	}

	// Order-reversing, so the mapped elements arrive descending.
	negated := SetMap(intSet(1, 2, 3), Neg)
	if want := ints(-3, -2, -1); !intsEqual(negated, want) {
		t.Errorf("{-x : x \\in {1,2,3}} = %v, want %v", negated, want)
	}

	if got := SetMap(intSet(4, 5, 6), func(x Int) Str { return "c" }); len(got) != 1 {
		t.Errorf("a constant mapping gave %v, want a single element", got)
	}
	if got := SetMap(Set[Int]{}, func(x Int) Int { return x }); len(got) != 0 {
		t.Errorf("SetMap over the empty set = %v, want empty", got)
	}
}

// TestChooseIsDeterministic is the property that forced CHOOSE away from a
// random pick: Hilbert's choice must return the same element for the same set
// and predicate, and {1,2} and {2,1} are the same set.
func TestChooseIsDeterministic(t *testing.T) {
	positive := func(x Int) bool { return x.Gt(MkInt(0)) }

	a, b := Choose(intSet(1, 2), positive), Choose(intSet(2, 1), positive)
	if !a.Eq(b) {
		t.Errorf("CHOOSE over {1,2} = %v but over {2,1} = %v; permutations denote the same set", a, b)
	}

	// Repeated evaluation must also agree, which a random pick would not.
	s := intSet(5, 3, 9, 1, 7)
	first := Choose(s, positive)
	for range 10 {
		if got := Choose(s, positive); !got.Eq(first) {
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
	if got := Choose(s, func(x Int) bool { return x.Gt(MkInt(2)) }); !eqInt(got, 3) {
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
	Choose(intSet(1, 2, 3), func(x Int) bool { return x.Gt(MkInt(99)) })
}

// TestOrdDerivations checks Le, Ge and Cmp against the primitive Gt/Lt they are
// derived from, including the reflexive cases the derivations exist to get
// right.
func TestOrdDerivations(t *testing.T) {
	cases := [][2]int{{1, 2}, {2, 1}, {2, 2}}
	for _, c := range cases {
		x, y := MkInt(c[0]), MkInt(c[1])
		if got, want := Le(x, y), c[0] <= c[1]; got != want {
			t.Errorf("Le(%d, %d) = %v, want %v", c[0], c[1], got, want)
		}
		if got, want := Ge(x, y), c[0] >= c[1]; got != want {
			t.Errorf("Ge(%d, %d) = %v, want %v", c[0], c[1], got, want)
		}
		if got, want := Neq(x, y), c[0] != c[1]; got != want {
			t.Errorf("Neq(%d, %d) = %v, want %v", c[0], c[1], got, want)
		}
		want := 0
		switch {
		case c[0] < c[1]:
			want = -1
		case c[0] > c[1]:
			want = 1
		}
		if got := Cmp(x, y); got != want {
			t.Errorf("Cmp(%d, %d) = %d, want %d", c[0], c[1], got, want)
		}
	}

	// FALSE sorts before TRUE.
	if !Bool(false).Lt(true) || !Bool(true).Gt(false) {
		t.Errorf("Bool ordering does not put FALSE before TRUE")
	}
	if Cmp(Bool(false), Bool(true)) != -1 {
		t.Errorf("Cmp(FALSE, TRUE) = %d, want -1", Cmp(Bool(false), Bool(true)))
	}
}
