package tlaplus

import "testing"

// Tests for the parts of Int that both representations must agree on. The
// representation-specific ones live in int_big_test.go, which is build-tagged.

// TestRandInRange checks the half-open interval, the boundary that decides
// whether Rand(0, n) can index an n-branch block or an n-element set.
//
// Enough draws that missing either endpoint's treatment is unlikely: the upper
// bound must never come out, and over this many draws every value below it
// should, so the loop also catches a generator stuck on one element.
func TestRandInRange(t *testing.T) {
	lo, hi := -3, 4
	seen := map[int]bool{}
	for range 1000 {
		got := ToInt(Rand(MkInt(lo), MkInt(hi)))
		if got < lo || got >= hi {
			t.Fatalf("Rand(%d, %d) = %d, outside [%d, %d)", lo, hi, got, lo, hi)
		}
		seen[got] = true
	}
	for n := lo; n < hi; n++ {
		if !seen[n] {
			t.Errorf("Rand(%d, %d) never returned %d in 1000 draws", lo, hi, n)
		}
	}
}

// TestRandSingleton is the degenerate range the compiler does emit: a
// one-branch atomic block.
func TestRandSingleton(t *testing.T) {
	if got := Rand(MkInt(7), MkInt(8)); !eqInt(got, 7) {
		t.Errorf("Rand(7, 8) = %v, want 7", got)
	}
}

// TestRandEmptyRangePanics covers both the empty and the inverted range, which
// have the same answer: there is no element to return.
func TestRandEmptyRangePanics(t *testing.T) {
	cases := []struct {
		name   string
		lo, hi int
	}{
		{"empty", 5, 5},
		{"inverted", 5, 2},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			defer func() {
				if recover() == nil {
					t.Errorf("Rand(%d, %d) did not panic", c.lo, c.hi)
				}
			}()
			Rand(MkInt(c.lo), MkInt(c.hi))
		})
	}
}
