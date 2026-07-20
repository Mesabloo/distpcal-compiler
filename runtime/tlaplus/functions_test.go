package tlaplus

import "testing"

// intsUpTo builds the set {0, ..., n-1}.
func intsUpTo(n int) Set[Int] { return IntRange(MkInt(0), MkInt(n-1)) }

// TestFnApplyMemoizes is the property the cache's pointer exists for: a value
// computed by one application must be reused by later ones, including
// applications of copies of the function, since Go passes LazyFunction by
// value.
func TestFnApplyMemoizes(t *testing.T) {
	var calls int
	f := FnConstructor(IntOrd, intsUpTo(4), func(x Int) Int {
		calls++
		return Mul(x, MkInt(10))
	})

	if got := FnApply(IntOrd, f, MkInt(2)); !eqInt(got, 20) {
		t.Fatalf("FnApply(IntOrd, f, 2) = %v, want 20", got)
	}
	if calls != 1 {
		t.Fatalf("generator ran %d times on the first application, want 1", calls)
	}

	if got := FnApply(IntOrd, f, MkInt(2)); !eqInt(got, 20) {
		t.Fatalf("FnApply(IntOrd, f, 2) = %v on reapplication, want 20", got)
	}
	if calls != 1 {
		t.Errorf("generator ran %d times over two applications: the memoized value was lost", calls)
	}

	// A copy of f shares the cache pointer, so it must see the memoized value
	// too. This is what holding the map by value would silently break.
	g := f
	if got := FnApply(IntOrd, g, MkInt(2)); !eqInt(got, 20) {
		t.Fatalf("FnApply(IntOrd, g, 2) = %v, want 20", got)
	}
	if calls != 1 {
		t.Errorf("generator ran %d times after applying a copy: the cache is not shared", calls)
	}
}

// TestFnOverloadDoesNotLeak is the EXCEPT property from PLAN.md §5.7:
// [f EXCEPT ![3] = 7][3] = 7 /\ f[3] # 7.
func TestFnOverloadDoesNotLeak(t *testing.T) {
	identity := func(x Int) Int { return x }

	f := FnConstructor(IntOrd, intsUpTo(5), identity)
	g := FnOverload(IntOrd, f, MkInt(3), MkInt(7))

	if got := FnApply(IntOrd, g, MkInt(3)); !eqInt(got, 7) {
		t.Errorf("FnApply(IntOrd, g, 3) = %v, want the overridden 7", got)
	}
	if got := FnApply(IntOrd, f, MkInt(3)); !eqInt(got, 3) {
		t.Errorf("FnApply(IntOrd, f, 3) = %v, want the original 3: the override leaked back", got)
	}

	// Applying the original first, so that its cache is populated, must not
	// change the answer either way round.
	f2 := FnConstructor(IntOrd, intsUpTo(5), identity)
	if got := FnApply(IntOrd, f2, MkInt(3)); !eqInt(got, 3) {
		t.Fatalf("FnApply(IntOrd, f2, 3) = %v, want 3", got)
	}
	g2 := FnOverload(IntOrd, f2, MkInt(3), MkInt(7))
	if got := FnApply(IntOrd, g2, MkInt(3)); !eqInt(got, 7) {
		t.Errorf("FnApply(IntOrd, g2, 3) = %v, want 7: the override did not take precedence over the cached value", got)
	}
	if got := FnApply(IntOrd, f2, MkInt(3)); !eqInt(got, 3) {
		t.Errorf("FnApply(IntOrd, f2, 3) = %v, want 3", got)
	}
}

// TestFnOverloadOutsideDomain checks that overloading outside the domain is a
// no-op — a TLA+ function's domain never changes.
func TestFnOverloadOutsideDomain(t *testing.T) {
	f := FnConstructor(IntOrd, intsUpTo(3), func(x Int) Int { return x })
	g := FnOverload(IntOrd, f, MkInt(99), MkInt(7))

	if len(Domain(g)) != 3 {
		t.Errorf("DOMAIN grew to %d after overloading outside it", len(Domain(g)))
	}
	defer func() {
		if recover() == nil {
			t.Errorf("applying outside the domain did not panic")
		}
	}()
	FnApply(IntOrd, g, MkInt(99))
}

// TestFnApplyOutsideDomainPanics checks the undefined case.
func TestFnApplyOutsideDomainPanics(t *testing.T) {
	f := FnConstructor(IntOrd, intsUpTo(3), func(x Int) Int { return x })
	defer func() {
		if recover() == nil {
			t.Errorf("FnApply outside the domain did not panic")
		}
	}()
	FnApply(IntOrd, f, MkInt(42))
}

// TestMkRecFnTiesTheKnot exercises the bootstrapping trick on the thesis's own
// example, Fibonacci. The call count is the point: without a working cache this
// recursion is exponential, so counting generator invocations is what
// distinguishes "ties the knot correctly" from "ties the knot and recomputes
// everything".
func TestMkRecFnTiesTheKnot(t *testing.T) {
	one, two := MkInt(1), MkInt(2)

	var calls int
	fib := MkRecFn(IntOrd, intsUpTo(21), func(f LazyFunction[Int, Int], n Int) Int {
		calls++
		switch {
		case eqInt(n, 0):
			return MkInt(0)
		case eqInt(n, 1):
			return MkInt(1)
		default:
			return Add(FnApply(IntOrd, f, Sub(n, one)), FnApply(IntOrd, f, Sub(n, two)))
		}
	})

	if got := FnApply(IntOrd, fib, MkInt(20)); !eqInt(got, 6765) {
		t.Fatalf("Fib[20] = %v, want 6765", got)
	}
	// One generator call per distinct argument, at most: 0 through 20.
	if calls > 21 {
		t.Errorf("generator ran %d times computing Fib[20]; memoization is not working (linear would be <= 21)", calls)
	}
}

// TestMkRecFnSharesCacheWithItself checks that the knot-tying closure and the
// returned value are backed by the same cache — the returned struct is a copy
// of the variable the closure captured, so this is not automatic.
func TestMkRecFnSharesCacheWithItself(t *testing.T) {
	one := MkInt(1)

	var calls int
	f := MkRecFn(IntOrd, intsUpTo(5), func(g LazyFunction[Int, Int], n Int) Int {
		calls++
		if eqInt(n, 0) {
			return MkInt(0)
		}
		return Add(FnApply(IntOrd, g, Sub(n, one)), one)
	})

	if got := FnApply(IntOrd, f, MkInt(4)); !eqInt(got, 4) {
		t.Fatalf("FnApply(IntOrd, f, 4) = %v, want 4", got)
	}
	before := calls
	if got := FnApply(IntOrd, f, MkInt(4)); !eqInt(got, 4) {
		t.Fatalf("FnApply(IntOrd, f, 4) = %v on reapplication, want 4", got)
	}
	if calls != before {
		t.Errorf("reapplying recomputed %d values: the returned function does not share the recursive cache",
			calls-before)
	}
}

// TestFnOrdPanics pins the placeholder from the design's §4: a dictionary for a
// function type exists, so that ordDict is total and the compiler always has
// something to emit, but using it fails loudly rather than quietly comparing
// caches. Delete this test with the placeholder.
func TestFnOrdPanics(t *testing.T) {
	o := FnOrd(IntOrd, IntOrd)
	f := FnConstructor(IntOrd, intsUpTo(3), func(x Int) Int { return x })

	for name, op := range map[string]func(a, b LazyFunction[Int, Int]) bool{"Eq": o.Eq, "Lt": o.Lt} {
		t.Run(name, func(t *testing.T) {
			defer func() {
				if recover() == nil {
					t.Errorf("%s on the placeholder dictionary did not panic", name)
				}
			}()
			op(f, f)
		})
	}
}

// TestFnKeyedByComposedDictionary checks a function whose domain is itself a
// container: the cache's comparator comes from the dictionary passed in, so a
// domain of sets works with no extra machinery.
func TestFnKeyedByComposedDictionary(t *testing.T) {
	setOrd := SetOrd(IntOrd)
	dom := MkSet(setOrd, intSet(1), intSet(1, 2))
	f := FnConstructor(setOrd, dom, func(s Set[Int]) Int { return Cardinality(s) })

	if got := FnApply(setOrd, f, intSet(2, 1)); !eqInt(got, 2) {
		t.Errorf("f[{2,1}] = %v, want 2: the domain lookup is not using the composed dictionary", got)
	}
	g := FnOverload(setOrd, f, intSet(1), MkInt(99))
	if got := FnApply(setOrd, g, intSet(1)); !eqInt(got, 99) {
		t.Errorf("the override did not take: %v", got)
	}
	if got := FnApply(setOrd, f, intSet(1)); !eqInt(got, 1) {
		t.Errorf("the override leaked back into f: %v", got)
	}
}
