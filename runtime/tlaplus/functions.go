package tlaplus

import "github.com/mesabloo/fugue/persistent/treemap"

// LazyFunction represents a TLA+ function t -> u.
//
// The graph is not computed at the definition site — a function's domain may be
// large and most of it never applied — so the structure keeps the domain, a
// generator computing one value on demand, and the cache of what has been
// computed or overridden so far. This mirrors how TLC evaluates functions.
//
// The cache is held by pointer, and that matters: LazyFunction is passed by
// value, so the two things the cache is for want different treatment.
//
//   - FnApply memoizes, and must make its result visible to every copy of the
//     LazyFunction it was applied to. It overwrites the map header through this
//     pointer, which every such copy shares. Persistence lives in the nodes,
//     not the header, so replacing the header is cheap and leaves every map
//     derived from it untouched.
//   - FnOverload implements EXCEPT, and must not let the override escape to the
//     function being overloaded. It simply keeps the fresh header Insert
//     returns, leaving the original pointer aimed at the original map.
//
// Storing the map by value would satisfy the second at the cost of the first:
// FnApply's write would land in its own copy of the struct and be discarded on
// return, silently, making every recursive function exponential.
//
// The keys are ordered by a dictionary rather than by Go's ==, which is exactly
// what the builtin map cannot accept, since comparable is not implementable for
// a custom type. Hence the treemap, which takes its ordering as a parameter —
// the same dictionary-passing shape as this package's own operations, and the
// precedent for them.
type LazyFunction[T, U any] struct {
	dom   Set[T]
	gen   func(x T) U
	cache *treemap.TreeMap[T, U]
}

// FnConstructor compiles the function literal [x \in dom |-> gen(x)].
func FnConstructor[T, U any](o Ord[T], dom Set[T], gen func(x T) U) LazyFunction[T, U] {
	return LazyFunction[T, U]{dom: dom, gen: gen, cache: treemap.New[T, U](o.Cmp)}
}

// FnOverload compiles the function overloading [f EXCEPT ![x] = y].
//
// The result shares f's domain and generator but gets a cache of its own, so
// that f itself still maps x to whatever it did before. That is what makes
// [f EXCEPT ![3] = 7][3] = 7 /\ f[3] # 7 come out true, and it is O(1): the
// underlying map is persistent, so the new cache shares all of f's structure
// and copies only the path to x.
//
// Overloading outside the domain is a no-op, since a TLA+ function's domain
// never changes.
func FnOverload[T, U any](o Ord[T], f LazyFunction[T, U], x T, y U) LazyFunction[T, U] {
	if !SetIn(o, f.dom, x) {
		return f
	}
	return LazyFunction[T, U]{dom: f.dom, gen: f.gen, cache: f.cache.Insert(x, y)}
}

// FnApply compiles function application f[x].
//
// The cache is consulted first, which is what makes an overridden value take
// precedence over what the generator would produce. A computed value is written
// back through the shared pointer, so later applications of this function — or
// of any copy of it — reuse it.
//
// It panics on application outside the domain, that being undefined in TLA+.
func FnApply[T, U any](o Ord[T], f LazyFunction[T, U], x T) U {
	if !SetIn(o, f.dom, x) {
		panic("Application of function outside its domain")
	}
	if y, ok := f.cache.Get(x); ok {
		return y
	}
	y := f.gen(x)
	*f.cache = *f.cache.Insert(x, y)
	return y
}

// MkRecFn constructs a recursively defined function, whose generator is given
// the function itself as its first argument.
//
// This needs a bootstrapping trick: gen has to be able to call back into the
// very LazyFunction being defined, which does not exist yet at the point gen is
// written. So the function is allocated first with no generator, and the
// generator is then installed as a closure over it. Go closures capture the
// variable rather than its value, so by the time that closure can run — on an
// FnApply, never during construction — the variable holds the finished
// function. This ties the knot.
func MkRecFn[T, U any](o Ord[T], dom Set[T], gen func(f LazyFunction[T, U], x T) U) LazyFunction[T, U] {
	f := LazyFunction[T, U]{dom: dom, cache: treemap.New[T, U](o.Cmp)}
	f.gen = func(x T) U { return gen(f, x) }
	return f
}

// Domain compiles DOMAIN f.
func Domain[T, U any](f LazyFunction[T, U]) Set[T] { return f.dom }

// SetAsFun compiles Fugue!SetAsFun(s), reading a set of pairs as the function
// whose graph it is.
//
// The pair type <<a, b>> compiles to an anonymous struct the runtime cannot
// project on its own, so the two projections arrive as callbacks, the way
// SetMap's mapping function does. Apalache leaves the result unspecified when a
// first component repeats with conflicting second components; the compiled form
// panics instead, and -Wunsafe warns at every call site.
func SetAsFun[P, K, V any](ok Ord[K], s Set[P], fst func(P) K, snd func(P) V) LazyFunction[K, V] {
	dom := make(Set[K], 0, len(s))
	for _, p := range s {
		dom = append(dom, fst(p))
	}
	dom = normalize(ok, dom)
	if len(dom) != len(s) {
		panic("SetAsFun of a set of pairs whose first components are not unique")
	}
	return FnConstructor(ok, dom, func(x K) V {
		for _, p := range s {
			if ok.Eq(fst(p), x) {
				return snd(p)
			}
		}
		panic("SetAsFun applied outside its domain")
	})
}

// FnOrd is the dictionary for LazyFunction, and is a placeholder: both
// operations panic.
//
// It exists so that ordDict is total — the compiler can produce a dictionary
// for a function type as it can for any other — and so that a specification
// that actually puts a function inside a set fails loudly at that point rather
// than failing to compile.
//
// A real implementation is known and not written yet. TLC orders functions by
// representing one as an explicit finite graph and comparing domain then range
// pointwise, with a per-value-kind ordinal breaking ties across kinds. Ours is
// lazy, so matching that means forcing the whole domain through gen before
// comparing — which is well defined, and compares the graph rather than the
// cache, two functions with equal graphs having possibly memoized different
// subsets of them. The cost is forcing, on a path nothing yet exercises; the
// question is left for the first specification that needs it.
func FnOrd[T, U any](Ord[T], Ord[U]) Ord[LazyFunction[T, U]] {
	unimplemented := func(LazyFunction[T, U], LazyFunction[T, U]) bool {
		panic("Comparison of functions is not implemented")
	}
	return Ord[LazyFunction[T, U]]{Eq: unimplemented, Lt: unimplemented}
}
