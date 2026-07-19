// Package treemap provides a persistent (immutable, structurally shared)
// ordered map whose keys need not satisfy Go's comparable constraint.
//
// Ordering comes from a Compare function supplied at construction time rather
// than from the key type itself, which is what lets the compiler's runtime
// library key maps by types carrying their own equality and ordering — Go's
// builtin map[K]V cannot, since comparable is not implementable for a custom
// type.
//
// Every operation is persistent: Insert and Delete return a new map and leave
// the receiver observably unchanged, sharing all subtrees they did not have to
// rebuild. Clone is therefore O(1) — it copies a struct header, not a tree.
// This is what makes TLA+ function overloading (EXCEPT) cheap, since it must
// copy before writing in order not to disturb unrelated sub-expressions.
//
// Because maps are immutable, they are safe to read from several goroutines
// without synchronisation. The package adds none of its own.
package treemap

// TreeMap is an immutable ordered map from K to V.
//
// The zero value is not usable; construct one with New. A nil *TreeMap is not
// a valid empty map either — New with no insertions is.
type TreeMap[K, V any] struct {
	cmp  func(a, b K) int
	root *node[K, V]
}

// New returns an empty map ordered by cmp, which must be a strict weak
// ordering: negative when a sorts before b, zero when the two are equivalent
// (and so denote the same key), positive otherwise.
//
// cmp is captured and reused by every map derived from this one. Maps derived
// from different New calls are unrelated even when their comparisons agree.
func New[K, V any](cmp func(a, b K) int) *TreeMap[K, V] {
	return &TreeMap[K, V]{cmp: cmp}
}

// Get returns the value stored under k and whether it was present.
func (m *TreeMap[K, V]) Get(k K) (V, bool) {
	return lookup(m.root, m.cmp, k)
}

// Insert returns a map binding k to v, replacing any existing binding. The
// receiver is unchanged.
//
// Only the nodes along the search path are rebuilt, so this costs O(log n)
// time and allocates O(log n) nodes; every other subtree is shared with the
// receiver.
func (m *TreeMap[K, V]) Insert(k K, v V) *TreeMap[K, V] {
	return &TreeMap[K, V]{cmp: m.cmp, root: insert(m.root, m.cmp, k, v)}
}

// Delete returns a map without any binding for k. The receiver is unchanged.
//
// When k is absent the receiver is returned as-is: nothing would be rebuilt,
// and the result is immutable, so sharing it is indistinguishable from
// returning a copy.
func (m *TreeMap[K, V]) Delete(k K) *TreeMap[K, V] {
	root, ok := remove(m.root, m.cmp, k)
	if !ok {
		return m
	}
	return &TreeMap[K, V]{cmp: m.cmp, root: root}
}

// Clone returns a map equal to the receiver, in O(1).
//
// Since maps are immutable, the copy shares the receiver's entire tree and
// there is nothing to deep-copy. Clone exists so that calling code can express
// "take a copy before modifying" — the discipline EXCEPT requires — without
// that discipline costing anything.
func (m *TreeMap[K, V]) Clone() *TreeMap[K, V] {
	c := *m
	return &c
}

// Len returns the number of bindings, in O(1).
func (m *TreeMap[K, V]) Len() int {
	return size(m.root)
}
