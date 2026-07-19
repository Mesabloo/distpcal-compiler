package treemap

// Iterate visits every binding in ascending key order, stopping early if f
// returns false.
//
// The traversal reads a tree that cannot change underneath it, so it is safe
// for f to derive new maps from m; those derived maps are simply not visited.
func (m *TreeMap[K, V]) Iterate(f func(k K, v V) bool) {
	iterate(m.root, f)
}

// iterate performs the in-order walk, reporting whether it ran to completion
// so that an early stop deep in the recursion unwinds the whole traversal
// instead of only the current subtree.
func iterate[K, V any](n *node[K, V], f func(k K, v V) bool) bool {
	if n == nil {
		return true
	}
	if !iterate(n.left, f) {
		return false
	}
	if !f(n.key, n.val) {
		return false
	}
	return iterate(n.right, f)
}
