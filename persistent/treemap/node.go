package treemap

// node is a single node of a weight-balanced binary search tree.
//
// Nodes are immutable: no function in this package ever assigns through a
// *node pointer. Every operation that looks like a mutation reads the existing
// nodes and allocates new ones, sharing whatever subtrees it did not have to
// rebuild. The only place a node's fields are written is the composite literal
// in mk.
type node[K, V any] struct {
	key         K
	val         V
	left, right *node[K, V]
	weight      int // number of nodes in this subtree, including this one
}

// size reports the number of nodes in the subtree rooted at n, treating the
// empty tree as size zero. Reading it from the node rather than recomputing is
// what makes the weight-balancing conditions in balance.go O(1).
func size[K, V any](n *node[K, V]) int {
	if n == nil {
		return 0
	}
	return n.weight
}

// mk allocates a node with the correct weight for its children. It performs no
// balancing: callers that may have unbalanced l against r go through balance
// instead.
func mk[K, V any](key K, val V, l, r *node[K, V]) *node[K, V] {
	return &node[K, V]{
		key:    key,
		val:    val,
		left:   l,
		right:  r,
		weight: size(l) + size(r) + 1,
	}
}

// lookup finds the value stored under k, if any.
func lookup[K, V any](n *node[K, V], cmp func(a, b K) int, k K) (V, bool) {
	for n != nil {
		switch c := cmp(k, n.key); {
		case c < 0:
			n = n.left
		case c > 0:
			n = n.right
		default:
			return n.val, true
		}
	}
	var zero V
	return zero, false
}

// insert returns a tree containing k, rebuilding only the nodes along the
// search path. An existing binding for k is replaced.
func insert[K, V any](n *node[K, V], cmp func(a, b K) int, k K, v V) *node[K, V] {
	if n == nil {
		return mk(k, v, nil, nil)
	}
	switch c := cmp(k, n.key); {
	case c < 0:
		return balance(n.key, n.val, insert(n.left, cmp, k, v), n.right)
	case c > 0:
		return balance(n.key, n.val, n.left, insert(n.right, cmp, k, v))
	default:
		// Same key: rebuild this one node with the new value, keeping both
		// subtrees. The shape is unchanged, so no rebalancing is needed.
		return mk(k, v, n.left, n.right)
	}
}

// remove returns a tree without k, and reports whether k was present. When it
// was not, the returned tree is nil and callers should keep the original —
// this avoids rebuilding the search path for a delete that changes nothing.
func remove[K, V any](n *node[K, V], cmp func(a, b K) int, k K) (*node[K, V], bool) {
	if n == nil {
		return nil, false
	}
	switch c := cmp(k, n.key); {
	case c < 0:
		l, ok := remove(n.left, cmp, k)
		if !ok {
			return nil, false
		}
		return balance(n.key, n.val, l, n.right), true
	case c > 0:
		r, ok := remove(n.right, cmp, k)
		if !ok {
			return nil, false
		}
		return balance(n.key, n.val, n.left, r), true
	default:
		return glue(n.left, n.right), true
	}
}

// glue combines the two subtrees of a node being deleted. The standard
// technique: promote the smallest key of the right subtree into the vacated
// position, which keeps the ordering invariant without touching l at all.
func glue[K, V any](l, r *node[K, V]) *node[K, V] {
	if l == nil {
		return r
	}
	if r == nil {
		return l
	}
	m, rest := deleteMin(r)
	return balance(m.key, m.val, l, rest)
}

// deleteMin splits off the leftmost node of a non-empty tree, returning it
// alongside the remaining tree. The returned node is only read for its key and
// value; its children belong to rest.
func deleteMin[K, V any](n *node[K, V]) (min, rest *node[K, V]) {
	if n.left == nil {
		return n, n.right
	}
	min, rest = deleteMin(n.left)
	return min, balance(n.key, n.val, rest, n.right)
}
