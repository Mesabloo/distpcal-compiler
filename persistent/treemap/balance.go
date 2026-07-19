package treemap

// Weight-balanced ("bounded balance") trees, following Adams. The choice over
// red-black is deliberate: rotations are ordinary functions from children to a
// freshly allocated parent, with no colour bits to thread through, which is
// exactly what a persistent tree wants.
//
// The invariant maintained is that for every node, the larger subtree is at
// most delta times the size of the smaller one — unless their combined size is
// at most one, where no arrangement can satisfy that. ratio then decides, for a
// subtree that has grown too large, whether a single rotation suffices or
// whether its inner child must be lifted by a double rotation.
const (
	delta = 3
	ratio = 2
)

// balance rebuilds a node from key, val and its two subtrees, rotating when
// one side has outgrown the other. Every caller has just replaced one subtree
// with a version differing in size by at most one, so a single (possibly
// double) rotation always restores the invariant.
func balance[K, V any](key K, val V, l, r *node[K, V]) *node[K, V] {
	ls, rs := size(l), size(r)
	switch {
	case ls+rs <= 1:
		return mk(key, val, l, r)
	case rs > delta*ls:
		return rotateL(key, val, l, r)
	case ls > delta*rs:
		return rotateR(key, val, l, r)
	default:
		return mk(key, val, l, r)
	}
}

// rotateL fixes a right subtree that has grown too large. Lifting r itself
// works when r leans right; when r leans left, doing so would just move the
// imbalance to the other side, so r's own left child is lifted instead.
func rotateL[K, V any](key K, val V, l, r *node[K, V]) *node[K, V] {
	if size(r.left) < ratio*size(r.right) {
		return singleL(key, val, l, r)
	}
	return doubleL(key, val, l, r)
}

// rotateR is the mirror image of rotateL.
func rotateR[K, V any](key K, val V, l, r *node[K, V]) *node[K, V] {
	if size(l.right) < ratio*size(l.left) {
		return singleR(key, val, l, r)
	}
	return doubleR(key, val, l, r)
}

// singleL lifts r into the root position, demoting the old root to r's left.
func singleL[K, V any](key K, val V, l, r *node[K, V]) *node[K, V] {
	return mk(r.key, r.val, mk(key, val, l, r.left), r.right)
}

// singleR lifts l into the root position, demoting the old root to l's right.
func singleR[K, V any](key K, val V, l, r *node[K, V]) *node[K, V] {
	return mk(l.key, l.val, l.left, mk(key, val, l.right, r))
}

// doubleL lifts r's left child two levels, splitting its children between the
// new root's two sides.
func doubleL[K, V any](key K, val V, l, r *node[K, V]) *node[K, V] {
	rl := r.left
	return mk(rl.key, rl.val,
		mk(key, val, l, rl.left),
		mk(r.key, r.val, rl.right, r.right))
}

// doubleR is the mirror image of doubleL.
func doubleR[K, V any](key K, val V, l, r *node[K, V]) *node[K, V] {
	lr := l.right
	return mk(lr.key, lr.val,
		mk(l.key, l.val, l.left, lr.left),
		mk(key, val, lr.right, r))
}
