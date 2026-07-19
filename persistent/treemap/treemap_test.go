package treemap

import (
	"math/rand"
	"strings"
	"testing"
)

func cmpInt(a, b int) int { return a - b }

// newInts builds a map from a literal set of bindings, in the given order.
func newInts(bindings ...[2]int) *TreeMap[int, int] {
	m := New[int, int](cmpInt)
	for _, b := range bindings {
		m = m.Insert(b[0], b[1])
	}
	return m
}

// checkInvariants walks the whole tree, verifying the ordering invariant, that
// every cached weight matches the actual subtree size, and that the
// weight-balance condition of balance.go holds at every node. Returns the
// subtree size so that callers can compare against Len.
func checkInvariants[V any](t *testing.T, n *node[int, V], lo, hi int) int {
	t.Helper()
	if n == nil {
		return 0
	}
	if n.key <= lo || n.key >= hi {
		t.Fatalf("key %d out of order: expected strictly within (%d, %d)", n.key, lo, hi)
	}
	ls := checkInvariants(t, n.left, lo, n.key)
	rs := checkInvariants(t, n.right, n.key, hi)
	if n.weight != ls+rs+1 {
		t.Fatalf("node %d: weight %d, actual subtree size %d", n.key, n.weight, ls+rs+1)
	}
	if ls+rs > 1 && (rs > delta*ls || ls > delta*rs) {
		t.Fatalf("node %d unbalanced: left %d, right %d (delta %d)", n.key, ls, rs, delta)
	}
	return ls + rs + 1
}

// TestAgainstOracle drives random insert/delete sequences against a builtin map
// and checks that Get and Len agree at every step, along with the tree's own
// structural invariants.
func TestAgainstOracle(t *testing.T) {
	const (
		steps   = 4000
		keySpan = 200
	)
	rng := rand.New(rand.NewSource(1))

	m := New[int, int](cmpInt)
	oracle := map[int]int{}

	for i := range steps {
		k := rng.Intn(keySpan)
		if rng.Intn(3) == 0 {
			m = m.Delete(k)
			delete(oracle, k)
		} else {
			m = m.Insert(k, i)
			oracle[k] = i
		}

		if got := m.Len(); got != len(oracle) {
			t.Fatalf("step %d: Len = %d, oracle has %d bindings", i, got, len(oracle))
		}
		want, wantOK := oracle[k]
		if got, ok := m.Get(k); ok != wantOK {
			t.Fatalf("step %d: Get(%d) presence = %v, oracle = %v", i, k, ok, wantOK)
		} else if ok && got != want {
			t.Fatalf("step %d: Get(%d) = %d, oracle = %d", i, k, got, want)
		}
	}

	if got := checkInvariants(t, m.root, -1, keySpan); got != len(oracle) {
		t.Fatalf("walked %d nodes, oracle has %d bindings", got, len(oracle))
	}
	for k, v := range oracle {
		got, ok := m.Get(k)
		if !ok || got != v {
			t.Fatalf("Get(%d) = (%d, %v), want (%d, true)", k, got, ok, v)
		}
	}
}

// TestInsertLeavesOriginalUnchanged is the property that matters most: a map
// derived by Insert must be observably independent of the one it came from,
// both for a fresh key and for one that already had a binding.
func TestInsertLeavesOriginalUnchanged(t *testing.T) {
	m1 := newInts([2]int{1, 10}, [2]int{2, 20}, [2]int{3, 30})

	m2 := m1.Insert(4, 40)
	if _, ok := m1.Get(4); ok {
		t.Errorf("inserting 4 into the derived map made it visible in the original")
	}
	if v, ok := m2.Get(4); !ok || v != 40 {
		t.Errorf("m2.Get(4) = (%d, %v), want (40, true)", v, ok)
	}
	if m1.Len() != 3 || m2.Len() != 4 {
		t.Errorf("Len: original %d, derived %d; want 3 and 4", m1.Len(), m2.Len())
	}

	m3 := m1.Insert(2, 999)
	if v, _ := m1.Get(2); v != 20 {
		t.Errorf("overwriting 2 in the derived map changed the original to %d", v)
	}
	if v, _ := m3.Get(2); v != 999 {
		t.Errorf("m3.Get(2) = %d, want 999", v)
	}
}

// TestDeleteLeavesOriginalUnchanged is the same property for Delete.
func TestDeleteLeavesOriginalUnchanged(t *testing.T) {
	m1 := newInts([2]int{1, 10}, [2]int{2, 20}, [2]int{3, 30})

	m2 := m1.Delete(2)
	if v, ok := m1.Get(2); !ok || v != 20 {
		t.Errorf("deleting 2 from the derived map removed it from the original")
	}
	if _, ok := m2.Get(2); ok {
		t.Errorf("m2 still contains 2 after Delete")
	}
	if m1.Len() != 3 || m2.Len() != 2 {
		t.Errorf("Len: original %d, derived %d; want 3 and 2", m1.Len(), m2.Len())
	}
}

// TestCloneIsIndependent checks Clone's contract at the API level. It shares
// the whole tree, which is unobservable precisely because derived maps never
// write through it.
func TestCloneIsIndependent(t *testing.T) {
	m1 := newInts([2]int{1, 10}, [2]int{2, 20})
	c := m1.Clone()

	if c.Len() != m1.Len() {
		t.Fatalf("Clone().Len() = %d, want %d", c.Len(), m1.Len())
	}
	c2 := c.Insert(3, 30)
	if _, ok := m1.Get(3); ok {
		t.Errorf("insertion into a map derived from the clone reached the original")
	}
	if _, ok := c.Get(3); ok {
		t.Errorf("insertion into a map derived from the clone reached the clone")
	}
	if _, ok := c2.Get(3); !ok {
		t.Errorf("c2 is missing the key just inserted into it")
	}
}

// TestStructuralSharing checks the claim that Insert copies the search path and
// nothing else, by finding a subtree of the original that the inserted key
// cannot have touched and asserting it is pointer-identical in the derived
// tree.
func TestStructuralSharing(t *testing.T) {
	m1 := New[int, int](cmpInt)
	for i := range 64 {
		m1 = m1.Insert(i, i)
	}

	// Insert a key larger than everything present: it descends right at the
	// root, so the root's entire left subtree must be shared verbatim.
	m2 := m1.Insert(1000, 1000)
	if m2.root.key != m1.root.key {
		t.Skipf("insertion rotated the root (%d to %d); sharing check needs a stable root",
			m1.root.key, m2.root.key)
	}
	if m1.root.left != m2.root.left {
		t.Errorf("root's left subtree was rebuilt despite the inserted key belonging to the right")
	}
	if m1.root == m2.root {
		t.Errorf("root was shared, but it is on the search path and must have been rebuilt")
	}
}

// TestIterateIsOrdered checks the in-order traversal and its early exit.
func TestIterateIsOrdered(t *testing.T) {
	m := New[int, int](cmpInt)
	for _, k := range []int{5, 1, 9, 3, 7, 2, 8, 4, 6} {
		m = m.Insert(k, k*10)
	}

	var keys []int
	m.Iterate(func(k, v int) bool {
		if v != k*10 {
			t.Errorf("Iterate gave (%d, %d), want value %d", k, v, k*10)
		}
		keys = append(keys, k)
		return true
	})
	for i := range keys {
		if keys[i] != i+1 {
			t.Fatalf("Iterate visited %v, want ascending 1..9", keys)
		}
	}

	var seen int
	m.Iterate(func(k, v int) bool {
		seen++
		return seen < 3
	})
	if seen != 3 {
		t.Errorf("Iterate visited %d bindings after the callback stopped at 3", seen)
	}
}

// version is a deliberately non-comparable key type: Go's == is not defined for
// a struct containing a slice, so a map[version]T would not compile. Ordering
// it needs nothing but the comparator supplied to New.
type version struct {
	name     string
	segments []int
}

func cmpVersion(a, b version) int {
	if c := strings.Compare(a.name, b.name); c != 0 {
		return c
	}
	for i := 0; i < len(a.segments) && i < len(b.segments); i++ {
		if d := a.segments[i] - b.segments[i]; d != 0 {
			return d
		}
	}
	return len(a.segments) - len(b.segments)
}

// TestNonComparableKeys is the reason this package exists rather than a
// map[K]V: it exercises the whole API with a key type Go refuses to compare.
func TestNonComparableKeys(t *testing.T) {
	m := New[version, string](cmpVersion)
	keys := []version{
		{name: "go", segments: []int{1, 25}},
		{name: "go", segments: []int{1, 4}},
		{name: "go", segments: []int{1}},
		{name: "lean", segments: []int{4, 0, 0}},
		{name: "lean", segments: []int{4}},
	}
	for i, k := range keys {
		m = m.Insert(k, string(rune('a'+i)))
	}
	if m.Len() != len(keys) {
		t.Fatalf("Len = %d, want %d", m.Len(), len(keys))
	}
	for i, k := range keys {
		// A structurally equal but distinct key value must find the binding,
		// since lookup goes through cmp and never through pointer identity.
		probe := version{name: k.name, segments: append([]int(nil), k.segments...)}
		if v, ok := m.Get(probe); !ok || v != string(rune('a'+i)) {
			t.Errorf("Get(%v) = (%q, %v), want (%q, true)", probe, v, ok, string(rune('a'+i)))
		}
	}

	m2 := m.Delete(version{name: "go", segments: []int{1}})
	if _, ok := m2.Get(version{name: "go", segments: []int{1}}); ok {
		t.Errorf("key survived Delete")
	}
	if _, ok := m.Get(version{name: "go", segments: []int{1}}); !ok {
		t.Errorf("Delete on the derived map removed the key from the original")
	}
}

// TestFuzzAgainstOracle randomises the operation sequence itself, checking the
// full contents against the oracle at the end rather than step by step.
func TestFuzzAgainstOracle(t *testing.T) {
	for seed := int64(0); seed < 20; seed++ {
		rng := rand.New(rand.NewSource(seed))
		m := New[int, int](cmpInt)
		oracle := map[int]int{}

		for i := range 500 {
			k := rng.Intn(50)
			switch rng.Intn(4) {
			case 0:
				m = m.Delete(k)
				delete(oracle, k)
			default:
				m = m.Insert(k, i)
				oracle[k] = i
			}
		}

		checkInvariants(t, m.root, -1, 50)
		if m.Len() != len(oracle) {
			t.Fatalf("seed %d: Len = %d, oracle has %d", seed, m.Len(), len(oracle))
		}
		m.Iterate(func(k, v int) bool {
			if want, ok := oracle[k]; !ok || want != v {
				t.Fatalf("seed %d: map has (%d, %d), oracle has (%d, %v)", seed, k, v, want, ok)
			}
			return true
		})
	}
}
