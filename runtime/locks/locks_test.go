package locks

import (
	"sync"
	"testing"
	"time"
)

// guarded stands in for the struct of process-local variables a lock covers.
type guarded struct {
	counter int
	seen    []int
}

func TestMkLockHoldsInitialValue(t *testing.T) {
	l := MkLock(guarded{counter: 3})

	got := Acquire(l)
	if got.counter != 3 {
		t.Errorf("Acquire returned %d, want the initial 3", got.counter)
	}
	Release(l, got)
}

// TestAcquireReleaseRoundTrip checks that a released value is what the next
// acquirer sees — the mechanism by which a block's writes become visible.
func TestAcquireReleaseRoundTrip(t *testing.T) {
	l := MkLock(guarded{counter: 0})

	v := Acquire(l)
	v.counter = 7
	Release(l, v)

	if got := Acquire(l); got.counter != 7 {
		t.Errorf("second Acquire returned %d, want the released 7", got.counter)
	}
}

// TestAcquireBlocksWhileHeld is the actual mutual-exclusion property at its
// smallest: a second acquisition must not succeed until the first releases.
func TestAcquireBlocksWhileHeld(t *testing.T) {
	l := MkLock(guarded{})
	held := Acquire(l)

	acquired := make(chan struct{})
	go func() {
		Release(l, Acquire(l))
		close(acquired)
	}()

	select {
	case <-acquired:
		t.Fatalf("Acquire succeeded while the lock was held")
	case <-time.After(50 * time.Millisecond):
	}

	Release(l, held)

	select {
	case <-acquired:
	case <-time.After(time.Second):
		t.Errorf("Acquire did not succeed after the lock was released")
	}
}

// TestMutualExclusion is the property lock inference exists to provide:
// concurrent read-modify-write cycles through the lock must not lose updates.
//
// Run this with -race to check the stronger claim, that the guarded value is
// never touched by two goroutines at once.
func TestMutualExclusion(t *testing.T) {
	const goroutines = 50
	const increments = 200

	l := MkLock(guarded{})

	var wg sync.WaitGroup
	for i := range goroutines {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for range increments {
				v := Acquire(l)
				// Read, modify and write back as a compiled atomic block
				// does: project the fields out, work on them, reassemble.
				counter := v.counter
				counter++
				Release(l, guarded{counter: counter, seen: append(v.seen, i)})
			}
		}()
	}
	wg.Wait()

	final := Acquire(l)
	if want := goroutines * increments; final.counter != want {
		t.Errorf("counter = %d, want %d: updates were lost", final.counter, want)
	}
	if len(final.seen) != goroutines*increments {
		t.Errorf("seen has %d entries, want %d", len(final.seen), goroutines*increments)
	}
}

// TestLocksAreOrderedByCaller documents the deadlock that lock inference's
// total order exists to prevent, by showing the safe case works: two locks
// acquired in the same order by both goroutines.
func TestLocksAreOrderedByCaller(t *testing.T) {
	first, second := MkLock(guarded{}), MkLock(guarded{})

	done := make(chan struct{})
	for range 2 {
		go func() {
			for range 100 {
				a := Acquire(first)
				b := Acquire(second)
				a.counter++
				b.counter++
				Release(second, b)
				Release(first, a)
			}
			done <- struct{}{}
		}()
	}

	for range 2 {
		select {
		case <-done:
		case <-time.After(5 * time.Second):
			t.Fatalf("deadlocked acquiring two locks in a consistent order")
		}
	}
}
