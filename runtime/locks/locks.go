// Package locks provides the mutual exclusion that keeps a compiled process's
// atomic blocks atomic.
//
// A process runs its threads as concurrent goroutines, so two atomic blocks in
// different threads can touch the same process-local variable at once. The
// compiler's lock inference decides which variables must be guarded together
// and in what order they are acquired; this package provides the lock those
// decisions are expressed with. Locks never leave the process that created
// them.
package locks

// Lock guards a group of process-local variables, carrying their values rather
// than sitting beside them.
//
// The representation is a channel of capacity one, holding exactly the value
// being guarded: taking the value out is acquisition, putting it back is
// release, and a second acquirer blocks on an empty channel until then. Holding
// the value inside the lock rather than next to it is what makes "read a
// variable without holding its lock" unrepresentable rather than merely
// discouraged.
//
// Generated code never performs channel operations on a Lock directly, going
// through MkLock, Acquire and Release instead, so that the representation stays
// swappable (thesis Listing 7.2.11).
//
// Which variables share a lock is decided by the compiler's lock inference,
// which also fixes a total order on locks so that a block acquiring several
// cannot deadlock against one acquiring the same locks in another order. That
// ordering is the caller's responsibility: nothing here enforces it.
type Lock[T any] chan T

// MkLock creates a lock already holding init, so that the guarded value is
// available to the first acquirer.
//
// The initial value comes from the initial values of the variables the lock
// covers, as written in the process.
func MkLock[T any](init T) Lock[T] {
	l := make(Lock[T], 1)
	l <- init
	return l
}

// Acquire takes the guarded value, blocking until it is available.
//
// Locks are not reentrant: acquiring one twice from the same goroutine blocks
// forever. Lock inference is what guarantees generated code does not, by
// merging locks so that a block names each of its locks once.
func Acquire[T any](l Lock[T]) T { return <-l }

// Release returns v as the new guarded value, making it visible to the next
// acquirer.
//
// Callers pass back a value reassembled from the local variables the block was
// working with, which is how writes become visible — releasing the value
// unchanged is what "read but did not modify" looks like.
//
// Releasing a lock that was never acquired blocks forever, rather than
// corrupting the guarded value: the channel is already full.
func Release[T any](l Lock[T], v T) { l <- v }
