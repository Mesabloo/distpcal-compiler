// Package sched provides the branch scheduler's primitives.
//
// An atomic block compiles to a loop that picks one of its branches at random
// and retries until one fires (thesis §7.2.3.1). The picker is deliberately
// unfair: a branch can be passed over arbitrarily many times, matching the
// compiler's stance that PlusCal's fairness annotations are carried through
// unused. Nothing here tries to be a scheduler in the operating-system sense —
// Go's runtime schedules the goroutines, and this only decides which branch of
// an either a given iteration attempts.
package sched

import "math/rand/v2"

// Rand returns a uniformly distributed integer in [lo, hi).
//
// The two-argument shape is the thesis's: generated code writes Rand(0, n) for
// an n-branch block. It is a thin wrapper over math/rand/v2 rather than a
// generator of its own — the standard library's is already uniform, seeded per
// process, and safe for concurrent use, all three of which this needs.
//
// It panics when hi <= lo, which the compiler never emits: an atomic block has
// at least one branch.
func Rand(lo, hi int) int {
	return lo + rand.IntN(hi-lo)
}
