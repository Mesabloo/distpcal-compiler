package tlaplus

// The Naturals module's operators.
//
// The arithmetic (Add, Sub, Neg, Mul) lives with the Int representation it
// depends on, in int_big.go and int_machine.go. It is exposed as functions
// rather than left to Go's own operators so that the two representations
// present the same surface and generated code is written once, whichever is
// selected.
//
// The comparisons (<, >, =<, >=) are deliberately absent: Int implements Ord,
// so they compile to Lt/Gt and the generic Le/Ge, representation-independent
// for the same reason.
//
// Nat is also absent. It denotes an infinite set, which Set cannot represent —
// see OPEN_QUESTIONS.md §9.15 for the general handling of infinite sets
// reaching a backend.

// IntRange compiles the range operator lo..hi, the set of integers from lo to
// hi inclusive.
//
// The result is empty when hi < lo, matching TLA+. It is built in ascending
// order and cannot repeat, so it satisfies Set's invariants by construction and
// needs no normalization.
//
// The loop counts with Int rather than a machine integer, so this holds for
// either representation without conversion.
func IntRange(lo, hi Int) Set[Int] {
	var out Set[Int]
	one := MkInt(1)
	for i := lo; Le(i, hi); i = Add(i, one) {
		out = append(out, i)
	}
	return out
}
