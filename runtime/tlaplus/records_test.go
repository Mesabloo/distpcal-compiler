package tlaplus

import "testing"

// Records and tuples have no types in this package: a record compiles to an
// anonymous Go struct, a tuple to an anonymous struct with Proj1..ProjN fields,
// and the compiler emits a dictionary literal beside each. That works only
// because Ord is a struct — a dictionary can be built for a type that can carry
// no methods.
//
// These tests stand in for generated code, spelling by hand what the emitter
// will spell mechanically. They are here rather than in a records.go's tests
// because there is no records.go and deliberately so, and because what they
// actually pin is a property of Ord: nothing in this package requires the types
// it orders to be nameable.

// message is the shape of LamportMutex's message record, minus the address
// field, which comm.Address cannot supply from inside this package. Field order
// is the sorted order compileTyp produces, which is what fixes the
// lexicographic order below.
type message = struct {
	Mes Str
	Num Int
}

// messageOrd is what ordDict emits for that record: lexicographic in field
// order, built from the components' own dictionaries.
var messageOrd = Ord[message]{
	Eq: func(x, y message) bool {
		return StrOrd.Eq(x.Mes, y.Mes) && IntOrd.Eq(x.Num, y.Num)
	},
	Lt: func(x, y message) bool {
		if c := StrOrd.Cmp(x.Mes, y.Mes); c != 0 {
			return c < 0
		}
		return IntOrd.Lt(x.Num, y.Num)
	},
}

func mes(s Str, n int) message { return message{Mes: s, Num: MkInt(n)} }

// TestAnonymousRecordOrd is §3's core claim: a dictionary for an anonymous
// struct orders it, so a record reaches a set with no named type anywhere.
func TestAnonymousRecordOrd(t *testing.T) {
	s := MkSet(messageOrd, mes("req", 2), mes("ack", 1), mes("req", 2))
	if len(s) != 2 {
		t.Fatalf("the record set has %d elements, want 2", len(s))
	}
	// Sorted on the first field, so "ack" precedes "req".
	if !messageOrd.Eq(s[0], mes("ack", 1)) {
		t.Errorf("the set's minimum is %v, want the \"ack\" record", s[0])
	}
	if !SetIn(messageOrd, s, mes("req", 2)) {
		t.Errorf("a record built separately is not found in the set")
	}
	if SetIn(messageOrd, s, mes("req", 3)) {
		t.Errorf("a record differing in its second field is a member, want false")
	}
	// The second field must break the tie rather than being ignored.
	if !messageOrd.Lt(mes("req", 1), mes("req", 2)) {
		t.Errorf("the second field does not break a tie on the first")
	}
}

// TestAnonymousRecordNesting is the rest of §3's claim: a set of such records,
// and a set of those sets. Composition does not care that the element type is
// unnameable.
func TestAnonymousRecordNesting(t *testing.T) {
	setOrd := SetOrd(messageOrd)

	a := MkSet(messageOrd, mes("req", 1), mes("ack", 2))
	b := MkSet(messageOrd, mes("ack", 2), mes("req", 1))
	outer := MkSet(SetOrd(messageOrd), a, b)
	if len(outer) != 1 {
		t.Errorf("a set of two equal record sets has %d elements, want 1", len(outer))
	}
	if !setOrd.Eq(a, b) {
		t.Errorf("two record sets written in different orders are not equal")
	}

	// A record whose own field is a container, which is where a dictionary
	// that only handled flat records would come apart.
	type inbox = struct {
		Msgs Set[message]
		Name Str
	}
	inboxOrd := Ord[inbox]{
		Eq: func(x, y inbox) bool {
			return setOrd.Eq(x.Msgs, y.Msgs) && StrOrd.Eq(x.Name, y.Name)
		},
		Lt: func(x, y inbox) bool {
			if c := setOrd.Cmp(x.Msgs, y.Msgs); c != 0 {
				return c < 0
			}
			return StrOrd.Lt(x.Name, y.Name)
		},
	}
	if !inboxOrd.Eq(inbox{Msgs: a, Name: "p"}, inbox{Msgs: b, Name: "p"}) {
		t.Errorf("records with equal set-valued fields do not compare equal")
	}
	if !inboxOrd.Lt(inbox{Msgs: a, Name: "p"}, inbox{Msgs: a, Name: "q"}) {
		t.Errorf("the trailing field does not break a tie on a set-valued one")
	}
}

// TestAnonymousTuple covers the arity-5 tuple §3 names, as an anonymous struct
// with Proj1..ProjN fields. There is no arity cap to test against: an anonymous
// struct takes as many fields as the specification wrote.
func TestAnonymousTuple(t *testing.T) {
	type tuple5 = struct {
		Proj1 Int
		Proj2 Int
		Proj3 Int
		Proj4 Int
		Proj5 Str
	}
	o := Ord[tuple5]{
		Eq: func(x, y tuple5) bool {
			return IntOrd.Eq(x.Proj1, y.Proj1) &&
				IntOrd.Eq(x.Proj2, y.Proj2) &&
				IntOrd.Eq(x.Proj3, y.Proj3) &&
				IntOrd.Eq(x.Proj4, y.Proj4) &&
				StrOrd.Eq(x.Proj5, y.Proj5)
		},
		Lt: func(x, y tuple5) bool {
			if c := IntOrd.Cmp(x.Proj1, y.Proj1); c != 0 {
				return c < 0
			}
			if c := IntOrd.Cmp(x.Proj2, y.Proj2); c != 0 {
				return c < 0
			}
			if c := IntOrd.Cmp(x.Proj3, y.Proj3); c != 0 {
				return c < 0
			}
			if c := IntOrd.Cmp(x.Proj4, y.Proj4); c != 0 {
				return c < 0
			}
			return StrOrd.Lt(x.Proj5, y.Proj5)
		},
	}
	base := tuple5{MkInt(1), MkInt(2), MkInt(3), MkInt(4), "e"}

	if !o.Eq(base, tuple5{MkInt(1), MkInt(2), MkInt(3), MkInt(4), "e"}) {
		t.Errorf("equal 5-tuples do not compare equal")
	}
	// A difference in each position in turn, so no component is skipped.
	larger := []tuple5{
		{MkInt(9), MkInt(2), MkInt(3), MkInt(4), "e"},
		{MkInt(1), MkInt(9), MkInt(3), MkInt(4), "e"},
		{MkInt(1), MkInt(2), MkInt(9), MkInt(4), "e"},
		{MkInt(1), MkInt(2), MkInt(3), MkInt(9), "e"},
		{MkInt(1), MkInt(2), MkInt(3), MkInt(4), "z"},
	}
	for i, l := range larger {
		if !o.Lt(base, l) {
			t.Errorf("a difference in component %d did not order the tuples", i+1)
		}
		if o.Eq(base, l) {
			t.Errorf("a difference in component %d compared equal", i+1)
		}
	}
	if got := MkSet(o, base, larger[0], base); len(got) != 2 {
		t.Errorf("a set of tuples has %d elements, want 2", len(got))
	}
}

// TestStructuralIdentity is the property that replaced name mangling: Go
// identifies anonymous struct types structurally, so two records of the same
// shape are already one type and one dictionary serves both. compileTyp sorting
// record fields by name is what makes the shapes coincide, and this is what
// that sorting buys.
func TestStructuralIdentity(t *testing.T) {
	// Written out afresh rather than through the message alias, so that what is
	// compared is the shape and not the name.
	direct := struct {
		Mes Str
		Num Int
	}{Mes: "req", Num: MkInt(1)}

	if !messageOrd.Eq(direct, mes("req", 1)) {
		t.Errorf("an identically-shaped struct is not accepted by the record's dictionary")
	}
	if !SetIn(messageOrd, MkSet(messageOrd, mes("req", 1)), direct) {
		t.Errorf("an identically-shaped struct is not found in a set of the record")
	}
}

// TestTupleWithFunctionComponent is a compilation property rather than a
// behavioural one, and it is the argument that killed declaration-site
// constraints: a tuple holding a function value must be *representable*, even
// though it has no dictionary. Under `type TupleN[A Ord[A], …]` this file would
// not compile. Nothing here asserts much at runtime, and that is the point.
func TestTupleWithFunctionComponent(t *testing.T) {
	f := FnConstructor(IntOrd, MkSet(IntOrd, MkInt(1), MkInt(2)), func(x Int) Int { return x })
	pair := struct {
		Proj1 LazyFunction[Int, Int]
		Proj2 Int
	}{Proj1: f, Proj2: MkInt(1)}

	if got := FnApply(IntOrd, pair.Proj1, MkInt(2)); !IntOrd.Eq(got, MkInt(2)) {
		t.Errorf("the function component came back wrong: %v", got)
	}
}
